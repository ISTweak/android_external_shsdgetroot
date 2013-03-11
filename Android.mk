LOCAL_PATH:= $(call my-dir)

include $(CLEAR_VARS)
LOCAL_SRC_FILES:= shsdgetroot.c
LOCAL_MODULE := shsdgetroot
LOCAL_CFLAGS += -std=c99
LOCAL_FORCE_STATIC_EXECUTABLE := true
LOCAL_STATIC_LIBRARIES := libm libstdc++ libc libcutils
LOCAL_MODULE_TAGS := optional
LOCAL_MODULE_PATH := $(PRODUCT_OUT)/istweak

include $(BUILD_EXECUTABLE)

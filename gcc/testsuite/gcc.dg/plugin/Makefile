HOST_GCC=g++-dev
TARGET_GCC=gcc-dev
CPYTHON_SOURCE_FILES= analyzer_cpython_plugin.c
KERNEL_SOURCE_FILES= analyzer_kernel_plugin.c
GCC_DIR = /home/flappy/gcc_/gcc/gcc
GCCPLUGINS_DIR:= $(shell $(TARGET_GCC) -print-file-name=plugin)
CXXFLAGS+= -I$(GCC_DIR) -I$(GCCPLUGINS_DIR)/include -fPIC -fno-rtti -O2

cpython_plugin.so: $(CPYTHON_SOURCE_FILES)
	$(HOST_GCC) -shared $(CXXFLAGS) $^ -o $@

kernel_plugin.so: $(KERNEL_SOURCE_FILES)
	$(HOST_GCC) -shared $(CXXFLAGS) $^ -o $@

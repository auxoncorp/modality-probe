TARGET := c-example

SRCS := src/main.c

INCLS = -Iinclude -I../../modality-probe-capi/include

OBJS := $(SRCS:.c=.o)
DEPS := $(SRCS:.c=.dep)

CC := gcc
CCFLAGS = -ansi \
	-D_DEFAULT_SOURCE \
	-UNDEBUG \
	-Wall -Wextra -Werror -Wsign-conversion \
	-Wformat=2 -Wno-unused-parameter -Wshadow \
	-Wwrite-strings -Wstrict-prototypes -Wold-style-definition \
	-Wnested-externs -Wmissing-include-dirs
LDFLAGS =
LIBS = ../../modality-probe-capi/target/debug/libmodality_probe.a

.PHONY: all clean probe-utils gen-manifest gen-header run test

all: probe-utils gen-manifest gen-header $(TARGET)

# Build the C API, cli, and UDP collector
probe-utils:
	@cd ../../modality-probe-capi && cargo build
	@cd ../../ && cargo build -p modality-probe-cli
	@cd ../../ && cargo build -p modality-probe-udp-collector

gen-manifest:
	@../../target/debug/modality-probe \
		manifest-gen \
		--lang C \
		--file-extension="c" \
		--component-name "example-component" \
		--output-path "example-component" \
		.

gen-header:
	@mkdir -p include
	@../../target/debug/modality-probe \
		header-gen \
		--lang C \
		--output-path "include/component_definitions.h" \
		example-component

run: all
	@./$(TARGET)

test: all
	@./integration_test.sh

$(TARGET): $(OBJS)
	$(CC) $(LDFLAGS) $(INCLS) -o $@ $^ $(LIBS)

$(OBJS): %.o: %.c %.dep
	$(CC) $(CCFLAGS) $(INCLS) -o $@ -c $<

$(DEPS): %.dep: %.c Makefile
	$(CC) $(CCFLAGS) $(INCLS) -MM $< > $@

clean:
	-rm -f src/*.o
	-rm -f src/*.dep
	-rm -f $(TARGET)
	-rm -rf artifacts

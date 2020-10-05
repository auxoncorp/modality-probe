ifeq ($(OS),Windows_NT)
	TEST_STATIC := test-static.exe
	TEST_DYN := test-dyn.exe
	TEST_NOOP := test-noop.exe
else
	TEST_STATIC := test-static
	TEST_DYN := test-dyn
	TEST_NOOP := test-noop
endif

TEST_STATIC_SRC := test.c
TEST_DYN_SRC := test.c
TEST_NOOP_SRC := noop.c

INCLS = -I../include

CC := gcc
CCFLAGS = -ansi -Wall -Wextra -Werror -Wconversion -Wsign-conversion -UNDEBUG

ifeq ($(OS),Windows_NT)
	# There appears to be missing dlls on windows
	# when running the statically linked test, just dynamically linked for now
	DYN_LIBS = -L../target/debug -lmodality_probe
	STATIC_LIBS = -L../target/debug -lmodality_probe
else
	DYN_LIBS = -L../target/debug -lmodality_probe
	STATIC_LIBS = ../target/debug/libmodality_probe.a
endif

.PHONY: all clean capi test

all: capi $(TEST_STATIC) $(TEST_DYN) $(TEST_NOOP)

capi:
	@cd ../ && cargo clean && cargo build

test: all
ifeq ($(OS),Windows_NT)
	./$(TEST_DYN)
else
	cd ../target/debug && ldconfig -Nn .
	LD_LIBRARY_PATH=../target/debug ./$(TEST_DYN)
endif
	./$(TEST_STATIC)
	./$(TEST_NOOP)

$(TEST_STATIC): capi
	$(CC) $(CCFLAGS) $(INCLS) -o $@ $(TEST_STATIC_SRC) $(STATIC_LIBS)

$(TEST_DYN): capi
	$(CC) $(CCFLAGS) $(INCLS) -o $@ $(TEST_DYN_SRC) $(DYN_LIBS)

# This test is intentionally not linked to libmodality_probe
$(TEST_NOOP): capi
	$(CC) $(CCFLAGS) $(INCLS) -o $@ $(TEST_NOOP_SRC)

clean:
	-rm -f $(TEST_STATIC) $(TEST_DYN) $(TEST_NOOP)

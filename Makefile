LAKE ?= lake
CC = clang
CFLAGS = -std=c11 -O3 -Wall -Wextra -Werror

.PHONY: all proof code test

all: proof code build/test_sqrt32 build/instruction_oracle build/routine_oracle build/fp_environment

build:
	mkdir -p build

proof:
	$(LAKE) build VerifiedSqrt checkInstructions checkCore32 checkMachine32
	$(LAKE) env lean --trust=0 Audit.lean

code:
	python3 scripts/extract_code.py --check

build/test_sqrt32: tests/sqrt32.c asm/sqrt32.S | build
	$(CC) $(CFLAGS) $^ -o $@

build/instruction_oracle: tests/instruction_oracle.c | build
	$(CC) $(CFLAGS) $< -o $@

build/routine_oracle: tests/routine_oracle.c asm/sqrt32.S | build
	$(CC) $(CFLAGS) $^ -o $@

build/fp_environment: tests/fp_environment.c | build
	$(CC) $(CFLAGS) $< -o $@

test: all
	./build/fp_environment
	./build/instruction_oracle build/instructions.bin 1000000
	.lake/build/bin/checkInstructions build/instructions.bin
	.lake/build/bin/checkCore32
	./build/routine_oracle build/routine.bin 1100000
	.lake/build/bin/checkMachine32 build/routine.bin
	./build/test_sqrt32 0 4294967296 0
	./build/test_sqrt32 0 4294967296 1

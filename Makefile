LAKE ?= lake
CC = clang
CFLAGS = -std=c11 -O3 -Wall -Wextra -Werror

.PHONY: all proof code test test64

all: proof code build/test_sqrt32 build/instruction_oracle build/integer_oracle build/scalar_state build/routine_oracle build/fp_environment build/correction32 build/test_sqrt64 build/instruction_oracle64

build:
	mkdir -p build

proof:
	$(LAKE) build VerifiedSqrt checkInstructions checkInteger checkScalarState checkCore32 checkMachine32 checkInstructions64
	$(LAKE) env lean --trust=0 Audit.lean

code:
	python3 scripts/extract_code.py --check
	python3 scripts/extract_code.py --precision 64 --check

build/test_sqrt32: tests/sqrt32.c asm/sqrt32.S | build
	$(CC) $(CFLAGS) $^ -o $@

build/test_sqrt64: tests/sqrt64.c asm/sqrt64.S | build
	$(CC) $(CFLAGS) $^ -o $@

build/instruction_oracle: tests/instruction_oracle.c | build
	$(CC) $(CFLAGS) $< -o $@

build/instruction_oracle64: tests/instruction_oracle64.c | build
	$(CC) $(CFLAGS) $< -o $@

build/routine_oracle: tests/routine_oracle.c asm/sqrt32.S | build
	$(CC) $(CFLAGS) $^ -o $@

build/fp_environment: tests/fp_environment.c | build
	$(CC) $(CFLAGS) $< -o $@

build/integer_oracle: tests/integer_oracle.c | build
	$(CC) $(CFLAGS) $< -o $@

build/scalar_state: tests/scalar_state.c | build
	$(CC) $(CFLAGS) $< -o $@

build/correction32: tests/correction32.c tests/correction_entry.S asm/sqrt32.S | build
	$(CC) $(CFLAGS) -DSQRT32_TESTING $^ -o $@

test: all
	./build/fp_environment
	./build/instruction_oracle build/instructions.bin 1000000
	.lake/build/bin/checkInstructions build/instructions.bin
	./build/integer_oracle build/integers.bin 1000000
	.lake/build/bin/checkInteger build/integers.bin
	./build/scalar_state build/scalar-state.bin 200000
	.lake/build/bin/checkScalarState build/scalar-state.bin
	./build/correction32
	.lake/build/bin/checkCore32
	./build/routine_oracle build/routine.bin 1100000
	.lake/build/bin/checkMachine32 build/routine.bin
	./build/test_sqrt32 0 4294967296 0
	./build/test_sqrt32 0 4294967296 1

test64: all
	./build/instruction_oracle64 build/instructions64.bin 1000000
	.lake/build/bin/checkInstructions64 build/instructions64.bin
	./build/test_sqrt64 1000000000 0
	./build/test_sqrt64 1000000000 1

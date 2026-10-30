#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t seed = UINT64_C(0x3c6ef372fe94f82b);

static uint64_t random_bits(void) {
    uint64_t z = (seed += UINT64_C(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
    return z ^ (z >> 31);
}

#define EXEC(instruction) __asm__ volatile("msr nzcv, %[initial]\n" instruction "\nmrs %[flags], nzcv" \
    : [r] "+&r"(result), [flags] "=r"(flags), [taken] "+&r"(taken) \
    : [a] "r"(a), [b] "r"(b), [initial] "r"(initial) : "cc")
#define BRANCH(instruction) EXEC("mov %[taken], #1\n" instruction " 1f\nmov %[taken], #0\n1:")

static void record(FILE *out, uint64_t op, uint64_t a, uint64_t b, uint64_t before, uint64_t nzcv) {
    uint64_t result = before, flags, taken = 0, initial = nzcv << 28;
    switch (op) {
        case 0: EXEC("and %[r], %[a], #0x7fffffffffffffff"); break;
        case 1: EXEC("and %[r], %[a], #0xfffffffffffff"); break;
        case 2: EXEC("mov %[r], #0x7ff0000000000000"); break;
        case 3: EXEC("mov %[r], #0x4690000000000000"); break;
        case 4: EXEC("mov %[r], #0x10000000000000"); break;
        case 5: EXEC("mov %[r], #0x3fe0000000000000"); break;
        case 6: EXEC("ubfx %[r], %[a], #52, #11"); break;
        case 7: EXEC("add %[r], %[a], #1"); break;
        case 8: EXEC("sub %[r], %[a], #1"); break;
        case 9: EXEC("add %[r], %[a], %[b]"); break;
        case 10: EXEC("add %[r], %[a], %[b], lsl #52"); break;
        case 11: EXEC("orr %[r], %[a], %[b], lsl #52"); break;
        case 12: EXEC("sub %w[r], %w[a], %w[b]"); break;
        case 13: EXEC("lsr %[r], %[a], %[b]"); break;
        case 14: EXEC("mul %[r], %[a], %[b]"); break;
        case 15: EXEC("umulh %[r], %[a], %[b]"); break;
        case 16: BRANCH("cbz %[a],"); break;
        case 17: BRANCH("cbnz %[a],"); break;
        case 18: BRANCH("tbnz %[a], #63,"); break;
        case 19: BRANCH("tbz %[a], #63,"); break;
        case 20: EXEC("mov %w[r], #-53"); break;
        case 21: EXEC("sub %w[r], %w[a], #1023"); break;
        case 22: EXEC("add %w[r], %w[a], #1023"); break;
        case 23: EXEC("sub %w[r], %w[a], #969"); break;
        case 24: EXEC("mov %w[r], #64"); break;
        default: exit(2);
    }
    uint64_t row[8] = {op, a, b, before, nzcv, result, flags >> 28, taken};
    if (fwrite(row, sizeof row, 1, out) != 1) { perror("fwrite"); exit(1); }
}

int main(int argc, char **argv) {
    if (argc != 3) return 2;
    char *end;
    errno = 0;
    uint64_t count = strtoull(argv[2], &end, 10);
    if (errno || !*argv[2] || *end) return 2;
    FILE *out = fopen(argv[1], "wb");
    if (!out) { perror("fopen"); return 1; }
    uint64_t edge[] = {0, 1, 31, 32, 63, 64, 65, 0x7fffffff, 0x80000000,
        0xffffffff, UINT64_C(0x100000000), UINT64_C(0xfffffffffffff),
        UINT64_C(0x10000000000000), UINT64_C(0x1fffffffffffff), UINT64_C(0x20000000000000), UINT64_C(0x7fffffffffffffff),
        UINT64_C(0x8000000000000000), UINT64_MAX};
    uint64_t rows = 0;
    for (uint64_t op = 0; op < 25; ++op) {
        for (uint64_t i = 0; i < count; ++i) {
            uint64_t a = random_bits(), b = random_bits(), r = random_bits();
            record(out, op, a, b, r, random_bits() & 15);
            ++rows;
        }
        for (size_t i = 0; i < sizeof edge / sizeof *edge; ++i)
            for (size_t j = 0; j < sizeof edge / sizeof *edge; ++j)
                for (uint64_t flags = 0; flags < 16; ++flags) {
                    record(out, op, edge[i], edge[j], random_bits(), flags);
                    ++rows;
                }
    }
    if (fclose(out)) return 1;
    printf("integer_rows=%" PRIu64 " random_per_op=%" PRIu64 " seed=3c6ef372fe94f82b\n", rows, count);
    return 0;
}

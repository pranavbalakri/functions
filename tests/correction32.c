#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern float test_correct32(uint32_t, uint64_t);

static uint64_t seed = UINT64_C(0xa54ff53a5f1d36f1);

static uint32_t random_bits(void) {
    uint64_t z = (seed += UINT64_C(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
    return (uint32_t)(z ^ (z >> 31));
}

static uint32_t reference(uint32_t bits) {
    float x, y;
    memcpy(&x, &bits, sizeof x);
    __asm__ volatile("fsqrt %s0, %s1" : "=w"(y) : "w"(x));
    uint32_t result;
    memcpy(&result, &y, sizeof result);
    return result;
}

static int check(uint32_t bits, uint32_t q) {
    uint64_t n4 = (uint64_t)(0x800000 | (bits & 0x7fffff)) << ((bits >> 23) - 102);
    float y = test_correct32(q, n4);
    uint32_t got;
    memcpy(&got, &y, sizeof got);
    uint32_t expected = reference(bits);
    if (got == expected) return 0;
    printf("correction failure input=%08" PRIx32 " seed=%" PRIu32 " got=%08" PRIx32 " expected=%08" PRIx32 "\n",
        bits, q, got, expected);
    return 1;
}

int main(void) {
    uint64_t old_fpcr, old_fpsr;
    __asm__ volatile("mrs %0, fpcr\nmrs %1, fpsr\nmsr fpcr, xzr\nisb"
        : "=r"(old_fpcr), "=r"(old_fpsr));
    uint64_t count = 0, failures = 0;
    for (uint32_t i = 0; i < 1000000; ++i) {
        uint32_t bits = 0x3f800000 + (random_bits() & 0xffffff);
        int64_t q = (reference(bits) & 0x7fffff) + 0x800000;
        q += (int64_t)(random_bits() % 17) - 8;
        if (q < 0x800000) q = 0x800000;
        if (q > 0x1000000) q = 0x1000000;
        failures += check(bits, (uint32_t)q);
        ++count;
        if (failures) break;
    }
    uint32_t edge[] = {0x3f800000, 0x3f800001, 0x3fffffff, 0x40000000, 0x407ffffe, 0x407fffff};
    for (size_t i = 0; i < sizeof edge / sizeof *edge && !failures; ++i) {
        failures += check(edge[i], 0x800000);
        failures += check(edge[i], 0x1000000);
        count += 2;
    }
    __asm__ volatile("msr fpcr, %0\nmsr fpsr, %1\nisb" : : "r"(old_fpcr), "r"(old_fpsr));
    printf("forced_correction_cases=%" PRIu64 " failures=%" PRIu64 " seed=a54ff53a5f1d36f1\n", count, failures);
    return failures != 0;
}

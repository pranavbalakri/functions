#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

extern float verified_sqrtf(float);

static uint64_t parse(const char *s) {
    char *end;
    errno = 0;
    uint64_t n = strtoull(s, &end, 0);
    if (errno || !*s || *end) { fprintf(stderr, "invalid integer: %s\n", s); exit(2); }
    return n;
}

int main(int argc, char **argv) {
    if (argc != 4) {
        fprintf(stderr, "usage: %s begin end DN\n", argv[0]);
        return 2;
    }
    uint64_t begin = parse(argv[1]), end = parse(argv[2]), dn = parse(argv[3]);
    if (begin >= end || end > (UINT64_C(1) << 32) || dn > 1) return 2;
    uint64_t old_fpcr, old_fpsr, fpcr = dn << 25;
    __asm__ volatile("mrs %0, fpcr\nmrs %1, fpsr" : "=r"(old_fpcr), "=r"(old_fpsr));
    __asm__ volatile("msr fpcr, %0\nisb" : : "r"(fpcr));
    uint64_t failures = 0;
    struct timespec start, finish;
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (uint64_t i = begin; i < end; ++i) {
        uint32_t input = (uint32_t)i, got, expected;
        float x, actual, reference;
        memcpy(&x, &input, sizeof x);
        actual = verified_sqrtf(x);
        __asm__ volatile("fsqrt %s0, %s1" : "=w"(reference) : "w"(x));
        memcpy(&got, &actual, sizeof got);
        memcpy(&expected, &reference, sizeof expected);
        if (got != expected) {
            if (failures < 20)
                printf("mismatch input=%08" PRIx32 " got=%08" PRIx32 " expected=%08" PRIx32 "\n", input, got, expected);
            ++failures;
        }
    }
    clock_gettime(CLOCK_MONOTONIC, &finish);
    __asm__ volatile("msr fpcr, %0\nmsr fpsr, %1\nisb" : : "r"(old_fpcr), "r"(old_fpsr));
    double seconds = finish.tv_sec - start.tv_sec + (finish.tv_nsec - start.tv_nsec) * 1e-9;
    printf("checked=%" PRIu64 " begin=%" PRIu64 " end=%" PRIu64 " DN=%" PRIu64 " failures=%" PRIu64 " seconds=%.3f\n", end - begin, begin, end, dn, failures, seconds);
    return failures != 0;
}

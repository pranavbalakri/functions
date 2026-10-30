#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

int main(void) {
    uint64_t fpcr;
    __asm__ volatile("mrs %0, fpcr" : "=r"(fpcr));
    printf("FPCR=0x%016" PRIx64 "\n", fpcr);
    printf("RMode=%" PRIu64 " FZ=%" PRIu64 " DN=%" PRIu64 "\n",
           (fpcr >> 22) & UINT64_C(3),
           (fpcr >> 24) & UINT64_C(1),
           (fpcr >> 25) & UINT64_C(1));
    printf("exception_enables=0x%02" PRIx64 " AH=%" PRIu64 " FIZ=%" PRIu64 "\n",
           (fpcr >> 8) & UINT64_C(0x9f),
           (fpcr >> 1) & UINT64_C(1),
           fpcr & UINT64_C(1));
    return 0;
}

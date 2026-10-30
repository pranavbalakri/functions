.text
.globl _test_correct32
_test_correct32:
    mov x3, x1
    mov w4, #0
    b _verified_sqrtf_correct_entry

.text
.globl _test_correct64
_test_correct64:
    mov x3, x1
    mov x5, x2
    mov w4, #0
    b _verified_sqrt_correct_entry

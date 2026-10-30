.text
.p2align 2
.globl _verified_sqrt
_verified_sqrt:
    fmov x0, d0
    and x1, x0, #0x7fffffffffffffff
    cbz x1, Lreturn64
    tbnz x0, #63, Lspecial64
    mov x2, #0x7ff0000000000000
    cmp x0, x2
    b.eq Lreturn64
    b.hi Lspecial64
    mov w4, #0
    ubfx x1, x0, #52, #11
    cbnz x1, Lnormalize64
    mov x2, #0x4690000000000000
    fmov d1, x2
    fmul d0, d0, d1
    fmov x0, d0
    ubfx x1, x0, #52, #11
    mov w4, #-53
Lnormalize64:
    sub w1, w1, #1023
    asr w2, w1, #1
    add w4, w4, w2
    and w1, w1, #1
    add w1, w1, #1023
    and x0, x0, #0xfffffffffffff
    orr x0, x0, x1, lsl #52
    fmov d0, x0
    fmov d5, #0.5
    frsqrte d1, d0
    fmul d2, d0, d1
    frsqrts d2, d2, d1
    fmul d1, d1, d2
    fmul d2, d0, d1
    frsqrts d2, d2, d1
    fmul d1, d1, d2
    fmul d2, d0, d1
    frsqrts d2, d2, d1
    fmul d1, d1, d2
    fmul d2, d0, d1
    fmul d3, d1, d5
    fmsub d4, d2, d2, d0
    fmadd d0, d4, d3, d2
    ubfx x2, x0, #52, #11
    sub w2, w2, #969
    and x3, x0, #0xfffffffffffff
    mov x1, #0x10000000000000
    add x3, x3, x1
    mov w6, #64
    sub w6, w6, w2
    lsr x5, x3, x6
    lsl x3, x3, x2
    fmov x0, d0
    and x0, x0, #0xfffffffffffff
    add x0, x0, x1
Lcorrect64:
    add x2, x0, x0
    sub x2, x2, #1
    umulh x6, x2, x2
    mul x2, x2, x2
    cmp x5, x6
    b.lo Ldown64
    b.hi Lupper64
    cmp x3, x2
    b.lo Ldown64
Lupper64:
    add x2, x0, x0
    add x2, x2, #1
    umulh x6, x2, x2
    mul x2, x2, x2
    cmp x5, x6
    b.hi Lup64
    b.lo Lencode64
    cmp x3, x2
    b.hi Lup64
Lencode64:
    mov x1, #0x3fe0000000000000
    add x0, x0, x1
    add x0, x0, x4, lsl #52
    fmov d0, x0
Lreturn64:
    ret
Lspecial64:
    frsqrte d0, d0
    ret
Ldown64:
    sub x0, x0, #1
    b Lcorrect64
Lup64:
    add x0, x0, #1
    b Lcorrect64

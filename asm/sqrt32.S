.text
.p2align 2
.globl _verified_sqrtf
_verified_sqrtf:
    fmov w0, s0
    and w1, w0, #0x7fffffff
    cbz w1, Lreturn
    tbnz w0, #31, Lspecial
    mov w2, #0x7f800000
    cmp w0, w2
    b.eq Lreturn
    b.hi Lspecial
    mov w4, #0
    ubfx w1, w0, #23, #8
    cbnz w1, Lnormalize
    mov w2, #0x57800000
    fmov s1, w2
    fmul s0, s0, s1
    fmov w0, s0
    ubfx w1, w0, #23, #8
    mov w4, #-24
Lnormalize:
    sub w1, w1, #127
    asr w2, w1, #1
    add w4, w4, w2
    and w1, w1, #1
    add w1, w1, #127
    and w0, w0, #0x7fffff
    orr w0, w0, w1, lsl #23
    fmov s0, w0
    fmov s5, #0.5
    frsqrte s1, s0
    fmul s2, s0, s1
    frsqrts s2, s2, s1
    fmul s1, s1, s2
    fmul s2, s0, s1
    frsqrts s2, s2, s1
    fmul s1, s1, s2
    fmul s2, s0, s1
    fmul s3, s1, s5
    fmsub s4, s2, s2, s0
    fmadd s0, s4, s3, s2
    ubfx w2, w0, #23, #8
    sub w2, w2, #102
    and w3, w0, #0x7fffff
    mov w1, #0x800000
    add w3, w3, w1
    lsl x3, x3, x2
    fmov w0, s0
    and w0, w0, #0x7fffff
    add w0, w0, w1
Lcorrect:
#ifdef SQRT32_TESTING
.globl _verified_sqrtf_correct_entry
_verified_sqrtf_correct_entry:
#endif
    add w2, w0, w0
    sub w2, w2, #1
    umull x2, w2, w2
    cmp x3, x2
    b.lo Ldown
    add w2, w0, w0
    add w2, w2, #1
    umull x2, w2, w2
    cmp x3, x2
    b.hi Lup
    mov w1, #0x3f000000
    add w0, w0, w1
    add w0, w0, w4, lsl #23
    fmov s0, w0
Lreturn:
    ret
Lspecial:
    frsqrte s0, s0
    ret
Ldown:
    sub w0, w0, #1
    b Lcorrect
Lup:
    add w0, w0, #1
    b Lcorrect

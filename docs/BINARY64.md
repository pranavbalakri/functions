# Binary64 status

The 81-instruction AArch64 routine in `asm/sqrt64.S` uses scalar double-precision
FRSQRTE, three FRSQRTS Newton refinements, the FMA residual/correction, and exact
integer midpoint correction. It contains no FSQRT. Both signs of zero and positive
infinity return unchanged. Negative nonzero inputs and NaNs use FRSQRTE's special
result. The same FP-control precondition as binary32 is required.

Positive subnormals are multiplied by 2^106, with 53 subtracted from the final
square-root exponent. The normal core input lies in [1,4). For its 53-bit
significand M and exponent parity p, N = M * 2^(52+p). The candidate Q starts at
2^52 plus the fraction bits of the FMA result. The correction compares 4*N with
(2*Q-1)^2 and (2*Q+1)^2, adjusting Q until both strict midpoint inequalities hold.
MUL and UMULH supply the low and high halves of each product; unsigned comparisons
of the high halves precede comparisons of the low halves. The output encoding
then adds the saved exponent.

`Arm/Scalar64.lean` specializes the same Arm pseudocode used for binary32. It
uses exact dyadic arithmetic and nearest-even rounding, and shares the estimate
table in `Arm/Estimate.lean`. Hardware comparisons cover all seven FP operations,
including result bits and FPSR. The assembler's output is extracted into
`Arm/Sqrt64Code.lean` and checked on rebuild.

The assembly passed 2,014,705,018 comparisons with hardware FSQRT, including two
billion random inputs with different seeds for the two DN settings, explicit
subnormals, exponent boundaries, and neighbors of exact and rounded squares.
The scalar model passed 18,912,386 instruction comparisons. See
[the validation record](../validation/binary64.md).

These tests do not constitute a proof. The binary64 algorithm proof and machine
execution proof are still outstanding, as are the decoder extension and separate
validation of its additional integer and move forms. General dyadic rounding,
integer-root correction, and relocation lemmas from binary32 are available for
reuse. The completed universal machine theorem currently applies to binary32.

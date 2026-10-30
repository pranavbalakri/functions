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

`Sqrt/Correctness64.lean` proves `algorithm64_correct` for every input encoding
and both DN settings. Its specification, `SqrtSpec64`, requires nearest-even
rounding of the true square root for positive finite inputs, preserves signed
zeros and positive infinity, and specifies the exact negative-input and NaN
encodings. The proof uses the general integer-root certificate and correction
lemmas, proves exact subnormal scaling by 2^106, and proves that encoding and
rescaling preserve the required nearest result. The normalized core theorem
covers all 2^53 encodings in [1,4), without enumeration or an estimate-error
assumption. The reusable format-specific encoding, spacing, and exact-rounding
lemmas are separate from the square-root proof.

`Arm/Machine64.lean` extends the decoder with D-register operations, the required
64-bit integer forms, and MUL/UMULH. Its full-routine execution agrees with both
the proved algorithm and hardware on 2,232,976 inputs, including FPSR. Separate
instruction checks cover the additional forms and complete SIMD state, and
forced-correction tests exercise seeds above and below the correct root.

`WideArithmetic.lean` proves that MUL/UMULH reconstruct the exact 128-bit product
and that comparing the high halves and then the low halves equals comparison
of the represented integers. It also proves exact lower/upper midpoint formation
throughout the candidate range. `CorrectionBlock64.lean` proves execution of the
four extracted instructions at offsets 208–220 and the resulting lower-midpoint
square. `Execution64.lean` supplies execution-composition lemmas.

The kernel axiom audit reports only the existing standard axioms, with no
admitted goals or native proof computation. The remaining machine proof must
establish correction-loop control flow and termination and compose it with
input preparation, floating-point evaluation, encoding, return, and relocation.
The completed universal machine theorem currently applies to binary32; the
binary64 hardware tests do not replace that obligation.

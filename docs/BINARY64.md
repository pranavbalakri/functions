# Binary64 algorithm and machine proof

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

`WideArithmetic.lean` proves that MUL/UMULH reconstruct exact 128-bit products
and that high/low comparisons equal comparison of the represented integers.
`CorrectionStage64.lean` connects these operations to the extracted branch
instructions. `CorrectionTermination64.lean` proves that each adjustment moves
toward the unique nearest integer root, terminates, and preserves the radicand.
Its worst-case bound is `20*2^52+18` instructions for any candidate in
`[2^52,2^53]`; this bound needs no approximation-error assumption.

`NormalizedBody64.lean` composes the fifteen FP instructions, twelve integer
setup instructions, correction loop, and five encoding/return instructions.
`Word64.lean` proves the modular exponent addition, including negative scales
held in W4 and shifted through X4. `Normalize64.lean`, `Scale64.lean`, and
`Prepare64.lean` establish the normalized input and exact subnormal adjustment.
`Classify64.lean` and `SpecialReturn64.lean` cover zeros, infinities, negatives,
and NaNs.

`Arm/Correctness64.lean` proves `machine_sqrt64_correct`: execution from entry
through RET terminates within `20*2^52+75` instructions and returns `SqrtSpec64`
for every input encoding. Caller register contents and FPSR are arbitrary; the
FP controls, register-array sizes, and return-address conditions are explicit.
X7–X30, V6–V31, and FPCR are preserved. FPSR may accumulate intermediate flags;
matching the exception flags of a single FSQRT is not the result specification.

`machine64_correct` specializes this result to the executable model fixture,
proving its `2^58` budget sufficient for every input and either DN setting.
`sqrt64_relocated_correct` proves the same result at every aligned 64-bit code
address, including modular address wraparound. It proves relocation of every
extracted opcode and composes the steps. The general register, trace, modular
arithmetic, and relocation glue remains separate from square-root mathematics.

The full build and trust-zero kernel audit cover both precisions. Audited
theorems use only subsets of `propext`, `Classical.choice`, and `Quot.sound`.
There are no admitted goals or native proof computations. See
[BUILD.md](BUILD.md) for the theorem, trusted boundary, and reproduction commands.

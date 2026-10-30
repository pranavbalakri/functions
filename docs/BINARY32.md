# Binary32 algorithm and proof status

The implementation starts from the reciprocal-root refinement and final FMA
correction requested for this project. Markstein's *IA-64 and Elementary
Functions* (2000) is the original book reference; the directly consulted source
is Harrison, [Formal Verification of Square Root Algorithms](https://www.cl.cam.ac.uk/~jrh13/papers/sqrt.pdf),
published in 2003, especially sections 3.2 and 3.3. The book itself has not been
obtained or independently checked in this checkout.

Harrison separates approximation error from correct rounding. The Itanium proof
uses a different estimate and exponent range; its error bounds cannot simply be
reused for Arm. The user approved adding exact midpoint correction after the FMA
steps. This gives a short rounding proof independent of the estimate's accuracy.

## Computation

Zero returns unchanged, including negative zero. Positive infinity returns
unchanged. Other negative values and NaNs use `FRSQRTE`'s special-value result.
These paths matched `FSQRT` exhaustively under both DN settings and are covered
by the algorithm proof.

For positive finite `x`, multiply a subnormal by 2^48. Write the resulting
unbiased exponent as `2*k + parity`, with parity zero or one, and construct `z`
in `[1,4)`. Subnormal scaling subtracts 24 from the saved output exponent.

The initial approximation uses binary32 operations:

```text
y0 = FRSQRTE(z)
y1 = y0 * FRSQRTS(z*y0, y0)
y2 = y1 * FRSQRTS(z*y1, y1)
s = z*y2
h = y2*0.5
r = fma(-s, s, z)
q0 = fma(r, h, s)
```

Let `M` be the input's 24-bit significand and `p` its exponent parity. Set
`N = M * 2^(23+p)` and initialize `Q = 2^23 + fraction(q0)`. The exact correction
uses integer arithmetic:

```text
while 4*N < (2*Q - 1)^2: Q = Q - 1
while (2*Q + 1)^2 < 4*N: Q = Q + 1
```

The assembly rechecks both inequalities on each iteration. The final result is
`Q * 2^(k-23)`, encoded by integer exponent adjustment. All correction products
fit in 64 bits for the established normalized ranges. Only the floating-point
operations use single precision; the correction uses 32-bit significands and
64-bit integer products/comparisons.

## Proved results

`IntegerCertificate.lean` constructs the unique nearest integer root from
`Nat.sqrt`, excludes midpoint ties by parity, and proves that each correction
step moves toward this root. With fuel at least the starting distance, the
correction terminates at that root. `Nat.sqrt` is used only in the proof; the
assembly and executable correction do not call it.

`Correction32.lean` establishes input and seed bounds and proves that 2^23 steps
suffice for every normalized input and every possible approximation bit pattern.
`coreCorrect32` proves all 2^24 normalized inputs satisfy

```text
(2*Q - 1)^2 < 4*N < (2*Q + 1)^2.
```

`Encoding32.lean` connects those integer inequalities to the actual decoded
binary32 result. `normalizedCore32_correct` proves that result is strictly
closer to the true square root than every different finite binary32 value.
There are no ties in this domain. The theorem has no certificate hypothesis.
The reusable rounding lemmas are described in [ROUNDING.md](ROUNDING.md).

`Normalization32.lean` proves the exact power-of-two decomposition of every
positive normal input and the value of the encoded output after rescaling.
`Correctness32.lean` connects these facts to `algorithm32`:
`algorithm32_normal_strict_nearest` proves strict distance minimization for every
positive normal binary32 input. The reusable Arm encoding, spacing, and rounding
lemmas cover exponent boundaries as well as the interior of each binade.

`Subnormal32.lean` proves that the modeled multiplication by 2^48 is exact,
produces a normal value, and permits exact recovery of the square root by
rescaling. `Special32.lean` proves the signed-zero, infinity, negative-input,
and NaN results. `algorithm32_correct` combines these results for all 2^32 input
encodings and both DN settings, without enumeration.

Its independent specification, `SqrtSpec32`, preserves both zeros and positive
infinity, returns the default quiet NaN for negative nonzero non-NaN inputs, and
quiets input NaNs while preserving their bits unless DN requests the default
NaN. For positive finite inputs it requires a positive finite result nearest
to the mathematical square root among all finite binary32 values, choosing an
even significand in any tie. The proof establishes strict distance minimization,
so a square-root tie cannot occur. `Arm/Correctness32.lean` connects this algorithm
theorem to execution of the assembled instructions, as described below.

`CorrectionTermination.lean` proves execution of the extracted correction-loop
instructions from byte offset 184 to 224. Any candidate in `[2^23,2^24]` reaches
the algorithm's corrected significand in at most `12*2^23+10` instructions.
The proof covers both branch directions, arithmetic without wraparound, and
preservation of every general-purpose register except X0/X2, all SIMD registers,
FPCR, and FPSR. It assumes the radicand and candidate are already in their loop
entry registers; the subsequent block proofs establish these entry conditions.

`CorrectionReturn32.lean` composes the loop with the five result-encoding and
return instructions. For an encoded signed scale exponent and a return address
outside the code, it proves that S0 contains exactly `rescale32 (core32 x) k`
after returning through the caller's link register. The proof includes the
32-bit modular arithmetic used to add a negative exponent. All GPRs except
X0/X1/X2, all SIMD registers except V0, FPCR, and FPSR are preserved by this block.

`NormalizedBody32.lean` proves execution from byte offset 100 through return.
It composes the twelve floating-point instructions with the nine integer setup
instructions and the correction/return block. The setup proof establishes the
exact radicand and bounds the initial candidate for any floating-point output.
`normalized_body_rounds` proves nearest-even rounding of the normalized input's
square root times the saved power of two, for scale exponents from -125 to 126.
The instruction bound is `12*2^23+36`. The block preserves GPRs X4–X30, SIMD
registers V6–V31, and FPCR; FPSR may accumulate floating-point exception flags.

`NormalizeReturn32.lean` extends this execution proof back to byte offset 68.
The eight normalization instructions construct exactly `normalizedInput32` and
add `rootExponent32` to the saved scale exponent. Reusable signed-word lemmas
prove the arithmetic right shift and parity extraction for negative exponents.
The composed bound is `12*2^23+44`; GPRs X5–X30, SIMD registers V6–V31, and FPCR
are preserved.

`Scale32.lean` and `Prepare32.lean` prove the normal/subnormal branch and the
six scaling instructions. `NaNControl32.lean` proves that DN does not affect
multiplication of non-NaN operands. `PositiveReturn32.lean` composes these blocks
with normalization and proves algorithm equality for every positive finite
input from offset 32 through return.

`Classify32.lean` proves the initial classification branches.
`SpecialReturn32.lean` proves the signed-zero/infinity return and the FRSQRTE
special-value path. `Arm/Correctness32.lean` combines every path:
`machine_sqrt32_correct` proves that execution of the extracted code terminates
and returns a result satisfying `SqrtSpec32` for every input. Its preconditions
are entry PC zero, 32-entry general/SIMD register arrays, `supportedControls`
(RN-even, gradual underflow, masked exceptions, and ordinary FP behavior), and
a return address outside the code. DN is unrestricted, as are initial register
contents and FPSR. The bound is `12*2^23+61` instructions. X5–X30, V6–V31, and
FPCR are preserved. FPSR may accumulate flags; equality with FSQRT's exception
flags is not part of the result specification.

`Initial32.lean` specializes this theorem to the executable machine fixture.
`machine32_eq_algorithm32` proves algorithm equality, and `machine32_correct`
proves the result specification for all 2^32 input encodings and both DN settings.
The existing 2^28 fixture budget is now proved sufficient. These are universal
proofs, independent of the exhaustive hardware tests.

Earlier attempts to prove the original FMA-only core by kernel enumeration were
impractical: the direct finite universal proof hit a recursion limit, and a
balanced 4,096-input trial exceeded 45 seconds. The current universal core proof
uses mathematical invariants rather than enumerating inputs.

## Remaining work

The all-input machine theorem uses code loaded at modeled address zero.
Generalizing execution to arbitrary aligned load addresses remains open; this
relocation obligation must be closed before starting binary64. Remaining integer
instruction forms also need separate single-step hardware comparisons, beyond
their existing coverage in complete routine executions.

Generalizing the reusable rounding/encoding bridge to all overflow and underflow
cases is future work; the corrected algorithm needs only the exact scaling cases
proved here. No proof admits a goal or uses native proof computation.

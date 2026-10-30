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
These paths matched `FSQRT` exhaustively under both DN settings; their formal
all-input proofs remain open.

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

Earlier attempts to prove the original FMA-only core by kernel enumeration were
impractical: the direct finite universal proof hit a recursion limit, and a
balanced 4,096-input trial exceeded 45 seconds. The current universal core proof
uses mathematical invariants rather than enumerating inputs.

## Remaining work

1. Prove exact subnormal scaling and every special input case against the full
   IEEE/Arm result specification, then combine them with the normal-input proof.
2. Prove execution of the extracted words equals the algorithm for every permitted
   caller state, including correction-loop termination, frame conditions, and
   code placement. The current execution fuel is a test-fixture bound, not a
   proved machine-level bound.
3. Complete the reusable bridge from dyadic nearest-even rounding to the binary32
   encoder, exponent selection, and overflow/underflow behavior.

These obligations block the requested binary32 end-to-end theorem and the
transition to binary64. No proof admits a goal or uses native proof computation.

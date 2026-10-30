# Binary32 algorithm and proof status

The implementation starts from the reciprocal-root refinement and final FMA
correction requested for this project. Markstein's *IA-64 and Elementary
Functions* (2000) is the original book reference; the directly consulted source
for the rounding condition is Harrison,
[Formal Verification of Square Root Algorithms](https://www.cl.cam.ac.uk/~jrh13/papers/sqrt.pdf),
published in 2003, especially sections 3.2 and 3.3. The book itself has not been
obtained or independently checked in this checkout.

Harrison separates approximation error from correct rounding. A sufficient
condition is that the final unrounded approximation is closer to the true root
than any rounding midpoint is. His Itanium proof uses a different initial
estimate and exponent range; its numerical bounds cannot simply be reused for
this Arm routine. No claim that the Itanium theorem applies unchanged is made.

## Implemented computation

Zero returns unchanged, including negative zero. Positive infinity returns
unchanged. Other negative values and NaNs use `FRSQRTE`'s special-value result,
which matched `FSQRT` for every binary32 pattern under both tested DN settings.

For positive finite `x`, multiply a subnormal by 2^48. Then write the resulting
unbiased exponent as `2*k + parity`, with parity zero or one, and construct `z`
in `[1,4)`. Subnormal scaling subtracts 24 from the saved output exponent.

All operations below round to binary32 nearest-even:

```text
y0 = FRSQRTE(z)
y1 = y0 * FRSQRTS(z*y0, y0)
y2 = y1 * FRSQRTS(z*y1, y1)
s = z*y2
h = y2*0.5
r = fma(-s, s, z)
q = fma(r, h, s)
```

The final result is `q` scaled by 2^k through an exponent-field adjustment. This
normalization avoids intermediate underflow and overflow in the refinement core.
The proof that all scaling and exponent adjustments preserve correct rounding
still needs to be formalized; the exhaustive hardware test covers these paths
empirically.

## Exact midpoint certificates

For a normalized input, let `M` be its 24-bit integer significand and `p` its
exponent parity. Set `N = M * 2^(23+p)`. A candidate output corresponds to an
integer significand `Q`, including `Q=2^24` for an output rounded to 2. The
certificate is

```text
(2*Q - 1)^2 < 4*N < (2*Q + 1)^2.
```

The proved lemma `certificate32_sound` turns this certificate into a strict
half-unit distance from `sqrt(N)`. `square_root_not_half_integer` excludes exact
integer-radicand ties. `correction_error_identity` proves the real identity
behind the final residual correction. The executable checker found a valid
certificate for every one of the 2^24 normalized binary32 inputs.

## What is not proved

`CoreCorrect32` is an explicit proposition, not an axiom and not a theorem. It
asserts that all normalized inputs have certificates. The exhaustive executable
check does not prove this proposition in Lean. A direct kernel `decide` attempt
on the finite universal statement hit the recursion limit; a concrete one-input
kernel check succeeds. The large failed trial lives only in ignored `build/`.
No admitted theorem or weakened replacement was added.

A balanced Boolean range checker avoids the linear recursion shape. A kernel
trial on 64 normalized inputs succeeded; a trial on 4,096 inputs was stopped
after 45 seconds without a result. This has not supplied a practical exhaustive
kernel proof of all 16,777,216 inputs.

The remaining work is:

1. Connect the proved real RN-even semantics of dyadic rounding to the binary32
   encoder, exponent selection, and overflow/underflow behavior. The reusable
   arithmetic and rounding proofs are described in [ROUNDING.md](ROUNDING.md).
2. Prove `CoreCorrect32`, using Arm-specific error bounds plus a certified hard-case
   analysis, or a kernel-checked finite computation. No native proof computation
   is authorized.
3. Prove normalization, rescaling, and every special input case against the full
   IEEE/Arm result specification.
4. Prove execution of the extracted words equals the algorithm for every permitted
   caller state. Current machine/algorithm equivalence checks are tests.

These obligations block the requested binary32 end-to-end theorem and therefore
the transition to binary64. There is no `sorry`, new axiom, or `native_decide` in
the committed proof sources.

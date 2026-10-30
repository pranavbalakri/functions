# Rounding proofs

`Float/Rounding.lean` defines nearest-even integer rounding by two independent
requirements: the result minimizes absolute distance among all integers, and a
result at distance exactly one half is even. It proves uniqueness and sign
symmetry of this specification.

For every natural number `n` and shift `k`, `roundShiftEven_nearest` proves that
the implemented `roundShiftEven n k` returns this unique rounding of the real
number `n / 2^k`. The proof uses quotient/remainder arithmetic, covers midpoint
ties, and does not enumerate inputs. `roundShiftEven_inexact` identifies the
returned inexact bit with a nonzero remainder.

`Float/DyadicReal.lean` proves that the model's dyadic addition, multiplication,
and halving have exactly their expected real values. `Float/DyadicRounding.lean`
proves nearest-even rounding of a signed dyadic coefficient at any specified
binary exponent, including shifts in both directions. This covers the numerical
rounding calculation inside `round32`; it does not yet prove that its binary32
encoding, exponent selection, overflow, and underflow implement the full IEEE
specification.

`certificate32_nearest` and `certificate32_unique` connect the existing strict
midpoint certificates to the unique nearest-even integer significand of the
scaled square root. They retain the explicit certificate hypothesis.
`CoreCorrect32`, which would discharge that hypothesis for every normalized
input, remains unproved. These are reusable lemmas and intermediate results,
not a replacement for the requested end-to-end theorem.

`Arm/Scalar32Real.lean` connects the model's bit fields and finite-value decoder
to real arithmetic. `Sqrt/Encoding32.lean` proves the normalization identities
for inputs in `[1,4)` and outputs in `[1,2]`. Given a valid certificate,
`certificate32_result_unique_float` proves strict distance minimization against
every different finite binary32 value, not just the integer significand grid.
The proof handles candidates below 1 and above 2 separately, so it includes the
change in spacing at those boundaries. It excludes a rounding tie under the
certificate hypothesis; the universal certificate proof remains necessary.

Run `make proof` to build these proofs and run the axiom audit. They use Lean's
standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`; they add
no axioms and use neither admitted proofs nor native proof computation.

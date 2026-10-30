# Phase 0: machine-model decision

Date: 2026-10-29 (America/New_York).

Choose option 3: a minimal Lean instruction model transcribed from Arm's
architecture pseudocode. This is a selection, not a completed or validated model.
Implementation stops here at the requested Phase 0 checkpoint.

## 1. LNSym

Inspected commit `5c05220ff970e3bdd7813ad0c9ef3741522c8b92` of
[leanprover/LNSym](https://github.com/leanprover/LNSym/tree/5c05220ff970e3bdd7813ad0c9ef3741522c8b92).
The audit searched the instruction definitions and decoder, not just the README.

| Required operation | Finding |
| --- | --- |
| Scalar `FRSQRTE S/D` | No implementation found |
| Scalar `FRSQRTS S/D` | No implementation found |
| Scalar `FMUL S/D` | No implementation found |
| Scalar `FMADD`, `FMSUB`, `FNMSUB` | No implementation found |
| `FMOV` between W/X and S/D | Implemented in `Conversion_between_FP_and_Int.lean` |
| Immediate moves | Integer `MOVZ/MOVN/MOVK` and SIMD modified immediates are implemented; this is not general scalar FP arithmetic support |
| `B`, `B.cond`, `CBZ`, `CBNZ`, `RET` | Implemented |
| `TBZ/TBNZ`, scalar `FCMP` | No implementation found; integer classification could avoid these |
| Floating-point environment | `ArmState` has SIMD registers but no FPCR/FPSR fields |

Relevant pinned source: [FP instruction imports](https://github.com/leanprover/LNSym/blob/5c05220ff970e3bdd7813ad0c9ef3741522c8b92/Arm/Insts/DPSFP/Insts.lean),
[general FMOV](https://github.com/leanprover/LNSym/blob/5c05220ff970e3bdd7813ad0c9ef3741522c8b92/Arm/Insts/DPSFP/Conversion_between_FP_and_Int.lean),
[branches](https://github.com/leanprover/LNSym/blob/5c05220ff970e3bdd7813ad0c9ef3741522c8b92/Arm/Insts/BR/Insts.lean),
[state](https://github.com/leanprover/LNSym/blob/5c05220ff970e3bdd7813ad0c9ef3741522c8b92/Arm/State.lean).

LNSym would require adding the entire relevant FP subsystem. Its pinned toolchain
is also `nightly-2024-10-07`. It does not supply the needed machine semantics as-is.

## 2. Sail-to-Lean

Found and inspected [opencompl/sail-arm-lean](https://github.com/opencompl/sail-arm-lean/tree/5654b38c3221311758140f8044708142c95bf9ee)
at commit `5654b38c3221311758140f8044708142c95bf9ee`:

- `Armv9/Instrs64.lean`, `Common.lean`, `V8Base.lean`, `DecodeEnd.lean`, the root
  module, and `lakefile.toml` are empty in this snapshot.
- `build_log.txt` says the build was skipped. The README's zero-error count is
  therefore not evidence of a successful build.
- [FakeReal.lean](https://github.com/opencompl/sail-arm-lean/blob/5654b38c3221311758140f8044708142c95bf9ee/Armv9/FakeReal.lean)
  represents Sail's exact reals using Lean `Float`, including multiplication and
  square root. This cannot serve as the exact intermediate arithmetic for a
  correctly rounded FMA model.
- [ArmExtras.lean](https://github.com/opencompl/sail-arm-lean/blob/5654b38c3221311758140f8044708142c95bf9ee/Armv9/ArmExtras.lean)
  includes a termination-tactic fallback to `sorry`.

Also inspected upstream [rems-project/sail-arm](https://github.com/rems-project/sail-arm/tree/7d0581642d0e3aaca367bbc5650aca7c53057543)
at commit `7d0581642d0e3aaca367bbc5650aca7c53057543`. Its Armv9.4-A
[Makefile](https://github.com/rems-project/sail-arm/blob/7d0581642d0e3aaca367bbc5650aca7c53057543/arm-v9.4-a/Makefile)
has a Lean generation target, using forced output and noncomputable generation.
Its Lean support file also contains the termination fallback. Those flags alone
do not prove a model is unsound, but a generation target is not a checked,
executable model. I did not attempt a full Sail toolchain build. No ready-to-use
translation meeting this task's requirements was identified in this audit.

## 3. Selected fallback

Use exact integers and dyadic numbers for executable FP semantics, with separate
Mathlib real-number interpretation and rounding proofs. Native Lean `Float`
arithmetic must not stand in for exact intermediates or determine NaN payloads.
No instruction semantics, rounding specification, or correctness result will be
introduced as an axiom.

The planned source is the [Arm Architecture Reference Manual](https://developer.arm.com/documentation/ddi0487/latest/)
and its [machine-readable pseudocode](https://developer.arm.com/downloads/-/exploration-tools).
The direct Arm download page returned HTTP 403 during this audit. Before
transcription, archive and identify the exact Arm pseudocode release used. The
reviewed upstream Sail specification is a useful cross-check: its README identifies
the source as Arm's 2023-03 ASL snapshot. This does not replace checking the original
pseudocode.

The pinned Sail [shared pseudocode translation](https://github.com/rems-project/sail-arm/blob/7d0581642d0e3aaca367bbc5650aca7c53057543/arm-v9.4-a/src/v8_base.sail)
contains `RecipSqrtEstimate`, `FPRSqrtEstimate`, `FPRSqrtStepFused`, `FPMul`,
`FPMulAdd`, unpacking, rounding, NaN processing, and exception handling. Its
[instruction definitions](https://github.com/rems-project/sail-arm/blob/7d0581642d0e3aaca367bbc5650aca7c53057543/arm-v9.4-a/src/instrs64.sail)
also expose operand negations and scalar register writes.

Keep the model limited to the instructions actually selected for the routine:
S/D estimate, multiply, fused correction operations, bit moves, integer
classification, constant construction, branches, and return. Model instruction
decoding from 32-bit words, register widths, PC, FPCR, and relevant FPSR effects.
Do not assume an abstract instruction list equals the assembled program.

Two semantic details need particular care:

- `FRSQRTE` uses Arm's estimate algorithm, not a correctly rounded reciprocal
  square root. Newer feature-dependent behavior must be resolved for this M4.
- `FRSQRTS` fuses the expression `(3 - a*b)/2` and has special-value rules. It
  cannot be modeled as a sequence of separately rounded multiply/subtract/divide
  instructions. FMA variants also negate particular operands before NaN handling.

## Preconditions and all-input coverage

The theorem must cover every input bit pattern. Finite nonnegative inputs get
the real square root rounded once to nearest, ties to even; signed zeros,
negative inputs, infinities, and NaNs require an explicit Arm-compatible result
specification. In particular, Mathlib's real square root of a negative number is
not a substitute for the required NaN result. NaN payloads and quieting must be
specified for bitwise comparison with `FSQRT`.

Nearest-even rounding and flush-to-zero disabled remain explicit preconditions.
Account explicitly for exception traps, default-NaN mode, alternative FP handling,
and input flushing. The current machine probe reports all of these controls zero.
Do not silently use `FPCR = 0` as a stronger theorem assumption; settle the precise
control-state contract when defining the model. Usual user-mode FP/SIMD access,
valid code memory, and call/return conditions also belong in the machine contract.

## Required validation before relying on the fallback

No model-versus-hardware differential tests have run: the model has not been
implemented at this checkpoint. The C program in `tests/fp_environment.c` only
reads the environment.

Before algorithm proofs, compare the actual executable Lean definitions with
instruction outputs on this Mac. Use at least one million deterministic random
operand tuples per used FP instruction and precision, plus directed tests for
NaNs, signed zeros, infinities, subnormal boundaries, cancellation, halfway cases,
underflow, and overflow. Record seeds, counts, FPCR, hardware, toolchain, and all
mismatches; compare FPSR effects wherever modeled. Exhaust the small estimate
lookup domain and test normalization/exponent boundaries. Check moves, register
aliasing, scalar upper-bit behavior, decoder fields, and both outcomes of branches.
Comparing two C implementations would not validate the Lean definitions.

These tests are evidence for the model's hardware correspondence, not a proof of
it. Later milestones still require the full binary32 input sweep, the binary32
end-to-end proof, then billions of binary64 tests and its end-to-end proof. No
`native_decide` has been used; ask before introducing it into a proof.

## File boundaries after continuation

Keep general rounding and real-number lemmas under `VerifiedSqrt/Float/`, the
instruction model and proof glue under `VerifiedSqrt/Arm/`, and the algorithm and
machine proofs under `VerifiedSqrt/Sqrt/`. These directories will be added with
their implementations. The only current Lean theorem is a Mathlib setup check.

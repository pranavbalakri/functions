# Arm model provenance and scope

The original Arm archive is now available locally under `.research/`:

- [ISA_A64_xml_A_profile-2023-03.tar.gz](https://developer.arm.com/-/media/developer/products/architecture/armv9-a-architecture/2023-03/ISA_A64_xml_A_profile-2023-03.tar.gz)
- SHA-256: `4be65585693d1bf1f1765bcc1a2493ce5df99718cc33d6e98fc3e83f76019bfd`
- The selected directory within it is `ISA_A64_xml_A_profile-2023-03/`, not the
  older XHTML snapshot or the `_OPT` directory also present in the archive.
- The archive remains ignored and is not redistributed in this repository.

`shared_pseudocode.xml` supplies `FPUnpackBase`, `FPRoundBase`, `FPProcessNaN`,
`FPProcessNaNs`, `FPProcessNaNs3`, `FPMul`, `FPMulAdd`, `FPRSqrtEstimate`,
`RecipSqrtEstimate`, and `FPRSqrtStepFused`. Instruction XML files supply the
encodings, register accesses, negations, and branching behavior. The corresponding
Sail translation pinned in the Phase 0 report was also cross-checked.

The Lean definitions implement the binary32, nearest-even, gradual-underflow,
non-AltFP cases. They preserve NaN payload/sign selection when DN is clear and
return default NaNs when DN is set. Underflow is detected before rounding,
including values rounded up to the smallest normal. FPSR results include invalid,
divide-by-zero, overflow, underflow, and inexact. Nonzero initial FPSR bits are
preserved by instruction execution. Masked exceptions are required.

Exact arithmetic is represented as an integer coefficient times an integral
power of two. `round32` normalizes using the coefficient's bit length, rounds the
discarded integer remainder to nearest-even, and encodes the result. This is an
executable specialization of the pseudocode's exact-real rounding operation;
the general proof connecting it to a Mathlib real-number rounding relation is
still outstanding. Native `Float` arithmetic is not used in these definitions.

The estimate loop has 512 fuel steps. For the relevant inputs, the transformed
index is at least 257, and the pseudocode loop has already stopped by `b=1024`.
`estimate_table_bounds` checks all 384 indices in Lean's kernel and proves that
the returned estimate lies in `[256,512)`, with squared bounds corresponding to
a relative-error enclosure of `1 ± 1/256` across each index bin. It uses
`decide +kernel`, not native computation, and has no axioms. The full exponent
and input-normalization connection to the reciprocal-square-root error bound
remains to be proved.

`Machine.lean` decodes only the forms needed by the routine:

| Group | Supported forms |
| --- | --- |
| FP arithmetic | Scalar S `FRSQRTE`, `FRSQRTS`, `FMUL`, all four FMA sign combinations |
| Moves | W/S bit moves, scalar immediate `0.5`, W `MOVZ/MOVN` |
| Integer arithmetic | W add/sub immediate, W add with LSL, W ORR with LSL, W/X CMP with LSL, UMULL |
| Bit operations | W AND with an unrotated low contiguous mask, nonwrapping UBFX, ASR, X LSLV |
| Branches | W CBZ/CBNZ, low-32-bit TBZ/TBNZ, B, B.EQ/B.LO/B.HI, RET |

W-register writes clear the upper 32 bits of X; scalar FP writes clear the upper
96 bits of V. General register 31 is the zero register for these forms. Branch
displacements are signed byte offsets, PC arithmetic wraps modulo 2^64, and RET
reads its register operand. Unsupported forms return `none`.

`supportedControls` requires RMode=00, FZ=FIZ=AH=NEP=0, and exception enables zero.
DN is free. FZ16/AHP and unrelated controls do not affect this S-only fragment.
The RPRES estimate behavior is inactive when AH is zero. User-mode FP/SIMD access
and instruction availability are assumed; privilege and trap controls are outside
this fragment.

`machine32` is a test fixture: code starts at address zero, X30 is 4096, other
initial general registers are zero, and there is a 2^28-step execution budget.
It is not a theorem that these initial values may be assumed for real callers.
The final machine proof must quantify the caller state, prove register/frame
conditions and code placement, and establish termination and algorithm equality.

Validation compares the actual compiled Lean definitions with hardware, not a
second C model. Per-instruction testing covers the FP operations and now also X LSLV, UMULL,
W/X CMP, B, B.EQ, B.LO, and B.HI. The added integer forms were transcribed from
`lslv.xml`, `umaddl.xml`, `subs_addsub_shift.xml`, `b_uncond.xml`, and `b_cond.xml`.
Eight million random cases plus boundary cases check registers, NZCV, PC, and
preservation of SIMD/control state. Moves and remaining integer forms are
exercised in complete routine executions; separate single-step tests for them
and arbitrary SIMD upper-lane writes remain outstanding. These limitations are part
of the remaining machine-model validation work.

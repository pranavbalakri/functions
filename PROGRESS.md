# Progress

Updated 2026-10-29 (America/New_York).

- Phase 0 decision: select a minimal Lean model transcribed from Arm pseudocode.
- Audited LNSym, the published Sail-to-Lean snapshot, and upstream Sail Arm.
  Evidence and pinned revisions are in [docs/MODEL_DECISION.md](docs/MODEL_DECISION.md).
- Installed elan 4.2.4 and Lean 4.35.0; pinned Mathlib 4.35.0 and dependencies.
- Apple M4 environment probe passed: FPCR is zero, including nearest-even rounding
  and flush-to-zero disabled.
- `lake build` and the setup check with `lean --trust=0` passed. `#print axioms`
  reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Stop at Phase 0. No sqrt algorithm, instruction model, end-to-end proof,
  differential instruction tests, or exhaustive/random sqrt tests exist yet.
- No new axioms or `native_decide` have been introduced.

Open work after continuation: obtain and pin the original Arm pseudocode (the
download page returned 403), define the full special-value/control-state contract,
implement and test the model against this Mac, then complete binary32 before
binary64. Preserve the all-input theorem; ask before any `native_decide` proof.

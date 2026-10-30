module

public import VerifiedSqrt.Arm.Execution

@[expose] public section

namespace VerifiedSqrt.Arm

def runAt (code : Array UInt32) (base returnPC : UInt64) : Nat → Machine → Option Machine
  | 0, s => if s.pc == returnPC then some s else none
  | fuel + 1, s => do
    if s.pc == returnPC then return s
    if s.pc.toNat % 4 != 0 then none else do
      let word ← code[(s.pc - base).toNat / 4]?
      let next ← step word s
      runAt code base returnPC fuel next

theorem runAt_zero_base (code : Array UInt32) (stop : UInt64) (fuel : Nat) (s : Machine) :
    runAt code 0 stop fuel s = run code stop fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih => simp only [runAt, run, UInt64.sub_zero, ih]

theorem runAt_at_stop (code : Array UInt32) (base stop : UInt64) (fuel : Nat)
    (s : Machine) (h : s.pc = stop) : runAt code base stop fuel s = some s := by
  cases fuel <;> simp [runAt, h]

theorem runAt_step (code : Array UInt32) (base stop : UInt64) (fuel : Nat)
    (s t : Machine) (word : UInt32) (hne : s.pc ≠ stop) (ha : s.pc.toNat % 4 = 0)
    (hf : code[(s.pc - base).toNat / 4]? = some word) (hs : step word s = some t) :
    runAt code base stop (fuel + 1) s = runAt code base stop fuel t := by
  simp [runAt, hne, ha, hf, hs]

end VerifiedSqrt.Arm

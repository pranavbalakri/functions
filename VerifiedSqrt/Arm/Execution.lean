module

public import VerifiedSqrt.Arm.Machine

@[expose] public section

namespace VerifiedSqrt.Arm

theorem run_step (code : Array UInt32) (stop : UInt64) (fuel : Nat)
    (s t : Machine) (word : UInt32) (hne : s.pc ≠ stop)
    (ha : s.pc.toNat % 4 = 0) (hf : code[s.pc.toNat / 4]? = some word)
    (hs : step word s = some t) :
    run code stop (fuel + 1) s = run code stop fuel t := by
  simp [run, hne, ha, hf, hs]

theorem run_at_stop (code : Array UInt32) (stop : UInt64) (fuel : Nat)
    (s : Machine) (h : s.pc = stop) : run code stop fuel s = some s := by
  cases fuel <;> simp [run, h]

end VerifiedSqrt.Arm

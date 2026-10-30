module

public import VerifiedSqrt.Arm.Machine

public section

namespace VerifiedSqrt.Arm

theorem Machine.writeW_size (s : Machine) (r : Nat) (w : UInt32) :
    (s.writeW r w).x.size = s.x.size := by
  by_cases h : r = 31 <;> simp [Machine.writeW, h]

theorem Machine.writeW_fpcr (s : Machine) (r : Nat) (w : UInt32) :
    (s.writeW r w).fpcr = s.fpcr := by
  by_cases h : r = 31 <;> simp [Machine.writeW, h]

theorem Machine.writeX_size (s : Machine) (r : Nat) (w : UInt64) :
    (s.writeX r w).x.size = s.x.size := by
  by_cases h : r = 31 <;> simp [Machine.writeX, h]

theorem Machine.writeX_fpcr (s : Machine) (r : Nat) (w : UInt64) :
    (s.writeX r w).fpcr = s.fpcr := by
  by_cases h : r = 31 <;> simp [Machine.writeX, h]

theorem Machine.writeS_size (s : Machine) (r : Nat) (w : UInt32) :
    (s.writeS r w).x.size = s.x.size := rfl

theorem Machine.writeS_fpcr (s : Machine) (r : Nat) (w : UInt32) :
    (s.writeS r w).fpcr = s.fpcr := rfl

theorem Machine.writeFP_size (s : Machine) (r : Nat) (w : FPResult) :
    (s.writeFP r w).x.size = s.x.size := rfl

theorem Machine.writeFP_fpcr (s : Machine) (r : Nat) (w : FPResult) :
    (s.writeFP r w).fpcr = s.fpcr := rfl

theorem run_invariants (code : Array UInt32)
    (hstep : ∀ word, word ∈ code → ∀ s t, step word s = some t →
      t.x.size = s.x.size ∧ t.fpcr = s.fpcr)
    (stop : UInt64) (fuel : Nat)
    (s t : Machine) (hr : run code stop fuel s = some t) :
    t.x.size = s.x.size ∧ t.fpcr = s.fpcr := by
  induction fuel generalizing s with
  | zero =>
    by_cases hp : s.pc = stop
    · have ht : s = t := by simpa [run, hp] using hr
      subst t
      exact ⟨rfl, rfl⟩
    · simp [run, hp] at hr
  | succ fuel ih =>
    by_cases hp : s.pc = stop
    · have ht : s = t := by simpa [run, hp] using hr
      subst t
      exact ⟨rfl, rfl⟩
    by_cases ha : s.pc.toNat % 4 = 0
    · cases hw : code[s.pc.toNat / 4]? with
      | none => simp [run, hp, ha, hw] at hr
      | some word =>
        cases he : step word s with
        | none => simp [run, hp, ha, hw, he] at hr
        | some u =>
          have hu : run code stop fuel u = some t := by simpa [run, hp, ha, hw, he] using hr
          have hi := ih u hu
          have hj := hstep word (Array.mem_of_getElem? hw) s u he
          exact ⟨hi.1.trans hj.1, hi.2.trans hj.2⟩
    · simp [run, hp, ha] at hr

end VerifiedSqrt.Arm

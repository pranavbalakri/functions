module

public import VerifiedSqrt.Arm.Execution64
public import VerifiedSqrt.Arm.Relocation64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem run64_relocate (code : Array UInt32)
    (hstep : ∀ base s word, word ∈ code → supportedControls s.fpcr = true → s.x.size = 32 →
      step64 word (s.relocate base) = (step64 word s).map (Machine.relocate base))
    (hkeep : ∀ word, word ∈ code → ∀ s t, step64 word s = some t →
      t.x.size = s.x.size ∧ t.fpcr = s.fpcr)
    (base stop : UInt64) (hb : base.toNat % 4 = 0) (fuel : Nat) (s t : Machine)
    (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hr : run64 code 0 stop fuel s = some t) :
    run64 code base (base + stop) fuel (s.relocate base) = some (t.relocate base) := by
  induction fuel generalizing s with
  | zero =>
    by_cases hp : s.pc = stop
    · have he : s = t := by simpa [run64, UInt64.sub_zero, hp] using hr
      subst t
      exact run64_at_stop _ _ _ _ _ (by rw [Machine.relocate_pc, hp])
    · simp [run64, hp] at hr
  | succ fuel ih =>
    by_cases hp : s.pc = stop
    · have he : s = t := by simpa [run64, UInt64.sub_zero, hp] using hr
      subst t
      exact run64_at_stop _ _ _ _ _ (by rw [Machine.relocate_pc, hp])
    by_cases ha : s.pc.toNat % 4 = 0
    · cases hw : code[s.pc.toNat / 4]? with
      | none => simp [run64, UInt64.sub_zero, hp, ha, hw] at hr
      | some word =>
        cases he : step64 word s with
        | none => simp [run64, UInt64.sub_zero, hp, ha, hw, he] at hr
        | some u =>
          have hu : run64 code 0 stop fuel u = some t := by simpa [run64, UInt64.sub_zero, hp, ha, hw, he] using hr
          have hinv := hkeep word (Array.mem_of_getElem? hw) s u he
          have hcu : supportedControls u.fpcr = true := by rw [hinv.2]; exact hc
          have hword : word ∈ code := Array.mem_of_getElem? hw
          have hrel : step64 word (s.relocate base) = some (u.relocate base) := by
            rw [hstep base s word hword hc hs, he, Option.map_some]
          have hp' : (s.relocate base).pc ≠ base + stop := by
            rw [Machine.relocate_pc]
            intro he
            exact hp ((UInt64.add_right_inj base).mp he)
          have ha' : (s.relocate base).pc.toNat % 4 = 0 := by
            rw [Machine.relocate_pc, aligned_relocate base s.pc hb, ha]
          have hw' : code[((s.relocate base).pc - base).toNat / 4]? = some word := by
            rw [Machine.relocate_pc, UInt64.add_comm base s.pc, UInt64.add_sub_cancel]
            exact hw
          rw [run64_step code base (base + stop) fuel _ _ word hp' ha' hw' hrel]
          exact ih u hcu (hinv.1.trans hs) hu
    · simp [run64, hp, ha] at hr

end VerifiedSqrt.Arm

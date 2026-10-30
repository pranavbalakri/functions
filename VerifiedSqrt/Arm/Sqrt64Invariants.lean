module

public import VerifiedSqrt.Arm.StepInvariants
public import VerifiedSqrt.Arm.RelocateInstructions64

public section

namespace VerifiedSqrt.Arm

theorem Machine.writeD_size (s : Machine) (r : Nat) (w : UInt64) :
    (s.writeD r w).x.size = s.x.size := rfl

theorem Machine.writeD_fpcr (s : Machine) (r : Nat) (w : UInt64) :
    (s.writeD r w).fpcr = s.fpcr := rfl

theorem Machine.writeFP64_size (s : Machine) (r : Nat) (w : FPResult64) :
    (s.writeFP64 r w).x.size = s.x.size := rfl

theorem Machine.writeFP64_fpcr (s : Machine) (r : Nat) (w : FPResult64) :
    (s.writeFP64 r w).fpcr = s.fpcr := rfl

theorem sqrt64_step_invariants (word : UInt32) (hw : word ∈ sqrt64Code)
    (s t : Machine) (h : step64 word s = some t) :
    t.x.size = s.x.size ∧ t.fpcr = s.fpcr := by
  by_cases hc : supportedControls s.fpcr = true
  · have hw := sqrt64_code_cases word hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [step64_setup_10, step64_input_magnitude, step64_input_zero, step64_input_sign, step64_input_infinity, step64_input_compare, step64_input_equal, step64_input_higher, step64_scale_zero, step64_input_exponent, step64_input_normal, step64_scale_bits, step64_scale_scalar, step64_scale_multiply, step64_scale_exponent, step64_normalize_1, step64_normalize_2, step64_normalize_3, step64_normalize_4, step64_normalize_5, step64_normalize_6, step64_normalize_7, step64_normalize_8, step64_float_half, step64_float_estimate, step64_float_product, step64_float_step, step64_float_refine, step64_float_half_estimate, step64_float_residual, step64_float_correction, step64_setup_1, step64_setup_2, step64_setup_3, step64_setup_4, step64_setup_5, step64_setup_6, step64_setup_7, step64_setup_8, step64_setup_9, step64_setup_12, step64_double_candidate, step64_lower_midpoint, step64_square_high, step64_square_low, step64_compare_high, step64_lo80, step64_hi12, step64_compare_low, step64_lo68, step64_upper_midpoint, step64_hi52, step64_lo12, step64_hi40, step64_result_bias, step64_add_result_exponent, step64_return, step64_special_estimate, step64_decrement, step64_back_down, step64_increment, step64_back_up, hc] at h
      cases h
      simp only [Machine.advanceW, Machine.advanceX, Machine.advanceD, compare64State,
        Machine.writeW_size, Machine.writeW_fpcr, Machine.writeX_size, Machine.writeX_fpcr,
        Machine.writeD_size, Machine.writeD_fpcr, Machine.writeFP64_size, Machine.writeFP64_fpcr,
        and_self]
  · have hc : supportedControls s.fpcr = false := Bool.eq_false_iff.mpr hc
    simp [step64, hc] at h

theorem run64_invariants (code : Array UInt32)
    (hstep : ∀ word, word ∈ code → ∀ s t, step64 word s = some t →
      t.x.size = s.x.size ∧ t.fpcr = s.fpcr)
    (base stop : UInt64) (fuel : Nat)
    (s t : Machine) (hr : run64 code base stop fuel s = some t) :
    t.x.size = s.x.size ∧ t.fpcr = s.fpcr := by
  induction fuel generalizing s with
  | zero =>
    by_cases hp : s.pc = stop
    · have ht : s = t := by simpa [run64, hp] using hr
      subst t
      exact ⟨rfl, rfl⟩
    · simp [run64, hp] at hr
  | succ fuel ih =>
    by_cases hp : s.pc = stop
    · have ht : s = t := by simpa [run64, hp] using hr
      subst t
      exact ⟨rfl, rfl⟩
    by_cases ha : s.pc.toNat % 4 = 0
    · cases hw : code[(s.pc - base).toNat / 4]? with
      | none => simp [run64, hp, ha, hw] at hr
      | some word =>
        cases he : step64 word s with
        | none => simp [run64, hp, ha, hw, he] at hr
        | some u =>
          have hu : run64 code base stop fuel u = some t := by simpa [run64, hp, ha, hw, he] using hr
          have hi := ih u hu
          have hj := hstep word (Array.mem_of_getElem? hw) s u he
          exact ⟨hi.1.trans hj.1, hi.2.trans hj.2⟩
    · simp [run64, hp, ha] at hr

end VerifiedSqrt.Arm

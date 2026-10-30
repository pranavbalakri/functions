module

public import VerifiedSqrt.Arm.StepInvariants
public import VerifiedSqrt.Arm.RelocateInstructions32

public section

namespace VerifiedSqrt.Arm

theorem sqrt32_step_invariants (word : UInt32) (hw : word ∈ sqrt32Code)
    (s t : Machine) (h : step word s = some t) :
    t.x.size = s.x.size ∧ t.fpcr = s.fpcr := by
  by_cases hc : supportedControls s.fpcr = true
  · have hw := sqrt32_code_cases word hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [step_scalar_to_word, step_input_magnitude, step_input_zero, step_input_sign, step_input_infinity, step_input_compare, step_input_equal, step_input_higher, step_scale_zero, step_input_exponent, step_input_normal, step_scale_bits, step_scale_scalar, step_scale_multiply, step_scale_exponent, step_unbias_exponent, step_halve_exponent, step_save_exponent, step_exponent_parity, step_bias_parity, step_setup_seed_fraction, step_normalize_bits, step_result_to_scalar, step_float_half, step_float_estimate, step_float_product, step_float_step, step_float_refine, step_float_half_estimate, step_float_residual, step_float_correction, step_setup_exponent, step_setup_shift, step_setup_fraction, step_setup_hidden_bit, step_setup_significand, step_setup_radicand, step_add_result_bias, step_double_candidate, step_lower_midpoint, step_square_midpoint, step_compare_midpoint, step_branch_lower, step_upper_midpoint, step_branch_upper, step_result_bias, step_add_result_exponent, step_return, step_special_estimate, step_decrement_candidate, step_back_lower, step_increment_candidate, step_back_upper, hc] at h
      cases h
      simp only [Machine.advanceW, Machine.advanceX, Machine.advanceS,
        Machine.writeW_size, Machine.writeW_fpcr, Machine.writeX_size, Machine.writeX_fpcr,
        Machine.writeS_size, Machine.writeS_fpcr, Machine.writeFP_size, Machine.writeFP_fpcr,
        and_self]
  · have hc : supportedControls s.fpcr = false := Bool.eq_false_iff.mpr hc
    simp [step, hc] at h

end VerifiedSqrt.Arm

module

public import VerifiedSqrt.Arm.Relocation
public import VerifiedSqrt.Arm.Sqrt32Cases
public import VerifiedSqrt.Arm.InstructionProof
public import VerifiedSqrt.Arm.SetupInstructions
public import VerifiedSqrt.Arm.InputInstructions
public import VerifiedSqrt.Arm.NormalizeInstructions
public import VerifiedSqrt.Arm.FloatInstructions

@[expose] public section

namespace VerifiedSqrt.Arm

theorem sqrt32_step_relocate (base : UInt64) (s : Machine) (word : UInt32)
    (hw : word ∈ sqrt32Code) (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32) :
    step word (s.relocate base) = (step word s).map (Machine.relocate base) := by
  have hw := sqrt32_code_cases word hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [
      step_scalar_to_word, step_input_magnitude, step_input_zero,
      step_input_sign, step_input_infinity, step_input_compare,
      step_input_equal, step_input_higher, step_scale_zero,
      step_input_exponent, step_input_normal, step_scale_bits,
      step_scale_scalar, step_scale_multiply, step_scale_exponent,
      step_unbias_exponent, step_halve_exponent, step_save_exponent,
      step_exponent_parity, step_bias_parity, step_setup_seed_fraction,
      step_normalize_bits, step_result_to_scalar, step_float_half,
      step_float_estimate, step_float_product, step_float_step,
      step_float_refine, step_float_half_estimate, step_float_residual,
      step_float_correction, step_setup_exponent, step_setup_shift,
      step_setup_fraction, step_setup_hidden_bit, step_setup_significand,
      step_setup_radicand, step_add_result_bias, step_double_candidate,
      step_lower_midpoint, step_square_midpoint, step_compare_midpoint,
      step_branch_lower, step_upper_midpoint, step_branch_upper,
      step_result_bias, step_add_result_exponent, step_return,
      step_special_estimate, step_decrement_candidate, step_back_lower,
      step_increment_candidate, step_back_upper, hc,
      hs, Machine.advanceW,
      Machine.advanceX, Machine.advanceS,
      Machine.relocate_writeW, Machine.relocate_writeX, Machine.relocate_writeS,
      Machine.relocate_writeFP, Machine.relocate_flags,
      Machine.readW_relocate, Machine.readX_relocate, Machine.readX_relocate_link,
      Machine.readS_relocate, Machine.relocate_pc, Machine.relocate_fpcr,
      Machine.relocate_fpsr, Machine.relocate_negative, Machine.relocate_zero,
      Machine.relocate_carry, Machine.relocate_overflow, branchPC_relocate,
      UInt64.add_assoc, apply_ite]

end VerifiedSqrt.Arm

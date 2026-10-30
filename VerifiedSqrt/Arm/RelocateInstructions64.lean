module

public import VerifiedSqrt.Arm.Relocation64
public import VerifiedSqrt.Arm.Sqrt64Cases
public import VerifiedSqrt.Arm.InstructionProof64
public import VerifiedSqrt.Arm.Return64
public import VerifiedSqrt.Arm.Setup64
public import VerifiedSqrt.Arm.InputInstructions64
public import VerifiedSqrt.Arm.Normalize64
public import VerifiedSqrt.Arm.FloatInstructions64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem sqrt64_step_relocate (base : UInt64) (s : Machine) (word : UInt32)
    (hw : word ∈ sqrt64Code) (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32) :
    step64 word (s.relocate base) = (step64 word s).map (Machine.relocate base) := by
  have hw := sqrt64_code_cases word hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [
      step64_setup_10, step64_input_magnitude, step64_input_zero, step64_input_sign, step64_input_infinity, step64_input_compare, step64_input_equal, step64_input_higher, step64_scale_zero, step64_input_exponent, step64_input_normal, step64_scale_bits, step64_scale_scalar, step64_scale_multiply, step64_scale_exponent, step64_normalize_1, step64_normalize_2, step64_normalize_3, step64_normalize_4, step64_normalize_5, step64_normalize_6, step64_normalize_7, step64_normalize_8, step64_float_half, step64_float_estimate, step64_float_product, step64_float_step, step64_float_refine, step64_float_half_estimate, step64_float_residual, step64_float_correction, step64_setup_1, step64_setup_2, step64_setup_3, step64_setup_4, step64_setup_5, step64_setup_6, step64_setup_7, step64_setup_8, step64_setup_9, step64_setup_12, step64_double_candidate, step64_lower_midpoint, step64_square_high, step64_square_low, step64_compare_high, step64_lo80, step64_hi12, step64_compare_low, step64_lo68, step64_upper_midpoint, step64_hi52, step64_lo12, step64_hi40, step64_result_bias, step64_add_result_exponent, step64_return, step64_special_estimate, step64_decrement, step64_back_down, step64_increment, step64_back_up, hc, hs,
      Machine.advanceW, Machine.advanceX, Machine.advanceD, compare64State,
      Machine.relocate_writeW, Machine.relocate_writeX, Machine.relocate_writeD,
      Machine.relocate_writeFP64, Machine.relocate_flags,
      Machine.readW_relocate, Machine.readX_relocate, Machine.readX_relocate_link,
      Machine.readD_relocate, Machine.relocate_pc, Machine.relocate_fpcr,
      Machine.relocate_fpsr, Machine.relocate_negative, Machine.relocate_zero,
      Machine.relocate_carry, Machine.relocate_overflow, branchPC_relocate,
      UInt64.add_assoc, apply_ite]

end VerifiedSqrt.Arm

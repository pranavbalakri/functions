module

public import VerifiedSqrt.Arm.ClassifyState32

@[expose] public section

namespace VerifiedSqrt.Arm

private theorem before_stop (stop : UInt64) (hstop : 32 ≤ stop.toNat)
    (p : Nat) (hp : p < 32) : UInt64.ofNat p ≠ stop := by
  intro h
  have hn := congrArg UInt64.toNat h
  rw [UInt64.toNat_ofNat'] at hn
  change p % 2 ^ 64 = stop.toNat at hn
  omega

theorem input_two (s : Machine) (stop : UInt64) (hstop : 32 ≤ stop.toNat)
    (hpc : s.pc = 0) (hc : supportedControls s.fpcr = true) (fuel : Nat) :
    run sqrt32Code stop (fuel + 2) s = run sqrt32Code stop fuel (input2 s) := by
  have hp1 : (input1 s).pc = 4 := by rw [input1, Machine.advanceW_pc, hpc]; decide +kernel
  have hc1 : supportedControls (input1 s).fpcr = true := by
    rw [input1, Machine.advanceW_fpcr]; exact hc
  calc
    _ = run sqrt32Code stop (fuel + 1) (input1 s) :=
      run_step _ _ _ _ _ 0x1e260000
        (by rw [hpc]; exact before_stop stop hstop 0 (by decide))
        (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel) (step_scalar_to_word s hc)
    _ = _ := run_step _ _ _ _ _ 0x12007801
      (by rw [hp1]; exact before_stop stop hstop 4 (by decide))
      (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel)
      (step_input_magnitude (input1 s) hc1)

theorem input2_pc (s : Machine) (hpc : s.pc = 0) : (input2 s).pc = 8 := by
  rw [input2, Machine.advanceW_pc, input1, Machine.advanceW_pc, hpc]
  decide +kernel

theorem input_zero_run (s : Machine) (hpc : s.pc = 0)
    (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hz : isZero32 (s.readS 0) = true) :
    run sqrt32Code 240 3 s = some {input2 s with pc := 240} := by
  have hp := input2_pc s hpc
  have hf := input2_state s hs
  have hc2 : supportedControls (input2 s).fpcr = true := by rw [hf.fpcr]; exact hc
  have hb : step 0x34000741 (input2 s) = some {input2 s with pc := 240} := by
    rw [step_input_zero _ hc2, input2_zero s hs, hz, hp]
    rfl
  rw [input_two s 240 (by decide) hpc hc 1,
    run_step _ _ 0 _ _ 0x34000741 (by rw [hp]; decide +kernel)
      (by rw [hp]; decide +kernel) (by rw [hp]; decide +kernel) hb]
  exact run_at_stop _ _ _ _ rfl

theorem input_nonzero_step (s : Machine) (hpc : s.pc = 0)
    (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hz : isZero32 (s.readS 0) = false) :
    step 0x34000741 (input2 s) = some (input3 s) := by
  have hc2 : supportedControls (input2 s).fpcr = true := by
    rw [(input2_state s hs).fpcr]; exact hc
  rw [step_input_zero _ hc2, input2_zero s hs, hz, input2_pc s hpc]
  rfl

theorem input_negative_run (s : Machine) (hpc : s.pc = 0)
    (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hz : isZero32 (s.readS 0) = false) (hn : sign32 (s.readS 0) = true) :
    run sqrt32Code 244 4 s = some {input2 s with pc := 244} := by
  have hp := input2_pc s hpc
  have hf := (input2_state s hs).withPC 12
  have hp3 : (input3 s).pc = 12 := rfl
  have hw3 : (input3 s).readW 0 = s.readS 0 := hf.input
  have hc3 : supportedControls (input3 s).fpcr = true := by
    change supportedControls (input2 s).fpcr = true
    rw [(input2_state s hs).fpcr]; exact hc
  have hb : step 0x37f80740 (input3 s) = some {input2 s with pc := 244} := by
    rw [step_input_sign _ hc3, input_sign_test, hw3, hn]
    rfl
  rw [input_two s 244 (by decide) hpc hc 2,
    run_step _ _ 1 _ _ 0x34000741 (by rw [hp]; decide +kernel)
      (by rw [hp]; decide +kernel) (by rw [hp]; decide +kernel)
      (input_nonzero_step s hpc hc hs hz),
    run_step _ _ 0 _ _ 0x37f80740 (by rw [hp3]; decide +kernel) (by rw [hp3]; decide +kernel)
      (by rw [hp3]; decide +kernel) hb]
  exact run_at_stop _ _ _ _ rfl

theorem input_six (s : Machine) (stop : UInt64) (hstop : 32 ≤ stop.toNat)
    (hpc : s.pc = 0) (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hz : isZero32 (s.readS 0) = false) (hn : sign32 (s.readS 0) = false) (fuel : Nat) :
    run sqrt32Code stop (fuel + 6) s = run sqrt32Code stop fuel (input6 s) := by
  have hp2 := input2_pc s hpc
  have hp3 : (input3 s).pc = 12 := rfl
  have hp4 : (input4 s).pc = 16 := rfl
  have hf2 := input2_state s hs
  have hw3 : (input3 s).readW 0 = s.readS 0 := hf2.input
  have hc3 : supportedControls (input3 s).fpcr = true := by
    change supportedControls (input2 s).fpcr = true
    rw [hf2.fpcr]; exact hc
  have hc4 : supportedControls (input4 s).fpcr = true := hc3
  have hc5 : supportedControls (input5 s).fpcr = true := by
    rw [input5, Machine.advanceW_fpcr]; exact hc4
  have hsign : step 0x37f80740 (input3 s) = some (input4 s) := by
    rw [step_input_sign _ hc3, input_sign_test, hw3, hn]
    rfl
  have hpc5 : (input5 s).pc = 20 := by rw [input5, Machine.advanceW_pc]; rfl
  have hcompare : step 0x6b02001f (input5 s) = some (input6 s) := by
    rw [step_input_compare _ hc5, hpc5]
    rfl
  rw [show fuel + 6 = (fuel + 4) + 2 by omega, input_two s stop hstop hpc hc (fuel + 4)]
  calc
    _ = run sqrt32Code stop (fuel + 3) (input3 s) :=
      run_step _ _ _ _ _ 0x34000741
        (by rw [hp2]; exact before_stop stop hstop 8 (by decide))
        (by rw [hp2]; decide +kernel) (by rw [hp2]; decide +kernel)
        (input_nonzero_step s hpc hc hs hz)
    _ = run sqrt32Code stop (fuel + 2) (input4 s) :=
      run_step _ _ _ _ _ 0x37f80740
        (before_stop stop hstop 12 (by decide)) (by rw [hp3]; decide +kernel)
        (by rw [hp3]; decide +kernel) hsign
    _ = run sqrt32Code stop (fuel + 1) (input5 s) :=
      run_step _ _ _ _ _ 0x52aff002
        (before_stop stop hstop 16 (by decide)) (by rw [hp4]; decide +kernel)
        (by rw [hp4]; decide +kernel)
        (step_input_infinity (input4 s) hc4)
    _ = _ := run_step _ _ _ _ _ 0x6b02001f
      (by rw [hpc5]; exact before_stop stop hstop 20 (by decide))
      (by rw [hpc5]; decide +kernel) (by rw [hpc5]; decide +kernel) hcompare

theorem input_infinity_run (s : Machine) (hpc : s.pc = 0)
    (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hx : s.readS 0 = 0x7f800000) :
    run sqrt32Code 240 7 s = some {input6 s with pc := 240} := by
  have hz : isZero32 (s.readS 0) = false := by rw [hx]; decide +kernel
  have hn : sign32 (s.readS 0) = false := by rw [hx]; decide +kernel
  have hc6 : supportedControls (input6 s).fpcr = true := by
    rw [(input6_state s hs).fpcr]; exact hc
  have hz6 : (input6 s).zero = true := by rw [(input6_flags s hs).1, hx]; decide +kernel
  have hp6 : (input6 s).pc = 24 := rfl
  have hbpc : (if (input6 s).zero then branchPC (input6 s).pc 216 else (input6 s).pc + 4) = 240 := by
    rw [hz6, hp6]
    decide +kernel
  have hb : step 0x540006c0 (input6 s) = some {input6 s with pc := 240} := by
    rw [step_input_equal _ hc6, hbpc]
  rw [input_six s 240 (by decide) hpc hc hs hz hn 1,
    run_step _ _ 0 _ _ 0x540006c0 (by rw [hp6]; decide +kernel) (by rw [hp6]; decide +kernel)
      (by rw [hp6]; decide +kernel) hb]
  exact run_at_stop _ _ _ _ rfl

theorem input_unequal_run (s : Machine) (stop : UInt64) (hstop : 32 ≤ stop.toNat)
    (hpc : s.pc = 0) (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hz : isZero32 (s.readS 0) = false) (hn : sign32 (s.readS 0) = false)
    (hne : s.readS 0 ≠ 0x7f800000)
    (htarget : (if s.readS 0 ≥ 0x7f800000 then (244 : UInt64) else 32) = stop) :
    run sqrt32Code stop 8 s = some {input6 s with pc := stop} := by
  have hc6 : supportedControls (input6 s).fpcr = true := by
    rw [(input6_state s hs).fpcr]; exact hc
  have hz6 : (input6 s).zero = false := by rw [(input6_flags s hs).1]; simp [hne]
  have hp6 : (input6 s).pc = 24 := rfl
  have hp7 : ({input6 s with pc := 28} : Machine).pc = 28 := rfl
  have hbpc : (if (input6 s).zero then branchPC (input6 s).pc 216 else (input6 s).pc + 4) = 28 := by
    rw [hz6, hp6]
    decide +kernel
  have hb : step 0x540006c0 (input6 s) = some {input6 s with pc := 28} := by
    rw [step_input_equal _ hc6, hbpc]
  have hc7 : supportedControls ({input6 s with pc := 28} : Machine).fpcr = true := hc6
  have hz7 : ({input6 s with pc := 28} : Machine).zero = false := hz6
  have hh : ({input6 s with pc := 28} : Machine).carry = decide (s.readS 0 ≥ 0x7f800000) :=
    (input6_flags s hs).2
  have hbpc7 : (if ({input6 s with pc := 28} : Machine).carry &&
      !({input6 s with pc := 28} : Machine).zero then
        branchPC ({input6 s with pc := 28} : Machine).pc 216 else
        ({input6 s with pc := 28} : Machine).pc + 4) = stop := by
    rw [hz7, hh, hp7]
    simpa only [Bool.not_false, Bool.and_true, decide_eq_true_eq,
      show branchPC 28 216 = 244 from by decide +kernel,
      show (28 : UInt64) + 4 = 32 from by decide +kernel] using htarget
  have hb7 : step 0x540006c8 {input6 s with pc := 28} = some {input6 s with pc := stop} := by
    rw [step_input_higher _ hc7, hbpc7]
  rw [input_six s stop hstop hpc hc hs hz hn 2,
    run_step _ _ 1 _ _ 0x540006c0 (before_stop stop hstop 24 (by decide))
      (by rw [hp6]; decide +kernel) (by rw [hp6]; decide +kernel) hb,
    run_step _ _ 0 _ _ 0x540006c8 (before_stop stop hstop 28 (by decide))
      (by rw [hp7]; decide +kernel) (by rw [hp7]; decide +kernel) hb7]
  exact run_at_stop _ _ _ _ rfl

end VerifiedSqrt.Arm

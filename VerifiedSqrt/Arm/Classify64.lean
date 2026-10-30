module

public import VerifiedSqrt.Arm.ClassifyState64

@[expose] public section

namespace VerifiedSqrt.Arm

private theorem before_stop (stop : UInt64) (hstop : 32 ≤ stop.toNat)
    (p : Nat) (hp : p < 32) : UInt64.ofNat p ≠ stop := by
  intro h
  have hn := congrArg UInt64.toNat h
  rw [UInt64.toNat_ofNat'] at hn
  change p % 2 ^ 64 = stop.toNat at hn
  omega

theorem input64_two (s : Machine) (stop : UInt64) (hstop : 32 ≤ stop.toNat)
    (hpc : s.pc = 0) (hc : supportedControls s.fpcr = true) (fuel : Nat) :
    run64 sqrt64Code 0 stop (fuel + 2) s = run64 sqrt64Code 0 stop fuel (input64_2 s) := by
  have hp1 : (input64_1 s).pc = 4 := by rw [input64_1, Machine.advanceX_pc, hpc]; decide +kernel
  have hc1 : supportedControls (input64_1 s).fpcr = true := by
    rw [input64_1, Machine.advanceX_fpcr]; exact hc
  calc
    _ = run64 sqrt64Code 0 stop (fuel + 1) (input64_1 s) :=
      run64_step _ _ _ _ _ _ 0x9e660000
        (by rw [hpc]; exact before_stop stop hstop 0 (by decide))
        (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel) (step64_setup_10 s hc)
    _ = _ := run64_step _ _ _ _ _ _ 0x9240f801
      (by rw [hp1]; exact before_stop stop hstop 4 (by decide))
      (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel)
      (step64_input_magnitude (input64_1 s) hc1)

theorem input64_2_pc (s : Machine) (hpc : s.pc = 0) : (input64_2 s).pc = 8 := by
  rw [input64_2, Machine.advanceX_pc, input64_1, Machine.advanceX_pc, hpc]
  decide +kernel

theorem input64_zero_run (s : Machine) (hpc : s.pc = 0)
    (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hz : isZero64 (s.readD 0) = true) :
    run64 sqrt64Code 0 296 3 s = some {input64_2 s with pc := 296} := by
  have hp := input64_2_pc s hpc
  have hf := input64_2_state s hs
  have hc2 : supportedControls (input64_2 s).fpcr = true := by rw [hf.fpcr]; exact hc
  have hb : step64 0xb4000901 (input64_2 s) = some {input64_2 s with pc := 296} := by
    rw [step64_input_zero _ hc2, input64_2_zero s hs, hz, hp]
    rfl
  rw [input64_two s 296 (by decide) hpc hc 1,
    run64_step _ _ _ 0 _ _ 0xb4000901 (by rw [hp]; decide +kernel)
      (by rw [hp]; decide +kernel) (by rw [hp]; decide +kernel) hb]
  exact run64_at_stop _ _ _ _ _ rfl

theorem input64_nonzero_step (s : Machine) (hpc : s.pc = 0)
    (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hz : isZero64 (s.readD 0) = false) :
    step64 0xb4000901 (input64_2 s) = some (input64_3 s) := by
  have hc2 : supportedControls (input64_2 s).fpcr = true := by
    rw [(input64_2_state s hs).fpcr]; exact hc
  rw [step64_input_zero _ hc2, input64_2_zero s hs, hz, input64_2_pc s hpc]
  rfl

theorem input64_negative_run (s : Machine) (hpc : s.pc = 0)
    (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hz : isZero64 (s.readD 0) = false) (hn : sign64 (s.readD 0) = true) :
    run64 sqrt64Code 0 300 4 s = some {input64_2 s with pc := 300} := by
  have hp := input64_2_pc s hpc
  have hf := (input64_2_state s hs).withPC 12
  have hp3 : (input64_3 s).pc = 12 := rfl
  have hw3 : (input64_3 s).readX 0 = s.readD 0 := hf.input
  have hc3 : supportedControls (input64_3 s).fpcr = true := by
    change supportedControls (input64_2 s).fpcr = true
    rw [(input64_2_state s hs).fpcr]; exact hc
  have hb : step64 0xb7f80900 (input64_3 s) = some {input64_2 s with pc := 300} := by
    rw [step64_input_sign _ hc3, input64_sign_test, hw3, hn]
    rfl
  rw [input64_two s 300 (by decide) hpc hc 2,
    run64_step _ _ _ 1 _ _ 0xb4000901 (by rw [hp]; decide +kernel)
      (by rw [hp]; decide +kernel) (by rw [hp]; decide +kernel)
      (input64_nonzero_step s hpc hc hs hz),
    run64_step _ _ _ 0 _ _ 0xb7f80900 (by rw [hp3]; decide +kernel) (by rw [hp3]; decide +kernel)
      (by rw [hp3]; decide +kernel) hb]
  exact run64_at_stop _ _ _ _ _ rfl

theorem input64_six (s : Machine) (stop : UInt64) (hstop : 32 ≤ stop.toNat)
    (hpc : s.pc = 0) (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hz : isZero64 (s.readD 0) = false) (hn : sign64 (s.readD 0) = false) (fuel : Nat) :
    run64 sqrt64Code 0 stop (fuel + 6) s = run64 sqrt64Code 0 stop fuel (input64_6 s) := by
  have hp2 := input64_2_pc s hpc
  have hp3 : (input64_3 s).pc = 12 := rfl
  have hp4 : (input64_4 s).pc = 16 := rfl
  have hf2 := input64_2_state s hs
  have hw3 : (input64_3 s).readX 0 = s.readD 0 := hf2.input
  have hc3 : supportedControls (input64_3 s).fpcr = true := by
    change supportedControls (input64_2 s).fpcr = true
    rw [hf2.fpcr]; exact hc
  have hc4 : supportedControls (input64_4 s).fpcr = true := hc3
  have hc5 : supportedControls (input64_5 s).fpcr = true := by
    rw [input64_5, Machine.advanceX_fpcr]; exact hc4
  have hsign : step64 0xb7f80900 (input64_3 s) = some (input64_4 s) := by
    rw [step64_input_sign _ hc3, input64_sign_test, hw3, hn]
    rfl
  have hpc5 : (input64_5 s).pc = 20 := by rw [input64_5, Machine.advanceX_pc]; rfl
  have hcompare : step64 0xeb02001f (input64_5 s) = some (input64_6 s) := by
    rw [step64_input_compare _ hc5, hpc5]
    rfl
  rw [show fuel + 6 = (fuel + 4) + 2 by omega, input64_two s stop hstop hpc hc (fuel + 4)]
  calc
    _ = run64 sqrt64Code 0 stop (fuel + 3) (input64_3 s) :=
      run64_step _ _ _ _ _ _ 0xb4000901
        (by rw [hp2]; exact before_stop stop hstop 8 (by decide))
        (by rw [hp2]; decide +kernel) (by rw [hp2]; decide +kernel)
        (input64_nonzero_step s hpc hc hs hz)
    _ = run64 sqrt64Code 0 stop (fuel + 2) (input64_4 s) :=
      run64_step _ _ _ _ _ _ 0xb7f80900
        (before_stop stop hstop 12 (by decide)) (by rw [hp3]; decide +kernel)
        (by rw [hp3]; decide +kernel) hsign
    _ = run64 sqrt64Code 0 stop (fuel + 1) (input64_5 s) :=
      run64_step _ _ _ _ _ _ 0xd2effe02
        (before_stop stop hstop 16 (by decide)) (by rw [hp4]; decide +kernel)
        (by rw [hp4]; decide +kernel)
        (step64_input_infinity (input64_4 s) hc4)
    _ = _ := run64_step _ _ _ _ _ _ 0xeb02001f
      (by rw [hpc5]; exact before_stop stop hstop 20 (by decide))
      (by rw [hpc5]; decide +kernel) (by rw [hpc5]; decide +kernel) hcompare

theorem input64_infinity_run (s : Machine) (hpc : s.pc = 0)
    (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hx : s.readD 0 = 0x7ff0000000000000) :
    run64 sqrt64Code 0 296 7 s = some {input64_6 s with pc := 296} := by
  have hz : isZero64 (s.readD 0) = false := by rw [hx]; decide +kernel
  have hn : sign64 (s.readD 0) = false := by rw [hx]; decide +kernel
  have hc6 : supportedControls (input64_6 s).fpcr = true := by
    rw [(input64_6_state s hs).fpcr]; exact hc
  have hz6 : (input64_6 s).zero = true := by rw [(input64_6_flags s hs).1, hx]; decide +kernel
  have hp6 : (input64_6 s).pc = 24 := rfl
  have hbpc : (if (input64_6 s).zero then branchPC (input64_6 s).pc 272 else (input64_6 s).pc + 4) = 296 := by
    rw [hz6, hp6]
    decide +kernel
  have hb : step64 0x54000880 (input64_6 s) = some {input64_6 s with pc := 296} := by
    rw [step64_input_equal _ hc6, hbpc]
  rw [input64_six s 296 (by decide) hpc hc hs hz hn 1,
    run64_step _ _ _ 0 _ _ 0x54000880 (by rw [hp6]; decide +kernel) (by rw [hp6]; decide +kernel)
      (by rw [hp6]; decide +kernel) hb]
  exact run64_at_stop _ _ _ _ _ rfl

theorem input64_unequal_run (s : Machine) (stop : UInt64) (hstop : 32 ≤ stop.toNat)
    (hpc : s.pc = 0) (hc : supportedControls s.fpcr = true) (hs : s.x.size = 32)
    (hz : isZero64 (s.readD 0) = false) (hn : sign64 (s.readD 0) = false)
    (hne : s.readD 0 ≠ 0x7ff0000000000000)
    (htarget : (if s.readD 0 ≥ 0x7ff0000000000000 then (300 : UInt64) else 32) = stop) :
    run64 sqrt64Code 0 stop 8 s = some {input64_6 s with pc := stop} := by
  have hc6 : supportedControls (input64_6 s).fpcr = true := by
    rw [(input64_6_state s hs).fpcr]; exact hc
  have hz6 : (input64_6 s).zero = false := by rw [(input64_6_flags s hs).1]; simp [hne]
  have hp6 : (input64_6 s).pc = 24 := rfl
  have hp7 : ({input64_6 s with pc := 28} : Machine).pc = 28 := rfl
  have hbpc : (if (input64_6 s).zero then branchPC (input64_6 s).pc 272 else (input64_6 s).pc + 4) = 28 := by
    rw [hz6, hp6]
    decide +kernel
  have hb : step64 0x54000880 (input64_6 s) = some {input64_6 s with pc := 28} := by
    rw [step64_input_equal _ hc6, hbpc]
  have hc7 : supportedControls ({input64_6 s with pc := 28} : Machine).fpcr = true := hc6
  have hz7 : ({input64_6 s with pc := 28} : Machine).zero = false := hz6
  have hh : ({input64_6 s with pc := 28} : Machine).carry = decide (s.readD 0 ≥ 0x7ff0000000000000) :=
    (input64_6_flags s hs).2
  have hbpc7 : (if ({input64_6 s with pc := 28} : Machine).carry &&
      !({input64_6 s with pc := 28} : Machine).zero then
        branchPC ({input64_6 s with pc := 28} : Machine).pc 272 else
        ({input64_6 s with pc := 28} : Machine).pc + 4) = stop := by
    rw [hz7, hh, hp7]
    simpa only [Bool.not_false, Bool.and_true, decide_eq_true_eq,
      show branchPC 28 272 = 300 from by decide +kernel,
      show (28 : UInt64) + 4 = 32 from by decide +kernel] using htarget
  have hb7 : step64 0x54000888 {input64_6 s with pc := 28} = some {input64_6 s with pc := stop} := by
    rw [step64_input_higher _ hc7, hbpc7]
  rw [input64_six s stop hstop hpc hc hs hz hn 2,
    run64_step _ _ _ 1 _ _ 0x54000880 (before_stop stop hstop 24 (by decide))
      (by rw [hp6]; decide +kernel) (by rw [hp6]; decide +kernel) hb,
    run64_step _ _ _ 0 _ _ 0x54000888 (before_stop stop hstop 28 (by decide))
      (by rw [hp7]; decide +kernel) (by rw [hp7]; decide +kernel) hb7]
  exact run64_at_stop _ _ _ _ _ rfl

end VerifiedSqrt.Arm

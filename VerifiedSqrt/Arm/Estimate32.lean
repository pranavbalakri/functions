module

public import VerifiedSqrt.Arm.FloatInstructions
public import VerifiedSqrt.Arm.Execution

@[expose] public section

namespace VerifiedSqrt.Arm

theorem estimate_run (s : Machine) (hpc : s.pc = 100)
    (hc : supportedControls s.fpcr = true) :
    ∃ t, run sqrt32Code 148 12 s = some t ∧ t.pc = 148 ∧ FloatFrame s t := by
  obtain ⟨s1, he1, hp1, hf1⟩ := progress_float_half s hc
  have hp1 : s1.pc = 104 := by rw [hp1, hpc]; decide +kernel
  have hc1 : supportedControls s1.fpcr = true := by rw [hf1.fpcr]; exact hc
  obtain ⟨s2, he2, hp2, hf2⟩ := progress_float_estimate s1 hc1
  have hp2 : s2.pc = 108 := by rw [hp2, hp1]; decide +kernel
  have hc2 : supportedControls s2.fpcr = true := by rw [hf2.fpcr]; exact hc1
  obtain ⟨s3, he3, hp3, hf3⟩ := progress_float_product s2 hc2
  have hp3 : s3.pc = 112 := by rw [hp3, hp2]; decide +kernel
  have hc3 : supportedControls s3.fpcr = true := by rw [hf3.fpcr]; exact hc2
  obtain ⟨s4, he4, hp4, hf4⟩ := progress_float_step s3 hc3
  have hp4 : s4.pc = 116 := by rw [hp4, hp3]; decide +kernel
  have hc4 : supportedControls s4.fpcr = true := by rw [hf4.fpcr]; exact hc3
  obtain ⟨s5, he5, hp5, hf5⟩ := progress_float_refine s4 hc4
  have hp5 : s5.pc = 120 := by rw [hp5, hp4]; decide +kernel
  have hc5 : supportedControls s5.fpcr = true := by rw [hf5.fpcr]; exact hc4
  obtain ⟨s6, he6, hp6, hf6⟩ := progress_float_product s5 hc5
  have hp6 : s6.pc = 124 := by rw [hp6, hp5]; decide +kernel
  have hc6 : supportedControls s6.fpcr = true := by rw [hf6.fpcr]; exact hc5
  obtain ⟨s7, he7, hp7, hf7⟩ := progress_float_step s6 hc6
  have hp7 : s7.pc = 128 := by rw [hp7, hp6]; decide +kernel
  have hc7 : supportedControls s7.fpcr = true := by rw [hf7.fpcr]; exact hc6
  obtain ⟨s8, he8, hp8, hf8⟩ := progress_float_refine s7 hc7
  have hp8 : s8.pc = 132 := by rw [hp8, hp7]; decide +kernel
  have hc8 : supportedControls s8.fpcr = true := by rw [hf8.fpcr]; exact hc7
  obtain ⟨s9, he9, hp9, hf9⟩ := progress_float_product s8 hc8
  have hp9 : s9.pc = 136 := by rw [hp9, hp8]; decide +kernel
  have hc9 : supportedControls s9.fpcr = true := by rw [hf9.fpcr]; exact hc8
  obtain ⟨s10, he10, hp10, hf10⟩ := progress_float_half_estimate s9 hc9
  have hp10 : s10.pc = 140 := by rw [hp10, hp9]; decide +kernel
  have hc10 : supportedControls s10.fpcr = true := by rw [hf10.fpcr]; exact hc9
  obtain ⟨s11, he11, hp11, hf11⟩ := progress_float_residual s10 hc10
  have hp11 : s11.pc = 144 := by rw [hp11, hp10]; decide +kernel
  have hc11 : supportedControls s11.fpcr = true := by rw [hf11.fpcr]; exact hc10
  obtain ⟨s12, he12, hp12, hf12⟩ := progress_float_correction s11 hc11
  have hp12 : s12.pc = 148 := by rw [hp12, hp11]; decide +kernel
  refine ⟨s12, ?_, hp12, ?_⟩
  · calc
      run sqrt32Code 148 12 s = run sqrt32Code 148 11 s1 :=
        run_step _ _ _ _ _ 0x1e2c1005
          (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel)
          (by rw [hpc]; decide +kernel) he1
      _ = run sqrt32Code 148 10 s2 :=
        run_step _ _ _ _ _ 0x7ea1d801
          (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel)
          (by rw [hp1]; decide +kernel) he2
      _ = run sqrt32Code 148 9 s3 :=
        run_step _ _ _ _ _ 0x1e210802
          (by rw [hp2]; decide +kernel) (by rw [hp2]; decide +kernel)
          (by rw [hp2]; decide +kernel) he3
      _ = run sqrt32Code 148 8 s4 :=
        run_step _ _ _ _ _ 0x5ea1fc42
          (by rw [hp3]; decide +kernel) (by rw [hp3]; decide +kernel)
          (by rw [hp3]; decide +kernel) he4
      _ = run sqrt32Code 148 7 s5 :=
        run_step _ _ _ _ _ 0x1e220821
          (by rw [hp4]; decide +kernel) (by rw [hp4]; decide +kernel)
          (by rw [hp4]; decide +kernel) he5
      _ = run sqrt32Code 148 6 s6 :=
        run_step _ _ _ _ _ 0x1e210802
          (by rw [hp5]; decide +kernel) (by rw [hp5]; decide +kernel)
          (by rw [hp5]; decide +kernel) he6
      _ = run sqrt32Code 148 5 s7 :=
        run_step _ _ _ _ _ 0x5ea1fc42
          (by rw [hp6]; decide +kernel) (by rw [hp6]; decide +kernel)
          (by rw [hp6]; decide +kernel) he7
      _ = run sqrt32Code 148 4 s8 :=
        run_step _ _ _ _ _ 0x1e220821
          (by rw [hp7]; decide +kernel) (by rw [hp7]; decide +kernel)
          (by rw [hp7]; decide +kernel) he8
      _ = run sqrt32Code 148 3 s9 :=
        run_step _ _ _ _ _ 0x1e210802
          (by rw [hp8]; decide +kernel) (by rw [hp8]; decide +kernel)
          (by rw [hp8]; decide +kernel) he9
      _ = run sqrt32Code 148 2 s10 :=
        run_step _ _ _ _ _ 0x1e250823
          (by rw [hp9]; decide +kernel) (by rw [hp9]; decide +kernel)
          (by rw [hp9]; decide +kernel) he10
      _ = run sqrt32Code 148 1 s11 :=
        run_step _ _ _ _ _ 0x1f028044
          (by rw [hp10]; decide +kernel) (by rw [hp10]; decide +kernel)
          (by rw [hp10]; decide +kernel) he11
      _ = run sqrt32Code 148 0 s12 :=
        run_step _ _ _ _ _ 0x1f030880
          (by rw [hp11]; decide +kernel) (by rw [hp11]; decide +kernel)
          (by rw [hp11]; decide +kernel) he12
      _ = some s12 := run_at_stop _ _ _ _ hp12
  · exact hf1.trans (hf2.trans (hf3.trans (hf4.trans (hf5.trans (hf6.trans (hf7.trans (hf8.trans (hf9.trans (hf10.trans (hf11.trans (hf12)))))))))))

end VerifiedSqrt.Arm

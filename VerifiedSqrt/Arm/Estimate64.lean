module

public import VerifiedSqrt.Arm.FloatInstructions64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem estimate64_trace (s : Machine) (hpc : s.pc = 100)
    (hc : supportedControls s.fpcr = true) :
    ∃ t, Steps64 sqrt64Code 0 15 s t ∧ t.pc = 160 ∧ FloatFrame s t := by
  obtain ⟨s1, he1, hp1, hf1⟩ := progress64_float_half s hc
  have hp1 : s1.pc = 104 := by rw [hp1, hpc]; decide +kernel
  have hc1 : supportedControls s1.fpcr = true := by rw [hf1.fpcr]; exact hc
  have ht1 : Steps64 sqrt64Code 0 1 s s1 := Steps64.single
    (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel) he1
  obtain ⟨s2, he2, hp2, hf2⟩ := progress64_float_estimate s1 hc1
  have hp2 : s2.pc = 108 := by rw [hp2, hp1]; decide +kernel
  have hc2 : supportedControls s2.fpcr = true := by rw [hf2.fpcr]; exact hc1
  have ht2 : Steps64 sqrt64Code 0 1 s1 s2 := Steps64.single
    (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel) he2
  obtain ⟨s3, he3, hp3, hf3⟩ := progress64_float_product s2 hc2
  have hp3 : s3.pc = 112 := by rw [hp3, hp2]; decide +kernel
  have hc3 : supportedControls s3.fpcr = true := by rw [hf3.fpcr]; exact hc2
  have ht3 : Steps64 sqrt64Code 0 1 s2 s3 := Steps64.single
    (by rw [hp2]; decide +kernel) (by rw [hp2]; decide +kernel) he3
  obtain ⟨s4, he4, hp4, hf4⟩ := progress64_float_step s3 hc3
  have hp4 : s4.pc = 116 := by rw [hp4, hp3]; decide +kernel
  have hc4 : supportedControls s4.fpcr = true := by rw [hf4.fpcr]; exact hc3
  have ht4 : Steps64 sqrt64Code 0 1 s3 s4 := Steps64.single
    (by rw [hp3]; decide +kernel) (by rw [hp3]; decide +kernel) he4
  obtain ⟨s5, he5, hp5, hf5⟩ := progress64_float_refine s4 hc4
  have hp5 : s5.pc = 120 := by rw [hp5, hp4]; decide +kernel
  have hc5 : supportedControls s5.fpcr = true := by rw [hf5.fpcr]; exact hc4
  have ht5 : Steps64 sqrt64Code 0 1 s4 s5 := Steps64.single
    (by rw [hp4]; decide +kernel) (by rw [hp4]; decide +kernel) he5
  obtain ⟨s6, he6, hp6, hf6⟩ := progress64_float_product s5 hc5
  have hp6 : s6.pc = 124 := by rw [hp6, hp5]; decide +kernel
  have hc6 : supportedControls s6.fpcr = true := by rw [hf6.fpcr]; exact hc5
  have ht6 : Steps64 sqrt64Code 0 1 s5 s6 := Steps64.single
    (by rw [hp5]; decide +kernel) (by rw [hp5]; decide +kernel) he6
  obtain ⟨s7, he7, hp7, hf7⟩ := progress64_float_step s6 hc6
  have hp7 : s7.pc = 128 := by rw [hp7, hp6]; decide +kernel
  have hc7 : supportedControls s7.fpcr = true := by rw [hf7.fpcr]; exact hc6
  have ht7 : Steps64 sqrt64Code 0 1 s6 s7 := Steps64.single
    (by rw [hp6]; decide +kernel) (by rw [hp6]; decide +kernel) he7
  obtain ⟨s8, he8, hp8, hf8⟩ := progress64_float_refine s7 hc7
  have hp8 : s8.pc = 132 := by rw [hp8, hp7]; decide +kernel
  have hc8 : supportedControls s8.fpcr = true := by rw [hf8.fpcr]; exact hc7
  have ht8 : Steps64 sqrt64Code 0 1 s7 s8 := Steps64.single
    (by rw [hp7]; decide +kernel) (by rw [hp7]; decide +kernel) he8
  obtain ⟨s9, he9, hp9, hf9⟩ := progress64_float_product s8 hc8
  have hp9 : s9.pc = 136 := by rw [hp9, hp8]; decide +kernel
  have hc9 : supportedControls s9.fpcr = true := by rw [hf9.fpcr]; exact hc8
  have ht9 : Steps64 sqrt64Code 0 1 s8 s9 := Steps64.single
    (by rw [hp8]; decide +kernel) (by rw [hp8]; decide +kernel) he9
  obtain ⟨s10, he10, hp10, hf10⟩ := progress64_float_step s9 hc9
  have hp10 : s10.pc = 140 := by rw [hp10, hp9]; decide +kernel
  have hc10 : supportedControls s10.fpcr = true := by rw [hf10.fpcr]; exact hc9
  have ht10 : Steps64 sqrt64Code 0 1 s9 s10 := Steps64.single
    (by rw [hp9]; decide +kernel) (by rw [hp9]; decide +kernel) he10
  obtain ⟨s11, he11, hp11, hf11⟩ := progress64_float_refine s10 hc10
  have hp11 : s11.pc = 144 := by rw [hp11, hp10]; decide +kernel
  have hc11 : supportedControls s11.fpcr = true := by rw [hf11.fpcr]; exact hc10
  have ht11 : Steps64 sqrt64Code 0 1 s10 s11 := Steps64.single
    (by rw [hp10]; decide +kernel) (by rw [hp10]; decide +kernel) he11
  obtain ⟨s12, he12, hp12, hf12⟩ := progress64_float_product s11 hc11
  have hp12 : s12.pc = 148 := by rw [hp12, hp11]; decide +kernel
  have hc12 : supportedControls s12.fpcr = true := by rw [hf12.fpcr]; exact hc11
  have ht12 : Steps64 sqrt64Code 0 1 s11 s12 := Steps64.single
    (by rw [hp11]; decide +kernel) (by rw [hp11]; decide +kernel) he12
  obtain ⟨s13, he13, hp13, hf13⟩ := progress64_float_half_estimate s12 hc12
  have hp13 : s13.pc = 152 := by rw [hp13, hp12]; decide +kernel
  have hc13 : supportedControls s13.fpcr = true := by rw [hf13.fpcr]; exact hc12
  have ht13 : Steps64 sqrt64Code 0 1 s12 s13 := Steps64.single
    (by rw [hp12]; decide +kernel) (by rw [hp12]; decide +kernel) he13
  obtain ⟨s14, he14, hp14, hf14⟩ := progress64_float_residual s13 hc13
  have hp14 : s14.pc = 156 := by rw [hp14, hp13]; decide +kernel
  have hc14 : supportedControls s14.fpcr = true := by rw [hf14.fpcr]; exact hc13
  have ht14 : Steps64 sqrt64Code 0 1 s13 s14 := Steps64.single
    (by rw [hp13]; decide +kernel) (by rw [hp13]; decide +kernel) he14
  obtain ⟨s15, he15, hp15, hf15⟩ := progress64_float_correction s14 hc14
  have hp15 : s15.pc = 160 := by rw [hp15, hp14]; decide +kernel
  have ht15 : Steps64 sqrt64Code 0 1 s14 s15 := Steps64.single
    (by rw [hp14]; decide +kernel) (by rw [hp14]; decide +kernel) he15
  exact ⟨s15, ht1.trans (ht2.trans (ht3.trans (ht4.trans (ht5.trans (ht6.trans (ht7.trans (ht8.trans (ht9.trans (ht10.trans (ht11.trans (ht12.trans (ht13.trans (ht14.trans (ht15)))))))))))))), hp15, hf1.trans (hf2.trans (hf3.trans (hf4.trans (hf5.trans (hf6.trans (hf7.trans (hf8.trans (hf9.trans (hf10.trans (hf11.trans (hf12.trans (hf13.trans (hf14.trans (hf15))))))))))))))⟩

end VerifiedSqrt.Arm

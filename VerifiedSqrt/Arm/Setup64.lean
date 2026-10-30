module

public import VerifiedSqrt.Arm.InstructionProof64
public import VerifiedSqrt.Arm.Registers64
public import VerifiedSqrt.Arm.WideArithmetic
public import VerifiedSqrt.Sqrt.Correction64

@[expose] public section

namespace VerifiedSqrt.Arm

private theorem shiftZero64 (w : UInt64) : UInt64.shiftLeft w ⟨0#64⟩ = w := UInt64.shiftLeft_zero
private theorem shiftZero32 (w : UInt32) : UInt32.shiftLeft w ⟨0#32⟩ = w := UInt32.shiftLeft_zero

attribute [local cbv_opaque] Machine.readW Machine.writeW Machine.readX Machine.writeX
  Machine.readD Machine.writeD supportedControls UInt32.add UInt32.sub UInt32.shiftLeft
  UInt64.add UInt64.sub UInt64.shiftLeft UInt64.shiftRight UInt32.toUInt64

def setup64_1 (s : Machine) : Machine :=
  s.advanceX 2 (UInt64.ofNat ((s.readX 0).toNat / 2 ^ 52 % 2048))

theorem step64_setup_1 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xd374f802 s = some (s.advanceX 2 (UInt64.ofNat ((s.readX 0).toNat / 2 ^ 52 % 2048))) := by
  unfold step64 step
  rw [hc]
  cbv

def setup64_2 (s : Machine) : Machine :=
  let s := setup64_1 s
  s.advanceW 2 (s.readW 2 - 969)

theorem step64_setup_2 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x510f2442 s = some (s.advanceW 2 (s.readW 2 - 969)) := by
  unfold step64 step
  rw [hc]
  cbv

def setup64_3 (s : Machine) : Machine :=
  let s := setup64_2 s
  s.advanceX 3 (s.readX 0 &&& 0xfffffffffffff)

theorem step64_setup_3 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x9240cc03 s = some (s.advanceX 3 (s.readX 0 &&& 0xfffffffffffff)) := by
  unfold step64 step
  rw [hc]
  cbv

def setup64_4 (s : Machine) : Machine :=
  let s := setup64_3 s
  s.advanceX 1 (0x10000000000000)

theorem step64_setup_4 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xd2e00201 s = some (s.advanceX 1 (0x10000000000000)) := by
  unfold step64 step
  rw [hc]
  cbv

def setup64_5 (s : Machine) : Machine :=
  let s := setup64_4 s
  s.advanceX 3 (s.readX 3 + s.readX 1)

theorem step64_setup_5 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x8b010063 s = some (s.advanceX 3 (s.readX 3 + s.readX 1)) := by
  unfold step64 step
  rw [hc]
  cbv
  simp only [shiftZero64]

def setup64_6 (s : Machine) : Machine :=
  let s := setup64_5 s
  s.advanceW 6 (64)

theorem step64_setup_6 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x52800806 s = some (s.advanceW 6 (64)) := by
  unfold step64 step
  rw [hc]
  cbv

def setup64_7 (s : Machine) : Machine :=
  let s := setup64_6 s
  s.advanceW 6 (s.readW 6 - s.readW 2)

theorem step64_setup_7 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x4b0200c6 s = some (s.advanceW 6 (s.readW 6 - s.readW 2)) := by
  unfold step64 step
  rw [hc]
  cbv
  simp only [shiftZero32]

def setup64_8 (s : Machine) : Machine :=
  let s := setup64_7 s
  s.advanceX 5 (s.readX 3 >>> (s.readX 6 &&& 63))

theorem step64_setup_8 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x9ac62465 s = some (s.advanceX 5 (s.readX 3 >>> (s.readX 6 &&& 63))) := by
  unfold step64 step
  rw [hc]
  cbv

def setup64_9 (s : Machine) : Machine :=
  let s := setup64_8 s
  s.advanceX 3 (s.readX 3 <<< (s.readX 2 &&& 63))

theorem step64_setup_9 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x9ac22063 s = some (s.advanceX 3 (s.readX 3 <<< (s.readX 2 &&& 63))) := by
  unfold step64 step
  rw [hc]
  cbv

def setup64_10 (s : Machine) : Machine :=
  let s := setup64_9 s
  s.advanceX 0 (s.readD 0)

theorem step64_setup_10 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x9e660000 s = some (s.advanceX 0 (s.readD 0)) := by
  unfold step64 step
  rw [hc]
  cbv

def setup64_11 (s : Machine) : Machine :=
  let s := setup64_10 s
  s.advanceX 0 (s.readX 0 &&& 0xfffffffffffff)

theorem step64_setup_11 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x9240cc00 s = some (s.advanceX 0 (s.readX 0 &&& 0xfffffffffffff)) := by
  unfold step64 step
  rw [hc]
  cbv

def setup64_12 (s : Machine) : Machine :=
  let s := setup64_11 s
  s.advanceX 0 (s.readX 0 + s.readX 1)

theorem step64_setup_12 (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x8b010000 s = some (s.advanceX 0 (s.readX 0 + s.readX 1)) := by
  unfold step64 step
  rw [hc]
  cbv
  simp only [shiftZero64]

theorem setup64_trace (s : Machine) (hpc : s.pc = 160)
    (hc : supportedControls s.fpcr = true) :
    Steps64 sqrt64Code 0 12 s (setup64_12 s) := by
  have hp1 : (setup64_1 s).pc = 164 := by
    rw [setup64_1, Machine.advanceX_pc, hpc]
    decide +kernel
  have hc1 : supportedControls (setup64_1 s).fpcr = true := by
    rw [setup64_1, Machine.advanceX_fpcr]
    exact hc
  have ht1 : Steps64 sqrt64Code 0 1 s (setup64_1 s) := Steps64.single
    (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel) (step64_setup_1 s hc)
  have hp2 : (setup64_2 s).pc = 168 := by
    rw [setup64_2, Machine.advanceW_pc, hp1]
    decide +kernel
  have hc2 : supportedControls (setup64_2 s).fpcr = true := by
    rw [setup64_2, Machine.advanceW_fpcr]
    exact hc1
  have ht2 : Steps64 sqrt64Code 0 1 (setup64_1 s) (setup64_2 s) := Steps64.single
    (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel) (step64_setup_2 (setup64_1 s) hc1)
  have hp3 : (setup64_3 s).pc = 172 := by
    rw [setup64_3, Machine.advanceX_pc, hp2]
    decide +kernel
  have hc3 : supportedControls (setup64_3 s).fpcr = true := by
    rw [setup64_3, Machine.advanceX_fpcr]
    exact hc2
  have ht3 : Steps64 sqrt64Code 0 1 (setup64_2 s) (setup64_3 s) := Steps64.single
    (by rw [hp2]; decide +kernel) (by rw [hp2]; decide +kernel) (step64_setup_3 (setup64_2 s) hc2)
  have hp4 : (setup64_4 s).pc = 176 := by
    rw [setup64_4, Machine.advanceX_pc, hp3]
    decide +kernel
  have hc4 : supportedControls (setup64_4 s).fpcr = true := by
    rw [setup64_4, Machine.advanceX_fpcr]
    exact hc3
  have ht4 : Steps64 sqrt64Code 0 1 (setup64_3 s) (setup64_4 s) := Steps64.single
    (by rw [hp3]; decide +kernel) (by rw [hp3]; decide +kernel) (step64_setup_4 (setup64_3 s) hc3)
  have hp5 : (setup64_5 s).pc = 180 := by
    rw [setup64_5, Machine.advanceX_pc, hp4]
    decide +kernel
  have hc5 : supportedControls (setup64_5 s).fpcr = true := by
    rw [setup64_5, Machine.advanceX_fpcr]
    exact hc4
  have ht5 : Steps64 sqrt64Code 0 1 (setup64_4 s) (setup64_5 s) := Steps64.single
    (by rw [hp4]; decide +kernel) (by rw [hp4]; decide +kernel) (step64_setup_5 (setup64_4 s) hc4)
  have hp6 : (setup64_6 s).pc = 184 := by
    rw [setup64_6, Machine.advanceW_pc, hp5]
    decide +kernel
  have hc6 : supportedControls (setup64_6 s).fpcr = true := by
    rw [setup64_6, Machine.advanceW_fpcr]
    exact hc5
  have ht6 : Steps64 sqrt64Code 0 1 (setup64_5 s) (setup64_6 s) := Steps64.single
    (by rw [hp5]; decide +kernel) (by rw [hp5]; decide +kernel) (step64_setup_6 (setup64_5 s) hc5)
  have hp7 : (setup64_7 s).pc = 188 := by
    rw [setup64_7, Machine.advanceW_pc, hp6]
    decide +kernel
  have hc7 : supportedControls (setup64_7 s).fpcr = true := by
    rw [setup64_7, Machine.advanceW_fpcr]
    exact hc6
  have ht7 : Steps64 sqrt64Code 0 1 (setup64_6 s) (setup64_7 s) := Steps64.single
    (by rw [hp6]; decide +kernel) (by rw [hp6]; decide +kernel) (step64_setup_7 (setup64_6 s) hc6)
  have hp8 : (setup64_8 s).pc = 192 := by
    rw [setup64_8, Machine.advanceX_pc, hp7]
    decide +kernel
  have hc8 : supportedControls (setup64_8 s).fpcr = true := by
    rw [setup64_8, Machine.advanceX_fpcr]
    exact hc7
  have ht8 : Steps64 sqrt64Code 0 1 (setup64_7 s) (setup64_8 s) := Steps64.single
    (by rw [hp7]; decide +kernel) (by rw [hp7]; decide +kernel) (step64_setup_8 (setup64_7 s) hc7)
  have hp9 : (setup64_9 s).pc = 196 := by
    rw [setup64_9, Machine.advanceX_pc, hp8]
    decide +kernel
  have hc9 : supportedControls (setup64_9 s).fpcr = true := by
    rw [setup64_9, Machine.advanceX_fpcr]
    exact hc8
  have ht9 : Steps64 sqrt64Code 0 1 (setup64_8 s) (setup64_9 s) := Steps64.single
    (by rw [hp8]; decide +kernel) (by rw [hp8]; decide +kernel) (step64_setup_9 (setup64_8 s) hc8)
  have hp10 : (setup64_10 s).pc = 200 := by
    rw [setup64_10, Machine.advanceX_pc, hp9]
    decide +kernel
  have hc10 : supportedControls (setup64_10 s).fpcr = true := by
    rw [setup64_10, Machine.advanceX_fpcr]
    exact hc9
  have ht10 : Steps64 sqrt64Code 0 1 (setup64_9 s) (setup64_10 s) := Steps64.single
    (by rw [hp9]; decide +kernel) (by rw [hp9]; decide +kernel) (step64_setup_10 (setup64_9 s) hc9)
  have hp11 : (setup64_11 s).pc = 204 := by
    rw [setup64_11, Machine.advanceX_pc, hp10]
    decide +kernel
  have hc11 : supportedControls (setup64_11 s).fpcr = true := by
    rw [setup64_11, Machine.advanceX_fpcr]
    exact hc10
  have ht11 : Steps64 sqrt64Code 0 1 (setup64_10 s) (setup64_11 s) := Steps64.single
    (by rw [hp10]; decide +kernel) (by rw [hp10]; decide +kernel) (step64_setup_11 (setup64_10 s) hc10)
  have hp12 : (setup64_12 s).pc = 208 := by
    rw [setup64_12, Machine.advanceX_pc, hp11]
    decide +kernel
  have ht12 : Steps64 sqrt64Code 0 1 (setup64_11 s) (setup64_12 s) := Steps64.single
    (by rw [hp11]; decide +kernel) (by rw [hp11]; decide +kernel) (step64_setup_12 (setup64_11 s) hc11)
  exact ht1.trans (ht2.trans (ht3.trans (ht4.trans (ht5.trans (ht6.trans (ht7.trans (ht8.trans (ht9.trans (ht10.trans (ht11.trans (ht12)))))))))))

attribute [local simp] Machine.advanceW_size Machine.advanceX_size
  Machine.readW_advanceW_same Machine.readW_advanceW_ne Machine.readX_advanceW_same
  Machine.readX_advanceW_ne Machine.readX_advanceX_same Machine.readX_advanceX_ne
  Machine.readW_advanceX_ne Machine.readD_advanceW Machine.readD_advanceX

theorem setup64_seed (s : Machine) (hs : s.x.size = 32) :
    (setup64_12 s).readX 0 = (s.readD 0 &&& 0xfffffffffffff) + (0x10000000000000 : UInt64) := by
  simp [setup64_12, setup64_11, setup64_10, setup64_9, setup64_8, setup64_7, setup64_6, setup64_5, setup64_4, setup64_3, setup64_2, setup64_1, hs]

theorem setup64_radicand (s : Machine) (hs : s.x.size = 32) :
    (setup64_12 s).readX 5 =
      ((s.readX 0 &&& 0xfffffffffffff) + (0x10000000000000 : UInt64)) >>>
        ((64 - ((UInt64.ofNat ((s.readX 0).toNat / 2 ^ 52 % 2048)).toUInt32 - 969)).toUInt64 &&& 63) ∧
    (setup64_12 s).readX 3 =
      ((s.readX 0 &&& 0xfffffffffffff) + (0x10000000000000 : UInt64)) <<<
        (((UInt64.ofNat ((s.readX 0).toNat / 2 ^ 52 % 2048)).toUInt32 - 969).toUInt64 &&& 63) := by
  constructor <;> simp [setup64_12, setup64_11, setup64_10, setup64_9, setup64_8, setup64_7, setup64_6, setup64_5, setup64_4, setup64_3, setup64_2, setup64_1, hs, Machine.readW_advanceX_same]

theorem masked_significand64_nat (w : UInt64) :
    ((w &&& 0xfffffffffffff) + (0x10000000000000 : UInt64)).toNat = fraction64 w + 2 ^ 52 := by
  have hf := fraction64_lt w
  rw [UInt64.toNat_add, show (w &&& 0xfffffffffffff).toNat = fraction64 w from rfl,
    show (0x10000000000000 : UInt64).toNat = 2 ^ 52 from rfl]
  omega

theorem setup64_seed_bounds (s : Machine) (hs : s.x.size = 32) :
    2 ^ 52 ≤ ((setup64_12 s).readX 0).toNat ∧ ((setup64_12 s).readX 0).toNat ≤ 2 ^ 53 := by
  have hf := fraction64_lt (s.readD 0)
  rw [setup64_seed s hs, masked_significand64_nat]
  omega

theorem setup64_radicand_value (s : Machine) (hs : s.x.size = 32)
    (lo : 0x3ff0000000000000 ≤ (s.readX 0).toNat) (hi : (s.readX 0).toNat < 0x4010000000000000) :
    wideValue ((setup64_12 s).readX 5) ((setup64_12 s).readX 3) =
      4 * Sqrt.normalizedRadicand64 (s.readX 0) := by
  have hf := fraction64_lt (s.readX 0)
  have hm := masked_significand64_nat (s.readX 0)
  obtain ⟨hh, hl⟩ := setup64_radicand s hs
  rw [hh, hl, ← exponent64_eq_div]
  rcases Sqrt.normalized64_exponent (s.readX 0) lo hi with he | he
  · rw [he]
    have hshift : ((UInt64.ofNat 1023).toUInt32 - 969).toUInt64 &&& 63 = 54 := by decide +kernel
    have hhigh : (64 - ((UInt64.ofNat 1023).toUInt32 - 969)).toUInt64 &&& 63 = 10 := by decide +kernel
    rw [hshift, hhigh, wideValue, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, hm]
    change ((fraction64 (s.readX 0) + 2 ^ 52) >>> 10) * 2 ^ 64 +
      ((fraction64 (s.readX 0) + 2 ^ 52) <<< 54) % 2 ^ 64 = _
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    norm_num [Sqrt.normalizedRadicand64, he]
    omega
  · rw [he]
    have hshift : ((UInt64.ofNat 1024).toUInt32 - 969).toUInt64 &&& 63 = 55 := by decide +kernel
    have hhigh : (64 - ((UInt64.ofNat 1024).toUInt32 - 969)).toUInt64 &&& 63 = 9 := by decide +kernel
    rw [hshift, hhigh, wideValue, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, hm]
    change ((fraction64 (s.readX 0) + 2 ^ 52) >>> 9) * 2 ^ 64 +
      ((fraction64 (s.readX 0) + 2 ^ 52) <<< 55) % 2 ^ 64 = _
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    norm_num [Sqrt.normalizedRadicand64, he]
    omega

theorem setup64_properties (s : Machine) : IntegerFrame [0, 1, 2, 3, 5, 6] s (setup64_12 s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [setup64_12, setup64_11, setup64_10, setup64_9, setup64_8, setup64_7, setup64_6, setup64_5, setup64_4, setup64_3, setup64_2, setup64_1, Machine.advanceW_fpcr, Machine.advanceX_fpcr]
  · simp only [setup64_12, setup64_11, setup64_10, setup64_9, setup64_8, setup64_7, setup64_6, setup64_5, setup64_4, setup64_3, setup64_2, setup64_1, Machine.advanceW_fpsr, Machine.advanceX_fpsr]
  · simp only [setup64_12, setup64_11, setup64_10, setup64_9, setup64_8, setup64_7, setup64_6, setup64_5, setup64_4, setup64_3, setup64_2, setup64_1, Machine.advanceW_vectors, Machine.advanceX_vectors]
  · simp [setup64_12, setup64_11, setup64_10, setup64_9, setup64_8, setup64_7, setup64_6, setup64_5, setup64_4, setup64_3, setup64_2, setup64_1]
  · intro r hr hn
    have h0 : 0 ≠ r := by simp at hn; omega
    have h1 : 1 ≠ r := by simp at hn; omega
    have h2 : 2 ≠ r := by simp at hn; omega
    have h3 : 3 ≠ r := by simp at hn; omega
    have h5 : 5 ≠ r := by simp at hn; omega
    have h6 : 6 ≠ r := by simp at hn; omega
    simp [setup64_12, setup64_11, setup64_10, setup64_9, setup64_8, setup64_7, setup64_6, setup64_5, setup64_4, setup64_3, setup64_2, setup64_1, hr, h0, h1, h2, h3, h5, h6]

end VerifiedSqrt.Arm

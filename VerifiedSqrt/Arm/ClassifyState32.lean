module

public import VerifiedSqrt.Arm.InputInstructions
public import VerifiedSqrt.Arm.Classification32
public import VerifiedSqrt.Arm.Execution

@[expose] public section

namespace VerifiedSqrt.Arm

def input1 (s : Machine) : Machine := s.advanceW 0 (s.readS 0)

def input2 (s : Machine) : Machine :=
  let s := input1 s
  s.advanceW 1 (s.readW 0 &&& 0x7fffffff)

def input3 (s : Machine) : Machine := {input2 s with pc := 12}

def input4 (s : Machine) : Machine := {input2 s with pc := 16}

def input5 (s : Machine) : Machine := (input4 s).advanceW 2 0x7f800000

def input6 (s : Machine) : Machine :=
  let s := input5 s
  {s with
    pc := 24
    negative := sign32 (s.readW 0 - s.readW 2)
    zero := s.readW 0 - s.readW 2 == 0
    carry := s.readW 0 ≥ s.readW 2
    overflow := (sign32 (s.readW 0) != sign32 (s.readW 2)) &&
      (sign32 (s.readW 0 - s.readW 2) != sign32 (s.readW 0))}

structure InputState (s t : Machine) : Prop where
  input : t.readW 0 = s.readS 0
  fpcr : t.fpcr = s.fpcr
  fpsr : t.fpsr = s.fpsr
  vectors : t.v = s.v
  size : t.x.size = s.x.size
  registers : ∀ r, 3 ≤ r → r < 31 → t.readX r = s.readX r

theorem InputState.withPC {s t : Machine} (h : InputState s t) (pc : UInt64) :
    InputState s {t with pc := pc} :=
  ⟨h.input, h.fpcr, h.fpsr, h.vectors, h.size, h.registers⟩

theorem InputState.wellFormed {s t : Machine} (h : InputState s t) (hs : s.WellFormed) :
    t.WellFormed := ⟨h.size.trans hs.1, by rw [h.vectors]; exact hs.2⟩

theorem InputState.scalar {s t : Machine} (h : InputState s t) : t.readS 0 = s.readS 0 := by
  simp only [Machine.readS, h.vectors]

attribute [local simp] Machine.readW_advanceW_same Machine.readW_advanceW_ne
  Machine.readX_advanceW_ne Machine.advanceW_size Machine.advanceW_fpcr
  Machine.advanceW_fpsr Machine.advanceW_vectors

theorem input2_state (s : Machine) (hs : s.x.size = 32) : InputState s (input2 s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [input2, input1, hs]
  · simp [input2, input1]
  · simp [input2, input1]
  · simp [input2, input1]
  · simp [input2, input1]
  · intro r hr hr'
    have h0 : 0 ≠ r := by omega
    have h1 : 1 ≠ r := by omega
    simp [input2, input1, hr', h0, h1]

theorem input6_state (s : Machine) (hs : s.x.size = 32) : InputState s (input6 s) := by
  have h := input2_state s hs
  have hx : (input4 s).readW 0 = s.readS 0 := h.input
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (input5 s).readW 0 = _
    rw [input5, Machine.readW_advanceW_ne _ 2 0 (by decide) (by decide) (by decide)]
    exact hx
  · change (input5 s).fpcr = _
    rw [input5, Machine.advanceW_fpcr]
    exact h.fpcr
  · change (input5 s).fpsr = _
    rw [input5, Machine.advanceW_fpsr]
    exact h.fpsr
  · change (input5 s).v = _
    rw [input5, Machine.advanceW_vectors]
    exact h.vectors
  · change (input5 s).x.size = _
    rw [input5, Machine.advanceW_size]
    exact h.size
  · intro r hr hr'
    change (input5 s).readX r = _
    rw [input5, Machine.readX_advanceW_ne _ 2 r (by decide) hr' (by omega)]
    exact h.registers r hr hr'

theorem input2_zero (s : Machine) (hs : s.x.size = 32) :
    ((input2 s).readW 1 == 0) = isZero32 (s.readS 0) := by
  simp [input2, input1, hs, isZero32]

theorem input_sign_test (w : UInt32) : ((w >>> 31) &&& 1 != 0) = sign32 w := by
  have hm : (w >>> 31) &&& (1 : UInt32) = w >>> 31 := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_and]
    change (w >>> 31).toNat &&& (2 ^ 1 - 1) = (w >>> 31).toNat
    rw [Nat.and_two_pow_sub_one_eq_mod, UInt32.toNat_shiftRight]
    change (w.toNat >>> 31) % 2 = w.toNat >>> 31
    rw [Nat.shiftRight_eq_div_pow]
    have hb := w.toNat_lt
    omega
  rw [hm]
  by_cases h : w.toNat < 2 ^ 31
  · rw [sign32_false_of_lt w h]
    have hz : w >>> 31 = 0 := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_shiftRight]
      change w.toNat >>> 31 = 0
      rw [Nat.shiftRight_eq_div_pow]
      omega
    simp [hz]
  · rw [sign32_true_of_ge w (by omega)]
    simp only [bne_iff_ne]
    intro hz
    have hn := congrArg UInt32.toNat hz
    rw [UInt32.toNat_shiftRight] at hn
    change w.toNat >>> 31 = 0 at hn
    rw [Nat.shiftRight_eq_div_pow] at hn
    omega

theorem input6_flags (s : Machine) (hs : s.x.size = 32) :
    (input6 s).zero = (s.readS 0 == 0x7f800000) ∧
      (input6 s).carry = decide (s.readS 0 ≥ 0x7f800000) := by
  have h0 : (input5 s).readW 0 = s.readS 0 := by
    change (input6 s).readW 0 = _
    exact (input6_state s hs).input
  have h2 : (input5 s).readW 2 = 0x7f800000 := by
    simp [input5, input4, input2, input1, hs]
  change ((input5 s).readW 0 - (input5 s).readW 2 == 0) = _ ∧
    decide ((input5 s).readW 0 ≥ (input5 s).readW 2) = _
  rw [h0, h2]
  refine ⟨?_, rfl⟩
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, UInt32.sub_eq_iff_eq_add, UInt32.zero_add]

end VerifiedSqrt.Arm

module

public import VerifiedSqrt.Arm.InputInstructions64
public import VerifiedSqrt.Arm.Classification64
public import VerifiedSqrt.Arm.Execution64

@[expose] public section

namespace VerifiedSqrt.Arm

def input64_1 (s : Machine) : Machine := s.advanceX 0 (s.readD 0)

def input64_2 (s : Machine) : Machine :=
  let s := input64_1 s
  s.advanceX 1 (s.readX 0 &&& 0x7fffffffffffffff)

def input64_3 (s : Machine) : Machine := {input64_2 s with pc := 12}

def input64_4 (s : Machine) : Machine := {input64_2 s with pc := 16}

def input64_5 (s : Machine) : Machine := (input64_4 s).advanceX 2 0x7ff0000000000000

def input64_6 (s : Machine) : Machine :=
  let s := input64_5 s
  {s with
    pc := 24
    negative := ((s.readX 0 - s.readX 2) >>> 63 != 0)
    zero := s.readX 0 - s.readX 2 == 0
    carry := s.readX 0 ≥ s.readX 2
    overflow := ((s.readX 0 >>> 63 != 0) != (s.readX 2 >>> 63 != 0)) &&
      (((s.readX 0 - s.readX 2) >>> 63 != 0) != (s.readX 0 >>> 63 != 0))}

structure InputState64 (s t : Machine) : Prop where
  input : t.readX 0 = s.readD 0
  fpcr : t.fpcr = s.fpcr
  fpsr : t.fpsr = s.fpsr
  vectors : t.v = s.v
  size : t.x.size = s.x.size
  registers : ∀ r, 3 ≤ r → r < 31 → t.readX r = s.readX r

theorem InputState64.withPC {s t : Machine} (h : InputState64 s t) (pc : UInt64) :
    InputState64 s {t with pc := pc} :=
  ⟨h.input, h.fpcr, h.fpsr, h.vectors, h.size, h.registers⟩

theorem InputState64.wellFormed {s t : Machine} (h : InputState64 s t) (hs : s.WellFormed) :
    t.WellFormed := ⟨h.size.trans hs.1, by rw [h.vectors]; exact hs.2⟩

theorem InputState64.scalar {s t : Machine} (h : InputState64 s t) : t.readD 0 = s.readD 0 := by
  simp only [Machine.readD, h.vectors]

attribute [local simp] Machine.readX_advanceX_same Machine.readX_advanceX_ne
  Machine.readX_advanceX_ne Machine.advanceX_size Machine.advanceX_fpcr
  Machine.advanceX_fpsr Machine.advanceX_vectors

theorem input64_2_state (s : Machine) (hs : s.x.size = 32) : InputState64 s (input64_2 s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [input64_2, input64_1, hs]
  · simp [input64_2, input64_1]
  · simp [input64_2, input64_1]
  · simp [input64_2, input64_1]
  · simp [input64_2, input64_1]
  · intro r hr hr'
    have h0 : 0 ≠ r := by omega
    have h1 : 1 ≠ r := by omega
    simp [input64_2, input64_1, hr', h0, h1]

theorem input64_6_state (s : Machine) (hs : s.x.size = 32) : InputState64 s (input64_6 s) := by
  have h := input64_2_state s hs
  have hx : (input64_4 s).readX 0 = s.readD 0 := h.input
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (input64_5 s).readX 0 = _
    rw [input64_5, Machine.readX_advanceX_ne _ 2 0 (by decide) (by decide) (by decide)]
    exact hx
  · change (input64_5 s).fpcr = _
    rw [input64_5, Machine.advanceX_fpcr]
    exact h.fpcr
  · change (input64_5 s).fpsr = _
    rw [input64_5, Machine.advanceX_fpsr]
    exact h.fpsr
  · change (input64_5 s).v = _
    rw [input64_5, Machine.advanceX_vectors]
    exact h.vectors
  · change (input64_5 s).x.size = _
    rw [input64_5, Machine.advanceX_size]
    exact h.size
  · intro r hr hr'
    change (input64_5 s).readX r = _
    rw [input64_5, Machine.readX_advanceX_ne _ 2 r (by decide) hr' (by omega)]
    exact h.registers r hr hr'

theorem input64_2_zero (s : Machine) (hs : s.x.size = 32) :
    ((input64_2 s).readX 1 == 0) = isZero64 (s.readD 0) := by
  simp [input64_2, input64_1, hs, isZero64]

theorem input64_sign_test (w : UInt64) : ((w >>> 63) &&& 1 != 0) = sign64 w := by
  have hm : (w >>> 63) &&& (1 : UInt64) = w >>> 63 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and]
    change (w >>> 63).toNat &&& (2 ^ 1 - 1) = (w >>> 63).toNat
    rw [Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_shiftRight]
    change (w.toNat >>> 63) % 2 = w.toNat >>> 63
    rw [Nat.shiftRight_eq_div_pow]
    have hb := w.toNat_lt
    omega
  rw [hm]
  by_cases h : w.toNat < 2 ^ 63
  · rw [sign64_false_of_lt w h]
    have hz : w >>> 63 = 0 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_shiftRight]
      change w.toNat >>> 63 = 0
      rw [Nat.shiftRight_eq_div_pow]
      omega
    simp [hz]
  · rw [sign64_true_of_ge w (by omega)]
    simp only [bne_iff_ne]
    intro hz
    have hn := congrArg UInt64.toNat hz
    rw [UInt64.toNat_shiftRight] at hn
    change w.toNat >>> 63 = 0 at hn
    rw [Nat.shiftRight_eq_div_pow] at hn
    omega

theorem input64_6_flags (s : Machine) (hs : s.x.size = 32) :
    (input64_6 s).zero = (s.readD 0 == 0x7ff0000000000000) ∧
      (input64_6 s).carry = decide (s.readD 0 ≥ 0x7ff0000000000000) := by
  have h0 : (input64_5 s).readX 0 = s.readD 0 := by
    change (input64_6 s).readX 0 = _
    exact (input64_6_state s hs).input
  have h2 : (input64_5 s).readX 2 = 0x7ff0000000000000 := by
    simp [input64_5, input64_4, input64_2, input64_1, hs]
  change ((input64_5 s).readX 0 - (input64_5 s).readX 2 == 0) = _ ∧
    decide ((input64_5 s).readX 0 ≥ (input64_5 s).readX 2) = _
  rw [h0, h2]
  refine ⟨?_, rfl⟩
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, UInt64.sub_eq_iff_eq_add, UInt64.zero_add]

end VerifiedSqrt.Arm

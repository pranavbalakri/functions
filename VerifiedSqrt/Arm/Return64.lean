module

public import VerifiedSqrt.Arm.Trace64
public import VerifiedSqrt.Arm.Registers64
public import VerifiedSqrt.Arm.InstructionProof64
public import VerifiedSqrt.Arm.Word64
public import VerifiedSqrt.Sqrt.Normalization64

@[expose] public section

namespace VerifiedSqrt.Arm

private theorem shiftZero64 (w : UInt64) : UInt64.shiftLeft w ⟨0#64⟩ = w := UInt64.shiftLeft_zero
private theorem shiftZero32 (w : UInt32) : UInt32.shiftLeft w ⟨0#32⟩ = w := UInt32.shiftLeft_zero

def bias64State (s : Machine) : Machine :=
  ({s with pc := s.pc + 4} : Machine).writeX 1 0x3fe0000000000000

def encode64State (s : Machine) : Machine :=
  let t := bias64State s
  ({t with pc := t.pc + 4} : Machine).writeX 0 (t.readX 0 + t.readX 1)

def rescale64State (s : Machine) : Machine :=
  let t := encode64State s
  ({t with pc := t.pc + 4} : Machine).writeX 0 (t.readX 0 + (t.readX 4 <<< 52))

def scalarResult64State (s : Machine) : Machine :=
  let t := rescale64State s
  ({t with pc := t.pc + 4} : Machine).writeD 0 (t.readX 0)

def returned64State (s : Machine) : Machine :=
  let t := scalarResult64State s
  {t with pc := t.readX 30}

theorem return64_registers (s : Machine) (hs : s.x.size = 32) :
    (rescale64State s).readX 0 = s.readX 0 + (0x3fe0000000000000 : UInt64) + (s.readX 4 <<< 52) := by
  have h1 : (bias64State s).x.size = 32 := by simpa [bias64State, Machine.writeX] using hs
  have h2 : (encode64State s).x.size = 32 := by simpa [encode64State, Machine.writeX] using h1
  have hr1 : (bias64State s).readX 1 = 0x3fe0000000000000 :=
    Machine.readX_writeX_same _ 1 (by decide) hs _
  have hr0 : (bias64State s).readX 0 = s.readX 0 :=
    Machine.readX_writeX_ne _ 1 0 (by decide) (by decide) (by decide) _
  have hr4 : (encode64State s).readX 4 = s.readX 4 := by
    have h : (encode64State s).readX 4 = (bias64State s).readX 4 :=
      Machine.readX_writeX_ne _ 0 4 (by decide) (by decide) (by decide) _
    have h' : (bias64State s).readX 4 = s.readX 4 :=
      Machine.readX_writeX_ne _ 1 4 (by decide) (by decide) (by decide) _
    exact h.trans h'
  have hr2 : (encode64State s).readX 0 = (bias64State s).readX 0 + (bias64State s).readX 1 :=
    Machine.readX_writeX_same _ 0 (by decide) h1 _
  have hr3 : (rescale64State s).readX 0 = (encode64State s).readX 0 + ((encode64State s).readX 4 <<< 52) :=
    Machine.readX_writeX_same _ 0 (by decide) h2 _
  rw [hr3, hr2, hr0, hr1, hr4]

theorem return64_link (s : Machine) : (scalarResult64State s).readX 30 = s.readX 30 := by
  change (rescale64State s).readX 30 = s.readX 30
  unfold rescale64State
  rw [Machine.readX_writeX_ne _ 0 30 (by decide) (by decide) (by decide)]
  change (encode64State s).readX 30 = s.readX 30
  unfold encode64State
  rw [Machine.readX_writeX_ne _ 0 30 (by decide) (by decide) (by decide)]
  change (bias64State s).readX 30 = s.readX 30
  unfold bias64State
  rw [Machine.readX_writeX_ne _ 1 30 (by decide) (by decide) (by decide)]
  rfl

theorem return64_value (s : Machine) (hs : s.WellFormed) :
    (returned64State s).readD 0 = s.readX 0 + (0x3fe0000000000000 : UInt64) + (s.readX 4 <<< 52) := by
  have hv : (rescale64State s).v.size = 32 := hs.2
  have h : (scalarResult64State s).readD 0 = (rescale64State s).readX 0 :=
    Machine.readD_writeD_same _ 0 (by decide) hv _
  change (scalarResult64State s).readD 0 = _
  rw [h, return64_registers s hs.1]

attribute [local cbv_opaque] Machine.readX Machine.writeX Machine.readD Machine.writeD
  supportedControls UInt64.add UInt64.shiftLeft

theorem step64_result_bias (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xd2e7fc01 s = some (s.advanceX 1 0x3fe0000000000000) := by
  unfold step64
  rw [hc]
  cbv

theorem step64_add_result_bias (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x8b010000 s = some (s.advanceX 0 (s.readX 0 + s.readX 1)) := by
  unfold step64
  rw [hc]
  cbv
  simp only [shiftZero64]

theorem step64_add_result_exponent (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x8b04d000 s = some (s.advanceX 0 (s.readX 0 + (s.readX 4 <<< 52))) := by
  unfold step64
  rw [hc]
  cbv

theorem step64_result_to_scalar (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0x9e670000 s = some (s.advanceD 0 (s.readX 0)) := by
  unfold step64
  rw [hc]
  cbv

theorem step64_return (s : Machine) (hc : supportedControls s.fpcr = true) :
    step64 0xd65f03c0 s = some ({s with pc := s.readX 30}) := by
  unfold step64 step
  rw [hc]
  cbv

theorem return64_trace (s : Machine) (hpc : s.pc = 280)
    (hc : supportedControls s.fpcr = true) :
    Steps64 sqrt64Code 0 5 s (returned64State s) := by
  have hp1 : (bias64State s).pc = 284 := by
    change (s).pc + 4 = _
    rw [hpc]
    decide +kernel
  have ht1 : Steps64 sqrt64Code 0 1 (s) (bias64State s) := Steps64.single
    (by rw [hpc]; decide +kernel) (by rw [hpc]; decide +kernel) (step64_result_bias (s) hc)
  have hp2 : (encode64State s).pc = 288 := by
    change (bias64State s).pc + 4 = _
    rw [hp1]
    decide +kernel
  have ht2 : Steps64 sqrt64Code 0 1 (bias64State s) (encode64State s) := Steps64.single
    (by rw [hp1]; decide +kernel) (by rw [hp1]; decide +kernel) (step64_add_result_bias (bias64State s) hc)
  have hp3 : (rescale64State s).pc = 292 := by
    change (encode64State s).pc + 4 = _
    rw [hp2]
    decide +kernel
  have ht3 : Steps64 sqrt64Code 0 1 (encode64State s) (rescale64State s) := Steps64.single
    (by rw [hp2]; decide +kernel) (by rw [hp2]; decide +kernel) (step64_add_result_exponent (encode64State s) hc)
  have hp4 : (scalarResult64State s).pc = 296 := by
    change (rescale64State s).pc + 4 = _
    rw [hp3]
    decide +kernel
  have ht4 : Steps64 sqrt64Code 0 1 (rescale64State s) (scalarResult64State s) := Steps64.single
    (by rw [hp3]; decide +kernel) (by rw [hp3]; decide +kernel) (step64_result_to_scalar (rescale64State s) hc)
  have ht5 : Steps64 sqrt64Code 0 1 (scalarResult64State s) (returned64State s) := Steps64.single
    (by rw [hp4]; decide +kernel) (by rw [hp4]; decide +kernel) (step64_return (scalarResult64State s) hc)
  exact ht1.trans (ht2.trans (ht3.trans (ht4.trans ht5)))

theorem return64_other_register (s : Machine) (r : Nat) (hr : r < 31)
    (h0 : r ≠ 0) (h1 : r ≠ 1) : (returned64State s).readX r = s.readX r := by
  change (rescale64State s).readX r = s.readX r
  unfold rescale64State
  rw [Machine.readX_writeX_ne _ 0 r (by decide) hr (Ne.symm h0)]
  change (encode64State s).readX r = s.readX r
  unfold encode64State
  rw [Machine.readX_writeX_ne _ 0 r (by decide) hr (Ne.symm h0)]
  change (bias64State s).readX r = s.readX r
  unfold bias64State
  rw [Machine.readX_writeX_ne _ 1 r (by decide) hr (Ne.symm h1)]
  rfl

theorem return64_other_vector (s : Machine) (r : Nat) (h : r ≠ 0) :
    (returned64State s).v[r]! = s.v[r]! := by
  exact Machine.vector_writeD_ne _ 0 r (Ne.symm h) _

theorem return64_correct (x : UInt64) (k : Int)
    (lo : 0x3ff0000000000000 ≤ x.toNat) (hi : x.toNat < 0x4010000000000000)
    (klo : -1021 ≤ k) (khi : k ≤ 1022) (s : Machine) (hs : s.WellFormed)
    (hq : (s.readX 0).toNat = Sqrt.correctedSignificand64 x)
    (hk : s.readW 4 = UInt32.ofInt k) :
    (returned64State s).readD 0 = Sqrt.rescale64 (Sqrt.core64 x) k := by
  have hb := Sqrt.correctedCore64_bounds x lo hi
  have hq' : s.readX 0 = UInt64.ofNat (Sqrt.correctedSignificand64 x) := by
    rw [← hq, UInt64.ofNat_toNat]
  have he : s.readX 0 + (0x3fe0000000000000 : UInt64) = Sqrt.core64 x := by
    rw [hq', Sqrt.core64]
    change UInt64.ofNat _ + UInt64.ofNat _ = _
    rw [← UInt64.ofNat_add]
    exact congrArg UInt64.ofNat (Nat.add_comm _ _)
  rw [return64_value s hs, he, word64_shift52_low32 (s.readX 4) k hk]
  exact word64_add_shift52 _ k (by omega)

end VerifiedSqrt.Arm

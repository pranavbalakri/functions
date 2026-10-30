module

public import VerifiedSqrt.Arm.Correctness32

@[expose] public section

namespace VerifiedSqrt.Arm

theorem initial32_scalar (dn : Bool) (x : UInt32) : (initial32 dn x).readS 0 = x := by
  change (({} : Machine).writeS 0 x).readS 0 = x
  exact Machine.readS_writeS_same {} 0 (by decide) (by decide) x

theorem initial32_link (dn : Bool) (x : UInt32) : (initial32 dn x).readX 30 = 4096 := by
  simp [initial32, Machine.readX, Machine.writeS]

theorem initial32_wellFormed (dn : Bool) (x : UInt32) : (initial32 dn x).WellFormed := by
  simp [Machine.WellFormed, initial32, Machine.writeS]

theorem initial32_controls (dn : Bool) (x : UInt32) : supportedControls (initial32 dn x).fpcr = true := by
  change supportedControls (if dn then 0x02000000 else 0) = true
  cases dn <;> decide +kernel

theorem initial32_dn (dn : Bool) (x : UInt32) :
    ((initial32 dn x).fpcr &&& 0x02000000 != 0) = dn := by
  change ((if dn then (0x02000000 : UInt32) else 0) &&& 0x02000000 != 0) = dn
  cases dn <;> decide +kernel

theorem machine32_eq_algorithm32 (dn : Bool) (x : UInt32) :
    machine32 dn x = some (Sqrt.algorithm32 dn x) := by
  obtain ⟨t, ht, hf⟩ := machine_algorithm32 (initial32 dn x) rfl
    (initial32_controls dn x) (initial32_wellFormed dn x)
    (by rw [initial32_link]; decide +kernel)
  rw [initial32_link] at ht
  have hrun := run_of_le_fuel _ _ _ sqrt32Fuel _ _ (by decide +kernel) ht
  have hv := hf.value
  rw [initial32_dn, initial32_scalar] at hv
  simp only [machine32, hrun, Option.map_some, hv]

theorem machine32_correct (dn : Bool) (x : UInt32) :
    ∃ y, machine32 dn x = some y ∧ Sqrt.SqrtSpec32 dn x y :=
  ⟨Sqrt.algorithm32 dn x, machine32_eq_algorithm32 dn x, Sqrt.algorithm32_correct dn x⟩

end VerifiedSqrt.Arm

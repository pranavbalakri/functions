module

public import VerifiedSqrt.Arm.Correctness64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem initial64_scalar (dn : Bool) (x : UInt64) : (initial64 dn x).readD 0 = x := by
  change (({} : Machine).writeD 0 x).readD 0 = x
  exact Machine.readD_writeD_same {} 0 (by decide) (by decide) x

theorem initial64_link (dn : Bool) (x : UInt64) : (initial64 dn x).readX 30 = 4096 := by
  simp [initial64, Machine.readX, Machine.writeD]

theorem initial64_wellFormed (dn : Bool) (x : UInt64) : (initial64 dn x).WellFormed := by
  simp [Machine.WellFormed, initial64, Machine.writeD]

theorem initial64_controls (dn : Bool) (x : UInt64) : supportedControls (initial64 dn x).fpcr = true := by
  change supportedControls (if dn then 0x02000000 else 0) = true
  cases dn <;> decide +kernel

theorem initial64_dn (dn : Bool) (x : UInt64) :
    ((initial64 dn x).fpcr &&& 0x02000000 != 0) = dn := by
  change ((if dn then (0x02000000 : UInt32) else 0) &&& 0x02000000 != 0) = dn
  cases dn <;> decide +kernel

theorem machine64_eq_algorithm64 (dn : Bool) (x : UInt64) :
    machine64 dn x = some (Sqrt.algorithm64 dn x) := by
  obtain ⟨t, ht, hf⟩ := machine_algorithm64 (initial64 dn x) rfl
    (initial64_controls dn x) (initial64_wellFormed dn x)
    (by rw [initial64_link]; decide +kernel)
  rw [initial64_link] at ht
  have hrun := run64_of_le_fuel _ _ _ _ sqrt64Fuel _ _ (by decide +kernel) ht
  have hv := hf.value
  rw [initial64_dn, initial64_scalar] at hv
  simp only [machine64, hrun, Option.map_some, hv]

theorem machine64_correct (dn : Bool) (x : UInt64) :
    ∃ y, machine64 dn x = some y ∧ Sqrt.SqrtSpec64 dn x y :=
  ⟨Sqrt.algorithm64 dn x, machine64_eq_algorithm64 dn x, Sqrt.algorithm64_correct dn x⟩

end VerifiedSqrt.Arm

module

public import VerifiedSqrt.Arm.Scalar32

namespace VerifiedSqrt.Arm

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
public theorem estimate_table_bounds : ∀ i : Fin 384,
    let a := 128 + i.val
    let r := recipSqrtEstimate a
    256 ≤ r ∧ r < 512 ∧ 65025 * 512 ≤ r * r * a ∧
      r * r * (a + 1) ≤ 66049 * 512 := by
  decide +kernel

#print axioms estimate_table_bounds

end VerifiedSqrt.Arm

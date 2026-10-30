module

public import VerifiedSqrt.Arm.Machine64

@[expose] public section

namespace VerifiedSqrt.Arm

theorem run64_step (code : Array UInt32) (base stop : UInt64) (fuel : Nat)
    (s t : Machine) (word : UInt32) (hne : s.pc ≠ stop)
    (ha : s.pc.toNat % 4 = 0) (hf : code[(s.pc - base).toNat / 4]? = some word)
    (hs : step64 word s = some t) :
    run64 code base stop (fuel + 1) s = run64 code base stop fuel t := by
  simp [run64, hne, ha, hf, hs]

theorem run64_at_stop (code : Array UInt32) (base stop : UInt64) (fuel : Nat)
    (s : Machine) (h : s.pc = stop) : run64 code base stop fuel s = some s := by
  cases fuel <;> simp [run64, h]

theorem run64_add_fuel (code : Array UInt32) (base stop : UInt64) (fuel extra : Nat)
    (s t : Machine) (h : run64 code base stop fuel s = some t) :
    run64 code base stop (fuel + extra) s = some t := by
  induction fuel generalizing s with
  | zero =>
    by_cases hp : s.pc = stop
    · have ht : s = t := by simpa [run64, hp] using h
      subst t
      exact run64_at_stop code base stop _ s hp
    · simp [run64, hp] at h
  | succ fuel ih =>
    by_cases hp : s.pc = stop
    · have ht : s = t := by simpa [run64, hp] using h
      subst t
      exact run64_at_stop code base stop _ s hp
    by_cases ha : s.pc.toNat % 4 = 0
    · cases hw : code[(s.pc - base).toNat / 4]? with
      | none => simp [run64, hp, ha, hw] at h
      | some word =>
        cases hs : step64 word s with
        | none => simp [run64, hp, ha, hw, hs] at h
        | some next =>
          have hn : run64 code base stop fuel next = some t := by simpa [run64, hp, ha, hw, hs] using h
          rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega,
            run64_step code base stop (fuel + extra) s next word hp ha hw hs]
          exact ih next hn
    · simp [run64, hp, ha] at h

theorem run64_of_le_fuel (code : Array UInt32) (base stop : UInt64) (fuel limit : Nat)
    (s t : Machine) (hle : fuel ≤ limit) (h : run64 code base stop fuel s = some t) :
    run64 code base stop limit s = some t := by
  have hr := run64_add_fuel code base stop fuel (limit - fuel) s t h
  simpa only [Nat.add_sub_cancel' hle] using hr

theorem run64_compose (code : Array UInt32) (base middle stop : UInt64) (before after : Nat)
    (s t u : Machine) (hstop : code[(stop - base).toNat / 4]? = none)
    (hbefore : run64 code base middle before s = some t)
    (hafter : run64 code base stop after t = some u) :
    run64 code base stop (before + after) s = some u := by
  induction before generalizing s with
  | zero =>
    by_cases hp : s.pc = middle
    · have ht : s = t := by simpa [run64, hp] using hbefore
      subst s
      simpa using hafter
    · simp [run64, hp] at hbefore
  | succ before ih =>
    by_cases hp : s.pc = middle
    · have ht : s = t := by simpa [run64, hp] using hbefore
      subst s
      simpa only [Nat.add_comm] using run64_add_fuel code base stop after (before + 1) t u hafter
    by_cases ha : s.pc.toNat % 4 = 0
    · cases hw : code[(s.pc - base).toNat / 4]? with
      | none => simp [run64, hp, ha, hw] at hbefore
      | some word =>
        have hne : s.pc ≠ stop := by
          intro h
          rw [h, hstop] at hw
          contradiction
        cases hs : step64 word s with
        | none => simp [run64, hp, ha, hw, hs] at hbefore
        | some next =>
          have hn : run64 code base middle before next = some t := by
            simpa [run64, hp, ha, hw, hs] using hbefore
          rw [show before + 1 + after = (before + after) + 1 by omega,
            run64_step code base stop (before + after) s next word hne ha hw hs]
          exact ih next hn
    · simp [run64, hp, ha] at hbefore

end VerifiedSqrt.Arm

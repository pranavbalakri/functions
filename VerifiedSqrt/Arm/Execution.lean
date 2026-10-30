module

public import VerifiedSqrt.Arm.Machine

@[expose] public section

namespace VerifiedSqrt.Arm

theorem run_step (code : Array UInt32) (stop : UInt64) (fuel : Nat)
    (s t : Machine) (word : UInt32) (hne : s.pc ≠ stop)
    (ha : s.pc.toNat % 4 = 0) (hf : code[s.pc.toNat / 4]? = some word)
    (hs : step word s = some t) :
    run code stop (fuel + 1) s = run code stop fuel t := by
  simp [run, hne, ha, hf, hs]

theorem run_at_stop (code : Array UInt32) (stop : UInt64) (fuel : Nat)
    (s : Machine) (h : s.pc = stop) : run code stop fuel s = some s := by
  cases fuel <;> simp [run, h]

theorem run_add_fuel (code : Array UInt32) (stop : UInt64) (fuel extra : Nat)
    (s t : Machine) (h : run code stop fuel s = some t) :
    run code stop (fuel + extra) s = some t := by
  induction fuel generalizing s with
  | zero =>
    by_cases hp : s.pc = stop
    · have ht : s = t := by simpa [run, hp] using h
      subst t
      exact run_at_stop code stop _ s hp
    · simp [run, hp] at h
  | succ fuel ih =>
    by_cases hp : s.pc = stop
    · have ht : s = t := by simpa [run, hp] using h
      subst t
      exact run_at_stop code stop _ s hp
    by_cases ha : s.pc.toNat % 4 = 0
    · cases hw : code[s.pc.toNat / 4]? with
      | none => simp [run, hp, ha, hw] at h
      | some word =>
        cases hs : step word s with
        | none => simp [run, hp, ha, hw, hs] at h
        | some next =>
          have hn : run code stop fuel next = some t := by simpa [run, hp, ha, hw, hs] using h
          rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega,
            run_step code stop (fuel + extra) s next word hp ha hw hs]
          exact ih next hn
    · simp [run, hp, ha] at h

theorem run_of_le_fuel (code : Array UInt32) (stop : UInt64) (fuel limit : Nat)
    (s t : Machine) (hle : fuel ≤ limit) (h : run code stop fuel s = some t) :
    run code stop limit s = some t := by
  have hr := run_add_fuel code stop fuel (limit - fuel) s t h
  simpa only [Nat.add_sub_cancel' hle] using hr

theorem run_compose (code : Array UInt32) (middle stop : UInt64) (before after : Nat)
    (s t u : Machine) (hstop : code[stop.toNat / 4]? = none)
    (hbefore : run code middle before s = some t)
    (hafter : run code stop after t = some u) :
    run code stop (before + after) s = some u := by
  induction before generalizing s with
  | zero =>
    by_cases hp : s.pc = middle
    · have ht : s = t := by simpa [run, hp] using hbefore
      subst s
      simpa using hafter
    · simp [run, hp] at hbefore
  | succ before ih =>
    by_cases hp : s.pc = middle
    · have ht : s = t := by simpa [run, hp] using hbefore
      subst s
      simpa only [Nat.add_comm] using run_add_fuel code stop after (before + 1) t u hafter
    by_cases ha : s.pc.toNat % 4 = 0
    · cases hw : code[s.pc.toNat / 4]? with
      | none => simp [run, hp, ha, hw] at hbefore
      | some word =>
        have hne : s.pc ≠ stop := by
          intro h
          rw [h, hstop] at hw
          contradiction
        cases hs : step word s with
        | none => simp [run, hp, ha, hw, hs] at hbefore
        | some next =>
          have hn : run code middle before next = some t := by
            simpa [run, hp, ha, hw, hs] using hbefore
          rw [show before + 1 + after = (before + after) + 1 by omega,
            run_step code stop (before + after) s next word hne ha hw hs]
          exact ih next hn
    · simp [run, hp, ha] at hbefore

end VerifiedSqrt.Arm

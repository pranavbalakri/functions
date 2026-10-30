module

public import VerifiedSqrt.Arm.Execution64
public import VerifiedSqrt.Arm.Registers

@[expose] public section

namespace VerifiedSqrt.Arm

inductive Steps64 (code : Array UInt32) (base : UInt64) : Nat → Machine → Machine → Prop
  | refl (s : Machine) : Steps64 code base 0 s s
  | cons {n : Nat} {s t u : Machine} {word : UInt32}
      (aligned : s.pc.toNat % 4 = 0)
      (fetch : code[(s.pc - base).toNat / 4]? = some word)
      (execute : step64 word s = some t) (tail : Steps64 code base n t u) :
      Steps64 code base (n + 1) s u

theorem Steps64.single {code : Array UInt32} {base : UInt64} {s t : Machine} {word : UInt32}
    (ha : s.pc.toNat % 4 = 0) (hf : code[(s.pc - base).toNat / 4]? = some word)
    (he : step64 word s = some t) : Steps64 code base 1 s t :=
  .cons ha hf he (.refl t)

theorem Steps64.trans {code : Array UInt32} {base : UInt64} {n m : Nat} {s t u : Machine}
    (h : Steps64 code base n s t) (k : Steps64 code base m t u) :
    Steps64 code base (n + m) s u := by
  induction h with
  | refl => simpa using k
  | cons ha hf he ht ih =>
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Steps64.cons ha hf he (ih k)

theorem Steps64.run {code : Array UInt32} {base stop : UInt64} {n : Nat} {s t : Machine}
    (h : Steps64 code base n s t) (hp : t.pc = stop)
    (hs : code[(stop - base).toNat / 4]? = none) : run64 code base stop n s = some t := by
  induction h with
  | refl => exact run64_at_stop _ _ _ _ _ hp
  | @cons n s v t word ha hf he ht ih =>
    have hn : s.pc ≠ stop := by
      intro h
      rw [h, hs] at hf
      contradiction
    rw [run64_step _ _ _ _ _ _ _ hn ha hf he]
    exact ih hp

theorem run64_steps (code : Array UInt32) (base stop : UInt64) (fuel : Nat)
    (s t : Machine) (hr : run64 code base stop fuel s = some t) :
    ∃ n, n ≤ fuel ∧ Steps64 code base n s t := by
  induction fuel generalizing s with
  | zero =>
    by_cases hp : s.pc = stop
    · have he : s = t := by simpa [run64, hp] using hr
      subst t
      exact ⟨0, by omega, .refl s⟩
    · simp [run64, hp] at hr
  | succ fuel ih =>
    by_cases hp : s.pc = stop
    · have he : s = t := by simpa [run64, hp] using hr
      subst t
      exact ⟨0, by omega, .refl s⟩
    by_cases ha : s.pc.toNat % 4 = 0
    · cases hw : code[(s.pc - base).toNat / 4]? with
      | none => simp [run64, hp, ha, hw] at hr
      | some word =>
        cases he : step64 word s with
        | none => simp [run64, hp, ha, hw, he] at hr
        | some u =>
          have hu : run64 code base stop fuel u = some t := by
            simpa [run64, hp, ha, hw, he] using hr
          obtain ⟨n, hn, ht⟩ := ih u hu
          exact ⟨n + 1, by omega, .cons ha hw he ht⟩
    · simp [run64, hp, ha] at hr

structure IntegerFrame (changed : List Nat) (s t : Machine) : Prop where
  fpcr : t.fpcr = s.fpcr
  fpsr : t.fpsr = s.fpsr
  vectors : t.v = s.v
  size : t.x.size = s.x.size
  registers : ∀ r, r < 31 → r ∉ changed → t.readX r = s.readX r

theorem IntegerFrame.refl (changed : List Nat) (s : Machine) : IntegerFrame changed s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem IntegerFrame.trans {changed : List Nat} {s t u : Machine}
    (h : IntegerFrame changed s t) (k : IntegerFrame changed t u) : IntegerFrame changed s u :=
  ⟨k.fpcr.trans h.fpcr, k.fpsr.trans h.fpsr, k.vectors.trans h.vectors,
    k.size.trans h.size, fun r hr hn => (k.registers r hr hn).trans (h.registers r hr hn)⟩

theorem IntegerFrame.widen {small large : List Nat} {s t : Machine}
    (h : IntegerFrame small s t) (hl : ∀ r, r ∈ small → r ∈ large) : IntegerFrame large s t :=
  ⟨h.fpcr, h.fpsr, h.vectors, h.size, fun r hr hn => h.registers r hr (fun hm => hn (hl r hm))⟩

theorem IntegerFrame.pc (changed : List Nat) (s : Machine) (pc : UInt64) :
    IntegerFrame changed s {s with pc := pc} :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem IntegerFrame.writeX (changed : List Nat) (s : Machine) (d : Nat)
    (hd : d < 31) (hm : d ∈ changed) (w : UInt64) : IntegerFrame changed s (s.writeX d w) := by
  have hn : d ≠ 31 := by omega
  refine ⟨by simp [Machine.writeX, hn], by simp [Machine.writeX, hn],
    by simp [Machine.writeX, hn], by simp [Machine.writeX, hn], ?_⟩
  intro r hr hnot
  exact Machine.readX_writeX_ne s d r hd hr (by intro h; subst r; exact hnot hm) w

def compare64State (s : Machine) (a b : UInt64) : Machine := {s with
  pc := s.pc + 4
  negative := (a - b) >>> 63 != 0
  zero := a - b == 0
  carry := a ≥ b
  overflow := ((a >>> 63 != 0) != (b >>> 63 != 0)) &&
    (((a - b) >>> 63 != 0) != (a >>> 63 != 0))}

theorem IntegerFrame.compare (changed : List Nat) (s : Machine) (a b : UInt64) :
    IntegerFrame changed s (compare64State s a b) :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

end VerifiedSqrt.Arm

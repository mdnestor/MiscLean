
-- Trying to construct the integers from the naturals and show they form a ring
def Integer_setoid: Setoid (Nat × Nat) := {
  r := fun a b => a.1 + b.2 = a.2 + b.1
  iseqv := {
    refl := by
      intro
      rw [Nat.add_comm]
    symm := by
      intro _ _ h
      rw [Nat.add_comm, ←h, Nat.add_comm]
    trans := by
      intro x y z h1 h2
      apply @Nat.add_left_cancel y.fst
      rw [Nat.add_comm, Nat.add_assoc, Nat.add_comm z.snd]
      rw [h2]
      rw [←Nat.add_assoc]
      rw [h1]
      rw [Nat.add_comm x.snd, Nat.add_assoc]
  }
}

def Integer := Quotient Integer_setoid

def Integer.neg: Integer → Integer := Quotient.lift (fun x: Nat × Nat => Quotient.mk Integer_setoid (x.2, x.1)) (by {
  intro _ _ h
  apply Quotient.sound
  apply Eq.symm
  exact h
})

def Integer.add: Integer → Integer → Integer := Quotient.lift₂ (fun a b: Nat × Nat => Quotient.mk Integer_setoid (a.1 + b.1, a.2 + b.2)) (by {
  intro x y w z h1 h2
  apply Quot.sound
  simp [Integer_setoid]
  rw [Nat.add_assoc, Nat.add_comm y.fst, Nat.add_assoc w.snd, ←Nat.add_assoc x.fst, Nat.add_comm z.snd]
  rw [←Nat.add_assoc (x.snd + y.snd), Nat.add_assoc x.snd, Nat.add_comm y.snd, ←Nat.add_assoc x.snd, Nat.add_assoc (x.snd + w.fst)]
  rw [h1, h2]
})

def Integer.zero: Integer := Quotient.mk Integer_setoid (0, 0)

theorem Integer.add_zero_left (x: Integer): Integer.add Integer.zero x = x := by
  sorry

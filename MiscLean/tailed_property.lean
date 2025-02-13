
-- "tailed properties"

def Sequence (X: Type u): Type u :=
  Nat → X

def tail (x: Sequence X) (n: Nat): Nat → X :=
  fun m => x (n + m)

-- a property is called "tailed" if it holds for a sequence iff. it holds for every tail.
def tailed (P: Sequence X → Prop): Prop :=
  ∀ x n, P x ↔ P (tail x n)

-- example 1: an event occuring infinitely often is a tailed property
def infinitely_often (x: Sequence X) (Q: X → Prop): Prop :=
  ∀ n, ∃ m, n ≤ m ∧ Q (x m)

example (Q: X → Prop): tailed (λ x => infinitely_often x Q) := by
  intro x n0
  constructor
  . intro h n
    obtain ⟨m, hm⟩ := h (n + n0)
    exists m - n0
    constructor
    . exact Nat.le_sub_of_add_le hm.left
    . simp [tail]
      rw [Nat.add_sub_of_le]
      . exact hm.right
      . rw [Nat.add_comm] at hm
        exact Nat.le_of_add_right_le hm.left
  . intro h n
    simp_all [infinitely_often, tail]
    obtain ⟨m, hm⟩ := h n
    exists n0 + m
    constructor
    rw [Nat.add_comm]
    exact Nat.le_add_right_of_le hm.left
    exact hm.right

-- example 2: an event occuring eventually is tailed
def eventually (x: Sequence X) (Q: X → Prop): Prop :=
  ∃ n, ∀ m, n ≤ m → Q (x m)

example (Q : X → Prop) : tailed (λ x => eventually x Q) := by
  sorry

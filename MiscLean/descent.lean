
/- 

Every nonincreasing sequence of natural numbers must stabilize, i.e. be eventually constant.

Proof idea:
If the sequence does not stabilize we can construct a strictly decreasing subsequence, which is a contradiction.

-/

@[simp]
def decreasing (a: Nat → Nat): Prop := ∀ m n: Nat, m < n → a n < a m

@[simp]
def nonincreasing (a: Nat → Nat): Prop := ∀ m n: Nat, m ≤ n → a n ≤ a m

@[simp]
def stabilizes (a: Nat → Nat): Prop := ∃ m: Nat, ∀ n: Nat, m ≤ n → a m = a n

def leq_lemma {a b: Nat}: a ≤ b → a - 1 ≤ b - 1 := sorry

theorem decreasing_iff {a: Nat → Nat}: decreasing a ↔ ∀ n: Nat, a (n + 1) < a n := sorry

theorem decreasing_bound {a: Nat → Nat} (h: decreasing a): ∀ n: Nat, a n ≤ a 0 - n := by
  intro n
  induction n with
  | zero => simp
  | succ p hp =>
    specialize h p (p + 1)
    simp at h
    calc
      a (p + 1) ≤ a p - 1       := by exact Nat.le_sub_one_of_lt h
              _ ≤ (a 0 - p) - 1 := leq_lemma hp
            
theorem no_decreasing_sequence {a: Nat → Nat} (h: decreasing a): False := by
  have bound: ∀ n: Nat, a n ≤ a 0 - n := decreasing_bound h
  specialize bound (a 0)
  simp at bound
  specialize h (a 0) (a 0 + 1)
  simp at h
  rw [bound] at h
  contradiction

noncomputable def construction {a: Nat → Nat} (h: ∀ x: Nat, ∃ x1: Nat, x < x1 ∧ a x1 < a x): Nat → Nat :=
  fun n => match n with
  | Nat.zero => 0
  | Nat.succ p => Classical.choose (h (construction h p))

theorem descent (a: Nat → Nat): nonincreasing a → stabilizes a := by
  intro h
  apply Classical.not_not.mp
  intro h0
  simp at h0
  have: ∀ m: Nat, ∃ n: Nat, m < n ∧ a n < a m := by
    intro m
    obtain ⟨n, hn⟩ := h0 m
    exists n
    constructor
    . have: m ≠ n := by intro; simp_all
      exact Nat.lt_of_le_of_ne hn.left this
    . specialize h m n hn.left
      apply Nat.lt_of_le_of_ne h
      rw [← ne_eq]
      intro
      simp_all
  let f := construction this
  have: ∀ n: Nat, a (f (n + 1)) < a (f n) := by
    intro n
    exact (Classical.choose_spec (this (f n))).right
  have: decreasing (a ∘ f) := decreasing_iff.mpr this
  exact no_decreasing_sequence this

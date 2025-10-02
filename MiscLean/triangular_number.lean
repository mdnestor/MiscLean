/-
The n-th triangular number is defined as the sum of the first n natural numbers: T(n) = 0+1+2+3+...+n
It can be proved via induction that T(n) = n*(n+1)/2.
To avoid integer division, we will instead prove 2 * T(n) = n*(n+1).
-/

def triangular (n: Nat): Nat :=
  match n with
  | Nat.zero => 0
  | Nat.succ p => (triangular p) + n

/-
Inductive proof using the `calc` tactic.
https://github.com/leanprover/theorem_proving_in_lean4/blob/master/quantifiers_and_equality.md#calculational-proofs
Useful lemmas about natural number arithmetic come from https://github.com/leanprover/lean4/blob/master/src/Init/Data/Nat/Basic.lean
-/

theorem triangular_formula: ∀ n: Nat, 2 * (triangular n) = n * (n + 1) := by
  intro n
  induction n with
  | zero => {
    rw [triangular]
  }
  | succ n h => {
    calc
      2 * triangular (n + 1) = 2 * (triangular n + (n + 1))   := by rw [triangular]
                           _ = 2 * triangular n + 2 * (n + 1) := by rw [Nat.left_distrib]
                           _ = n * (n + 1) + 2 * (n + 1)      := by rw [h]
                           _ = (n + 1) * n + 2 * (n + 1)      := by rw [Nat.mul_comm]
                           _ = (n + 1) * n + (n + 1) * 2      := by rw [Nat.mul_comm 2 (n + 1)]
                           _ = (n + 1) * (n + 2)              := by rw [Nat.left_distrib]
                           _ = (n + 1) * (n + 2 * 1)          := by rfl
                           _ = (n + 1) * (n + 1 + 1)          := by rw [Nat.two_mul]
  }

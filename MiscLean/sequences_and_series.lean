import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

def converges (a: Nat -> Real) (L: Real): Prop :=
  forall epsilon: Real, exists N: Nat, forall n: Nat,
  (0 < epsilon) ∧ (N ≤ n) -> abs (a n - L) < epsilon

def convergent (a: Nat -> Real) : Prop :=
  exists L: Real, converges a L

theorem constant_sequence_converges (c: Real): converges (fun _ => c) c := by
  intro epsilon
  exists 0
  intro n
  intro ⟨h0, _⟩
  simp
  exact h0

theorem constant_sequence_convergent (c: Real): convergent (fun _ => c) := by
  exists c
  exact constant_sequence_converges c

theorem sum_converges (h0: converges a0 L0) (h1: converges a1 L1): converges (fun n => a0 n + a1 n) (L0 + L1) := by
  intro epsilon
  obtain ⟨N0, h2⟩ := h0 (epsilon / 2)
  obtain ⟨N1, h3⟩ := h1 (epsilon / 2)
  exists max N0 N1
  intro n
  intro ⟨h4, h5⟩
  simp
  have h6: 0 < epsilon / 2 := div_pos h4 two_pos
  have h7: N0 ≤ n := (max_le_iff.mp h5).1
  have h8: N1 ≤ n := (max_le_iff.mp h5).2
  have h9 := h2 n ⟨h6, h7⟩
  have h10 := h3 n ⟨h6, h8⟩
  calc
    |a0 n + a1 n - (L0 + L1)| = |(a0 n - L0) + (a1 n - L1)|   := by ring_nf
                            _ ≤ |a0 n - L0| + |a1 n - L1|     := by apply abs_add
                            _ < (epsilon / 2) + (epsilon / 2) := by linarith [h9, h10]
                            _ = epsilon                       := by simp

theorem product_converges (h0: converges a0 L0) (h1: converges a1 L1): converges (fun n => a0 n * a1 n) (L0 * L1) := by
  sorry

def partial_sums (a: Nat -> Real): Nat -> Real := by
  intro n
  exact match n with
  | Nat.zero => 0
  | Nat.succ m => a n + (partial_sums a) m

def series_converges (a: Nat -> Real) (L: Real): Prop :=
  converges (partial_sums a) L

def series_convergent (a: Nat -> Real): Prop :=
  convergent (partial_sums a)

theorem zero_series_converges_to_zero: series_converges (fun _ => 0) 0 := by
  intro epsilon
  exists 0
  intro n
  intro ⟨h0, h1⟩
  simp
  induction n with
  | zero => {
    rw [partial_sums]
    rw [abs_zero]
    exact h0
  }
  | succ p h => {
    rw [partial_sums]
    simp
    exact h (Nat.zero_le p)
  }

theorem partial_sums_convergent_implies_limit_zero (a: Nat -> Real):
  series_convergent a -> converges a 0 := 
  sorry


-- https://math.stackexchange.com/questions/1936098/

import Mathlib.Logic.Function.Iterate

def lemma1 {f: Nat → Nat} (h: ∀ n, f (f n) = n + 1): ∀ n, f^[2 * n] 0 = n := by
  intro n
  induction n with
  | zero => rfl
  | succ p hp =>
    simp [Nat.left_distrib, Function.iterate_add, hp, Nat.add_comm]
    exact h p

def lemma2 {f: Nat → Nat} (h: ∀ n, f (f n) = n + 1): ∀ n, f^[2 * n + 1] 0 = f 0 + n := by
  intro n
  induction n with
  | zero => simp
  | succ p hp =>
    simp_all [Nat.left_distrib, Function.iterate_add, hp, Nat.add_comm, h (f 0 + p)]
    rw [Nat.add_comm p, Nat.add_assoc]

def lemma3 {f: Nat → Nat} (h: ∀ n, f (f n) = n + 1): ∀ n, f n = f 0 + n := by
  intro n
  calc
    f n = f (f^[2 * n] 0) := by rw [lemma1 h n]
      _ = f^[2 * n + 1] 0 := by exact Eq.symm (Function.iterate_succ_apply' f (2 * n) 0)
      _ = f 0 + n         := by rw [lemma2 h n]

def lemma4 {f: Nat → Nat} (h: ∀ n, f (f n) = n + 1): 2 * f 0 = 1 := by
  calc
    2 * f 0 = f 0 + f 0 := by exact Nat.two_mul (f 0)
          _ = f (f 0)   := by rw [lemma3 h (f 0)]
          _ = 1         := by rw [h]

def lemma5: ∀ n: Nat, ¬ (2 * n = 1) := by
  intro n hn
  have h: 2 * n % 2 = 1 % 2 := by rw [hn]
  simp at h

theorem main: ∀ f: Nat → Nat, ¬ (∀ n, f (f n) = n + 1) := by
  intro f h
  exact lemma5 (f 0) (lemma4 h)

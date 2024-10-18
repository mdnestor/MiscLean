import Mathlib

open Finset BigOperators

example {a r : ℝ} (n : ℕ) (h : r ≠ 1) : ∑ i ∈ range (n+1), a * r^i = (a * r^(n+1) - a) / (r-1) := by
  rw [←mul_sum, ←mul_one a, mul_assoc a 1 (r^(n+1)), ←mul_sub_left_distrib]
  simp [mul_div_assoc]
  apply Or.inl
  have: r - 1 ≠ 0 := by
    intro h
    have := eq_add_of_sub_eq h
    simp_all
  induction n with
  | zero => simp [div_self this]
  | succ p hp => 
    rw [Finset.sum_range_succ, hp]
    calc
      _ = (r^(p+1) - 1) / (r-1) + r^(p+1) * 1 := by simp
      _ = (r^(p+1) - 1) / (r-1) + r^(p+1) * ((r-1)/(r-1)) := by rw [div_self this]
    ring_nf

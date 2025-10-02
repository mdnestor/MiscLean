-- Defines metric spaces and the discrete metric

import Mathlib.Data.Real.Basic

universe u

class MetricSpace (X: Type u) where
  dist: X → X → Real
  dist_nonneg: ∀ (x y: X), 0 ≤ dist x y
  dist_zero_iff: ∀ (x y: X), dist x y = 0 ↔ x = y
  dist_symm: ∀ (x y: X), dist x y = dist y x
  triangle_ineq: ∀ (x y z: X), dist x z ≤ dist x y + dist y z

open MetricSpace

theorem dist_self_zero {X: Type u} [MetricSpace X] (x: X): dist x x = 0 := by
  apply (dist_zero_iff x x).mpr
  rfl

def DiscreteMetric (X: Type u) [DecidableEq X]: MetricSpace X := {
  dist := fun x y => if x = y then 0 else 1
  dist_nonneg := by
    intros
    simp
    split <;> simp
  dist_zero_iff := by
    simp
  dist_symm := by
    intros
    simp
    split <;> split <;> simp_all
  triangle_ineq := by 
    intros
    simp
    split <;> split <;> split <;> simp_all
}

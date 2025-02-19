
-- defines inner product space over a complex vector field (more generally complex module)
-- also shows how an inner product space is a norm space, and a norm space is a metric space.

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Complex.Abs

class MetricSpace2 (X: Type u) where
  dist: X → X → ℝ
  nonneg: ∀ x y, 0 ≤ dist x y
  symm: ∀ x y, dist x y = dist y x
  triangle: ∀ x y z, dist x z ≤ dist x y + dist y z

class NormSpace (X: Type u) [AddCommMonoid X] [Module ℂ X] where
  norm: X → ℝ
  triangle_ineq: ∀ x y, norm (x + y) ≤ norm x + norm y
  homog: ∀ c x, norm (c • x) = Complex.abs c * norm x
  positive_def: ∀ x, x = 0 ↔ norm x = 0

theorem norm_zero (X: Type u) [AddCommMonoid X] [Module ℂ X] [N: NormSpace X]: N.norm 0 = 0 := by
  apply (N.positive_def 0).mp
  rfl 

theorem norm_nonneg (X: Type u) [AddCommGroup X] [Module ℂ X] [N: NormSpace X]: ∀ x, 0 ≤ N.norm x := by
  intro x
  have := N.triangle_ineq x (-x)
  rw [Eq.symm (neg_one_smul ℂ x)] at this
  rw [N.homog (-1) x] at this
  simp [←two_mul] at this
  rw [norm_zero] at this
  have h2: 0 ≤ (1/2: ℝ) := by aesop -- lol
  have := mul_le_mul_of_nonneg_left this h2
  simp at this
  exact this 

-- convert a norm space to a metric space
def NormSpace.toMetricSpace (X: Type u) [AddCommGroup X] [Module ℂ X] [N: NormSpace X]: MetricSpace2 X := {
  dist := fun x y => N.norm (x - y)
  nonneg := by
    intros
    apply norm_nonneg
  symm := by
    intro x y
    calc
      norm (x - y) = (Complex.abs 1) * norm (x - y) := by simp
                 _ = Complex.abs (-1) * norm (x - y) := by simp
                 _ = norm ((-1: ℂ) • (x - y)) := by rw [N.homog (-1) (x - y)]
                 _ = norm (y - x) := by simp
  triangle := by
    intro x y z
    have := N.triangle_ineq (x - y) (y - z)
    simp at this
    exact this
}

class InnerProductSpace (X: Type u) [AddCommMonoid X] [Module ℂ X] where
  inner_prod: X → X → ℂ
  conj_symm: inner_prod x y = star (inner_prod y x)
  linear: inner_prod (a • x + b • y) z = a * inner_prod x z + b * inner_prod y z
  positive_def: ∀ x, x = 0 ↔ inner_prod x x = 0

noncomputable def InnerProductSpace.toNormSpace (X: Type u) [AddCommMonoid X] [Module ℂ X] [P: InnerProductSpace X]: NormSpace X := {
  norm := fun x => Real.sqrt (P.inner_prod x x).re
  triangle_ineq := by sorry -- use cauchy schwarz
  homog := by sorry
  positive_def := by
    intro x
    simp
    constructor
    . intro h
      rw [h]
      have := (P.positive_def x).mp h
      rw [h] at this
      simp [this]
    . intro h
      sorry
}

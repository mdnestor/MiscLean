
/-

proof of Euler's identity:

Let f(z) = (cos(z) + i * sin(z)) * exp(-i * z).

Then f'(z) = 0 and f(0) = 1, so f(z) = 1.

-/

import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Complex

theorem Euler (z: Complex): exp (i * z) = cos z + i * sin z := by

  let f: Complex → Complex := fun z => (cos z + i * sin z) * exp (-i * z)

  have hf0: f 0 = 1 := by calc
    f 0 = (cos 0 + i * sin 0) * exp (-i * 0) := by rfl
      _ = (1 + i * 0) * exp 0 := by simp
      _ = 1 := by simp
      
  have hf: deriv f = 0 := by
    simp [f]
    ext z
    calc
      deriv (fun z => (cos z + i * sin z) * exp (-(i * z))) z
      _ = (deriv (fun z => (cos z + i * sin z)) z) * exp (-(i * z)) + (cos z + i * sin z) * (deriv (fun z => exp (-(i * z))) z) := by sorry
      _ = (deriv cos z + i * deriv sin z) * cexp (-(i * z)) + (cos z + i * sin z) * (-i * deriv exp (-(i * z))) := by sorry
      _ = (-sin z + i * cos z) * exp (-(i * z)) + (cos z + i * sin z) * (-i * exp (-(i * z))) := by sorry
      _ = (-sin z + i * cos z) * exp (-(i * z)) + ((cos z + i * sin z) * -i) * exp (-(i * z)) := by sorry
      _ = ((-sin z + i * cos z) + ((cos z + i * sin z) * -i)) * exp (-(i * z)) := by rw [←right_distrib]
      _ = 0 * exp (-(i * z)) := by sorry
      _ = 0 := by simp

  have: Differentiable Complex f := by
    simp [f]
    apply Differentiable.mul
    apply Differentiable.add
    exact differentiable_cos
    apply Differentiable.mul
    apply differentiable_const
    exact differentiable_sin
    apply Differentiable.cexp
    apply Differentiable.neg
    apply Differentiable.mul
    apply differentiable_const
    exact differentiable_id
  
  have := is_const_of_deriv_eq_zero this (by simp [hf]) 0
  rw [hf0] at this
  apply Eq.symm
  calc
    cos z + i * sin z 
    _ = (cos z + i * sin z) * exp (-i * z) * exp (i * z) := by simp [f, exp_neg]
    _ = (f z) * exp (i * z) := by simp [f]
    _ = 1 * exp (i * z) := by rw [this]
    _ = exp (i * z) := by simp

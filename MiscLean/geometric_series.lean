
-- proof of the geometric series formula
-- if |r| < 1 then 1 + r + r^2 + ... = 1/(1 - r)
-- see Mathlib.Analysis.SpecificLimits.Basic.hasSum_geometric_of_lt_one

import Mathlib.Data.Real.Basic

-- definition of convergence for sequences of real numbers
def converges (s: Nat → Real) (x: Real): Prop :=
  ∀ ε: Real, ε > 0 → ∀ N: Nat, ∃ n: Nat, N ≤ n → |s n - x| < ε

-- a sequence is convergent if there exists a real number to which it converges
def convergent (s: Nat → Real): Prop :=
  ∃ x: Real, converges s x

-- if a0, a1, a2, ... converges to x then c * a0, c * a1, c * a2, ... converges to c * x
theorem converges_mul (h: converges a x) (c: Real): converges (fun n => c * a n) (c * x) :=
  sorry

-- if a sequence converges to both x1 and x2 then x1 = x2
theorem converges_unique (h1: converges a x1) (h2: converges a x2): x1 = x2 := by
  sorry

def series (s: Nat → Real): Nat → Real :=
  fun n => match n with
  | 0 => s 0
  | n + 1 => series s n + s (n + 1)

-- the tail of a sequence a0, a1, a2, ... is the sequence a1, a2, a3, ...
def tail (s: Nat → Real): Nat → Real :=
  fun n => s (n + 1)

-- if S = a0 + a1 + a2 + ... then S - a0 = a1 + a2 + ...
theorem series_tail_subtract (s: Nat → Real) (h: converges (series s) x): converges (tail (series s)) (x - s 0) :=
  sorry

def geometric (r: Real): Nat → Real :=
  fun n => r^n

def geometric_series (r: Real): Nat → Real :=
  series (geometric r)

-- r + r^2 + r^3 + ... = r * (1 + r + r^2 + ...)
theorem geometric_tail (r: Real): tail (series (geometric r)) = fun n => r * (geometric_series r) n := by
  sorry

-- if |r| < 1 then the geometric series is convergent (taken for granted)
theorem geometric_series_convergent (r: Real) (h: |r| < 1): convergent (geometric_series r) := by
  sorry

-- easy lemma about real numbers: if x - 1 = y*x then y = 1/(1 - x)
-- this is pretty ugly...
theorem easy_lemma {x y: Real} (h: y - 1 = x*y): y = (1 - x)⁻¹ := by
  have h: y = x*y + 1 := eq_add_of_sub_eq h
  have h: y = 1 + x*y := by
    rw [add_comm] at h
    exact h
  have h: y   - x*y = 1 := sub_eq_of_eq_add h
  have h: 1*y - x*y = 1 := by
    calc 
      1*y - x*y = y - x*y := by rw [one_mul]
              _ = 1       := h
  have h: (1 - x)*y = 1 := by
    rw [← mul_sub_right_distrib] at h
    exact h
  exact eq_inv_of_mul_eq_one_right h

theorem geometric_series_converges (r: Real) (h: |r| < 1): converges (geometric_series r) (1 - r)⁻¹ := by
  -- let S = 1 + r + r^2 + ...
  obtain ⟨S, hS⟩ := geometric_series_convergent r h
  -- then S - 1 = r + r^2 + ...
  have h1 := series_tail_subtract (geometric r) hS
  simp [geometric] at h1
  rw [geometric_tail r] at h1
  -- also r*S = r + r^2 + ...
  have h2 := converges_mul hS r
  -- by uniqueness of series, r*S = 1 - S
  have h3 := converges_unique h1 h2
  -- therefore S = (1 - r)⁻¹ by lemma
  have h4 := easy_lemma h3
  rw [h4] at hS
  exact hS

/-

A non-constructive existence argument: there exists irrational a,b such that a^b is rational.

Proof: Let x = √2^√2. There are two possibilities:

1. If x is rational, then take a = b = √2. Then a,b are irrational and a^b = x, which is rational.

2. If x is irrational, then take a = x and b = √2. Then a,b are irrational and a^b = (√2^√2)^√2 = √2^2 = 2, which is rational. ▪

See also: Gelfond–Schneider theorem

-/

import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem rational_power: ∃ a b: ℝ, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by
  by_cases h: Irrational (√2^√2)
  . exists √2^√2, √2
    simp_all
    constructor
    . exact irrational_sqrt_two
    . simp [←Real.rpow_mul]
  . exists √2, √2
    simp
    constructor
    . exact irrational_sqrt_two
    . exact h

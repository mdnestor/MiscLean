/-
States (but does not prove) the Kahn-Kalai conjecture https://arxiv.org/abs/2203.17207
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Max
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- imports could probably be pruned
import Mathlib.Topology.ContinuousFunction.Algebra

def increasing_property {X: Type} (F: Finset (Finset X)): Prop :=
  ∀ A B: Finset X, A ⊆ B ∧ A ∈ F → B ∈ F

def trivial_property {X: Type} [Fintype X] [DecidableEq X] (F: Finset (Finset X)): Prop :=
  F = ∅ ∨ Fᶜ = ∅

def product_measure {X: Type} (p: Real) [Fintype X] [DecidableEq X] (A: Finset X): Real := p^(Finset.card A) * (1 - p)^(Finset.card Aᶜ)

def total_measure {X: Type} [Fintype X] [DecidableEq X] (F: Finset (Finset X)) (p: Real): Real :=
  ∑ A ∈ F, product_measure p A

-- total measure is continuous
theorem total_measure_continuous {X: Type} [Fintype X] [DecidableEq X] (F: Finset (Finset X)): Continuous (fun p => total_measure F p) := by
  apply continuous_finset_sum
  intros
  apply Continuous.mul
  apply continuous_pow
  apply Continuous.comp
  apply continuous_pow
  exact Continuous.sub continuous_const continuous_id

-- total measure is strictly increasing in p
-- this needs to be restricted to 0 ≤ p ≤ 1
theorem total_measure_strict_mono {X: Type} [Fintype X] [DecidableEq X] (F: Finset (Finset X)) (h1: increasing_property F): StrictMono (fun p => total_measure F p) := sorry

theorem total_measure_zero {X: Type} [Fintype X] [DecidableEq X] (F: Finset (Finset X)): total_measure F 0 = 0 := by
  sorry

theorem total_measure_one {X: Type} [Fintype X] [DecidableEq X] (F: Finset (Finset X)): total_measure F 1 = 1 := by
  sorry

-- by inverse function theorem

theorem strict_mono_inverse_unique [Preorder X] [Preorder Y] {f: X → Y} (y: Y) (h: StrictMono f): ∃! x: X, f x = y := sorry

def exists_threshold {X: Type} [Fintype X] [DecidableEq X] (F: Finset (Finset X)) (h: increasing_property F): ∃! p: Real, total_measure F p  = 1/2 :=
  strict_mono_inverse_unique (1/2) (total_measure_strict_mono F h)

noncomputable def threshold {X: Type} [Fintype X] [DecidableEq X] (F: Finset (Finset X)) (h: increasing_property F): Real :=
  Classical.choose (exists_threshold F h)

def bar {X: Type} [DecidableEq X] (G: Finset (Finset X)): Finset (Finset X) :=
  Finset.biUnion G (fun S => Finset.filter (fun T => S ⊆ T) G)

def psum {X: Type} (G: Finset (Finset X)) (p: Real): Real :=
  ∑ S ∈ G, p^(Finset.card S)

def psmall {X: Type} [Fintype X] [DecidableEq X] (F: Finset (Finset X)) (p: Real): Prop :=
  ∃ G: Finset (Finset X), F ⊆ bar G ∧ psum G p ≤ 1/2

noncomputable def expectation_threshold {X: Type} [Fintype X] [DecidableEq X] (F: Finset (Finset X)): Real :=
  sSup {p: Real | psmall F p}

noncomputable def largest_min_elt (F: Finset (Finset X)): ℕ :=
  sSup (Set.image Finset.card {A ∈ F | IsMin A})

-- weird phrasing
theorem kahn_kalai {u: Type} [DecidableEq u]: ∃ K: Real, ∀ X: Finset u, ∀ F: Finset (Finset X), Fintype X → increasing_property F → ¬ trivial_property F → threshold F sorry ≤ K * expectation_threshold F * Real.log (max (largest_min_elt F) 2) := by
  sorry

def l_bounded (H: Finset (Finset X)) (l: Nat): Prop :=
  ∀ E ∈ H, E.card ≤ l

/-

A variant of a metric space which consists of

- sets X and D
- a function `dist: X × X → D`

and D is equipped with

- a relation ≤
- an element ⊥ such that ⊥ ≤ d for all d
- a binary operation +

satisfying analogous axioms to a metric space.

-/

import Mathlib.Topology.Order

structure DMetricSpace (X: Type u) (D: Type v) [LE D] [OrderBot D] [Add D] where
  dist: X → X → D
  refl: dist x y = ⊥ ↔ x = y
  symm: dist x y = dist y x
  tri: dist x z ≤ dist x y + dist y z

theorem dist_self [LE D] [OrderBot D] [Add D] (M: DMetricSpace X D) (x: X): M.dist x x = ⊥ :=
  M.refl.mpr rfl

instance: Add Bool := {
  add := Bool.or
}

def DiscreteMetric [DecidableEq X]: DMetricSpace X Bool := {
  dist := fun x y => decide (x ≠ y)
  refl := by simp
  symm := by simp [Eq.comm]
  tri := by
    intros x y z
    by_cases x = y <;> by_cases x = z <;> aesop
}

instance [LE X]: LT X := {
  lt := fun x y => x ≤ y ∧ x ≠ y
}

example [LE D] [OrderBot D] [Add D] (M: DMetricSpace X D): TopologicalSpace X :=
  TopologicalSpace.generateFrom (fun B: Set X => ∃ (x0: X) (r: D), ∀ (x: X), x ∈ B ↔ M.dist x0 x < r)

-- definition of a convergent sequence
def converges [LE D] [OrderBot D] [Add D] (M: DMetricSpace X D) (a: Nat → X) (x: X): Prop :=
  ∀ ε: D, ε ≠ ⊥ → ∃ m: Nat, ∀ n: Nat, m ≤ n → M.dist x (a n) < ε

-- theorem: the constant sequence converges
theorem const_converges [LE D] [OrderBot D] [Add D] (M: DMetricSpace X D) (x: X): converges M (fun _ => x) x := by
  intro _ _
  exists 0
  intros
  rw [dist_self]
  constructor
  simp
  intro h
  rw [Eq.comm] at h
  contradiction

-- theorem: a sequence converges iff. all its tails do
theorem converges_iff_tails_converge [LE D] [OrderBot D] [Add D] (M: DMetricSpace X D) (x: X): converges M a x ↔ ∀ m: Nat, converges M (fun n => a (n + m)) x := by
  constructor
  . intro h m ε hε
    obtain ⟨k, hk⟩ := h ε hε
    exists k
    intro n hn
    apply hk (n + m)
    exact Nat.le_add_right_of_le hn
  . intro h
    specialize h 0
    simp_all

-- todo: category of D-metric spaces?

structure MetricMap1 [LE D] [OrderBot D] [Add D] (M1: DMetricSpace X D) (M2: DMetricSpace Y D) (f: X → Y): Prop where
  main: ∀ x y: X, M2.dist (f x) (f y) ≤ M1.dist x y


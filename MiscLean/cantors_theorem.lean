/-
Cantor's theorem:
Let X be a set and P(X) its power set.
Then any function X → P(X) is non-surjective.

Proof:
- Suppose for a contradiction f is surjective.
- Define S = {x in X | x ∉ f(x)}.
- Since f is surjective, there exists z ∈ S such that f(z) = S.
- Then z ∈ S iff. z ∉ f z by definition.
- Replacing f z with S this yields the contradiction z ∈ S ↔ z ∉ S.

See also: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Logic/Function/Basic.lean
-/

def Set (X: Type) : Type :=
  X → Prop

def surjective {X Y: Type} (f: X → Y) : Prop :=
  ∀ y: Y, ∃ x: X, f x = y

theorem Cantor {X : Type} (f: X → Set X): ¬ surjective f := by
  -- assume by contradiction f is surjective
  apply Not.intro
  intro hf
  -- define S as above
  let S: Set X := fun x => ¬ f x x
  -- since f is surjective, let z be such that f(z) = S
  obtain ⟨z, hz⟩ := hf S
  -- then z ∈ S iff. z ∉ f z
  have hS: S z ↔ ¬ f z z := by rfl
  -- equivalently z ∈ S iff. z ∉ S
  rw [hz] at hS
  -- this is a contradiction by iff_not_self
  exact iff_not_self hS


-- some basic proofs about set fields, sigma fields (sigma algebras) and rings of sets

import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.Countable.Defs

class SigmaField (F: Set (Set X)): Prop where
  compl: A ∈ F → Aᶜ ∈ F
  union: C ⊆ F → Countable C → Set.sUnion C ∈ F

class Field (F: Set (Set X)): Prop where
  compl: A ∈ F → Aᶜ ∈ F
  union: C ⊆ F → Finite C → Set.sUnion C ∈ F

example: SigmaField F → Field F := by
  intro h
  constructor
  . exact h.compl
  . intro _ h1 _
    exact h.union h1 Finite.to_countable

example {F: Set (Set X)} (h0: Finite X): Field F → SigmaField F := by
  intro h
  constructor
  . exact h.compl
  . intro C h1 h2
    have: Finite C := sorry
    apply h.union h1 this

class RingOfSets (F: Set (Set X)): Prop where
  union: C ⊆ F → Finite C → Set.sUnion C ∈ F
  rel_compl: A ∈ F → B ∈ F → A \ B ∈ F

example {F: Set (Set X)} (h0: Set.univ ∈ F): RingOfSets F → Field F := by
  intro h
  constructor
  intro _ hA
  rw [Set.compl_eq_univ_diff]
  exact h.rel_compl h0 hA
  intro C h1 h2
  apply h.union h1 h2

theorem RingOfSets.empty_mem {F: Set (Set X)} (h: RingOfSets F): ∅ ∈ F := by
  have: (∅: Set X) = ⋃₀ ∅ := sorry
  rw [this]
  apply h.union
  apply Set.empty_subset
  sorry

theorem Field.univ_mem {F: Set (Set X)} (h: Field F): Set.univ ∈ F := by
  rw [←Set.compl_empty]
  apply h.compl
  have: (∅: Set X) = ⋃₀ ∅ := sorry
  rw [this]
  apply h.union
  apply Set.empty_subset
  sorry

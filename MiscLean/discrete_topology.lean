-- defines the discrete topology

import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.Finite.Defs

structure TopologicalSpace (X: Type u) where
  opensets: Set (Set X)
  empty_isOpen: ∅ ∈ opensets
  univ_isOpen: Set.univ ∈ opensets
  union_isOpen: ∀ S: Set (Set X), S ⊆ opensets → Set.sUnion S ∈ opensets
  inter_isOpen: ∀ S: Set (Set X), S ⊆ opensets ∧ Finite S → Set.sInter S ∈ opensets

def DiscreteTopology (X: Type u): TopologicalSpace X := {
  opensets := Set.univ
  empty_isOpen := by
    apply Set.mem_univ
  univ_isOpen := by
    apply Set.mem_univ
  union_isOpen := by
    intros
    apply Set.mem_univ
  inter_isOpen := by
    intros
    apply Set.mem_univ
}

def IndiscreteTopology (X: Type u): TopologicalSpace X := {
  opensets := {∅, Set.univ}
  empty_isOpen := by simp
  univ_isOpen := by simp
  union_isOpen := by
    intro S h
    by_cases h': Set.univ ∈ S
    apply Or.inr
    aesop
    apply Or.inl
    -- ⊢ ⋃₀ S = ∅
    -- surprisingly difficult
    sorry
  inter_isOpen := by
    intro S h
    by_cases h': ∅ ∈ S
    apply Or.inl
    aesop
    apply Or.inr
    simp
    -- ⊢ ⋂₀ S = Set.univ
    sorry
}

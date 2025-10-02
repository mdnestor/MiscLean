/-

Topological space

-/


import Mathlib.Data.Set.Finite

class TopologicalSpace (X: Type u) where
  IsOpen: Set X → Prop
  openUnion {S: Set (Set X)}: S ⊆ IsOpen → IsOpen (Set.sUnion S)
  openInter {S: Set (Set X)}: S ⊆ IsOpen → Finite S → IsOpen (Set.sInter S)

open TopologicalSpace

-- the empty set is open
theorem empty_open {X: Type u} [TopologicalSpace X]: IsOpen (∅: Set X) := by
  rw [←Set.sUnion_empty]
  apply openUnion
  simp

-- the universe set is open
theorem univ_open {X: Type u} [TopologicalSpace X]: IsOpen (Set.univ: Set X) := by
  have: @Set.univ X = Set.sInter ∅ := by simp
  rw [this]
  apply openInter
  simp
  exact Set.finite_empty

-- arbitrary unions of open sets are open
theorem open_iUnion {X: Type u} {I: Type v} [TopologicalSpace X] (U: I → Set X)
  (h: ∀ i, IsOpen (U i)): IsOpen (Set.iUnion U) := by
  rw [←Set.sUnion_range]
  apply openUnion
  intro _ h
  obtain ⟨i, hi⟩ := h
  rw [←hi]
  exact h i

-- finite indexed intersections of open sets are open
theorem open_iInter {X: Type u} {I: Type v} [TopologicalSpace X] [Finite I] (U: I → Set X)
  (h: ∀ i, IsOpen (U i)): IsOpen (Set.iInter U) := by  
  rw [←Set.sInter_range]
  apply openInter
  intro _ h
  obtain ⟨i, hi⟩ := h
  rw [←hi]
  exact h i
  apply Set.finite_range

-- the union of a pair of open sets is open
theorem open_union {X: Type u} [TopologicalSpace X] (U V: Set X)
  (hU: IsOpen U) (hV: IsOpen V): IsOpen (U ∪ V) := by
  have: U ∪ V = Set.sUnion {U, V} := by simp
  rw [this]
  apply openUnion
  intro _ hW
  cases hW with
  | inl h =>
    subst h
    exact hU
  | inr h =>
    subst h
    exact hV

-- the intersection of a pair of open sets is open
theorem open_inter {X: Type u} [TopologicalSpace X] (U V: Set X)
  (hU: IsOpen U) (hV: IsOpen V): IsOpen (U ∩ V) := by
  have: U ∩ V = Set.sInter {U, V} := by simp
  rw [this]
  apply openInter
  intro _ hW
  cases hW with
  | inl h =>
    rw [h]
    exact hU
  | inr h =>
    rw [h]
    exact hV
  apply Set.Finite.insert
  simp

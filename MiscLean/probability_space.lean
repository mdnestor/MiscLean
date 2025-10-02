
-- defines a probability space

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Instances.NNReal.Defs

abbrev Set.empty {X: Type u}: Set X :=
  ∅

structure SigmaAlgebra {X: Type u} (F: Set (Set X)) where
  compl: ∀ A, A ∈ F → Aᶜ ∈ F
  union: ∀ C, C ⊆ F → Countable C → Set.sUnion C ∈ F

-- given a type X, produces the discrete sigma algebra on X
def DiscreteSigmaAlgebra (X: Type u): @SigmaAlgebra X Set.univ := {
  compl := by simp
  union := by simp
}

def IndiscreteSigmaAlgebra (X: Type u): @SigmaAlgebra X {∅, ⊤} := {
  compl := by simp
  union := by sorry
}

theorem SigmaAlgebra.empty_mem {X: Type u} {F: Set (Set X)} (h: SigmaAlgebra F): ∅ ∈ F := by
  let C := @Set.empty (Set X)
  rw [←Set.sUnion_empty]
  apply h.union C
  apply Set.empty_subset
  exact Subsingleton.to_countable

theorem SigmaAlgebra.univ_mem {X: Type u} {F: Set (Set X)} (h: SigmaAlgebra F): ⊤ ∈ F := by
  have: ⊤ = (∅ᶜ: Set X) := by simp
  rw [this]
  apply h.compl
  exact empty_mem h

def disjoint (C: Set (Set X)): Prop :=
  ∀ A B, A ∈ C → B ∈ C → A ∩ B = ∅

structure ProbabilitySpace (Ω: Type u) (F: Set (Set Ω)) (P: F → NNReal): Prop where
  sigma_algebra: SigmaAlgebra F
  total_probability: P ⟨Set.univ, SigmaAlgebra.univ_mem sigma_algebra⟩ = 1
  countable_additivity: ∀ C: Set (Set Ω), (h1: C ⊆ F) → (h2: Countable C) → disjoint C → P ⟨Set.sUnion C, sigma_algebra.union C h1 h2⟩ = ∑' E: C, P ⟨E, h1 E.prop⟩


-- a discrete probability space is much simpler
-- it just assigns each outcome a probability
structure DiscreteProbabilitySpace (Ω: Type u) (p: Ω → NNReal): Prop where
  total_probability: ∑' x, p x = 1

-- turn any discrete probability space into a probability space with a discrete sigma algebra
example (Ω: Type u) (p: Ω → NNReal) (h: DiscreteProbabilitySpace Ω p): ProbabilitySpace Ω Set.univ (fun E => ∑' x: E.val, p x) := {
  sigma_algebra := DiscreteSigmaAlgebra Ω
  total_probability := by
    simp [←h.total_probability]
    sorry
  countable_additivity := by
    intro C _ h1 h2
    simp
    sorry
}

-- if a probability space has a discrete sigma algebra, we can turn it into a discrete probability space
example (Ω: Type u) (P: Set.univ → NNReal) (h: ProbabilitySpace Ω Set.univ P): DiscreteProbabilitySpace Ω (fun x: Ω => P ⟨Set.singleton x, trivial⟩) := {
  total_probability := by
    sorry
}


import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas

variable {X: Type} 

class SigmaAlgebra {X: Type} (F: Set (Set X)): Prop where
  univ: Set.univ ∈ F
  compl: ∀ A, A ∈ F → A.compl ∈ F
  countable_union: ∀ A: Nat → Set X, (∀ n, (A n) ∈ F) → Set.iUnion A ∈ F

theorem SigmaAlgebra.empty_mem {X: Type} {F: Set (Set X)} (h: SigmaAlgebra F): ∅ ∈ F := by
  rw [←Set.compl_univ]
  apply h.compl
  exact h.univ

theorem SigmaAlgebra.countable_inter {X: Type} {F: Set (Set X)} (h1: SigmaAlgebra F) {A: Nat → Set X} (h2: ∀ n, (A n) ∈ F): Set.iInter A ∈ F := by
  sorry

theorem SigmaAlgebra.finite_inter {X: Type} {F: Set (Set X)} (h1: SigmaAlgebra F) {I: Finset Nat} {A: I → Set X} (h2: ∀ n, (A n) ∈ F): Set.iInter A ∈ F := by
  sorry

theorem SigmaAlgebra.sInter {X I: Type} (C: Set (Set (Set X))) (h: ∀ F ∈ C, SigmaAlgebra F): SigmaAlgebra (Set.sInter C) := by
  sorry

theorem SigmaAlgebra.iInter {X I: Type} {F: I → Set (Set X)} (h: ∀ i, SigmaAlgebra (F i)): SigmaAlgebra (Set.iInter F) := by
  sorry

def SigmaAlgebra.generate {X: Type} (B: Set (Set X)): Set (Set X) :=
  Set.sInter {F: Set (Set X) | B ⊆ F ∧ SigmaAlgebra F}

theorem SigmaAlgebra.generate_sound {X: Type} (B: Set (Set X)): SigmaAlgebra (SigmaAlgebra.generate B) := by
  sorry

theorem SigmaAlgebra.generate_subset {X: Type} (B: Set (Set X)): B ⊆ SigmaAlgebra.generate B := by
  sorry

def TailAlgebra {X: Type} (F: Nat → Set (Set X)): Set (Set X) :=
  Set.iInter fun n => SigmaAlgebra.generate (Set.iUnion fun m => F (n + m))

theorem TailAlgebra.sigma_algebra {X: Type} (F: Nat → Set (Set X)): SigmaAlgebra (TailAlgebra F) := by
  apply SigmaAlgebra.iInter
  intro
  apply SigmaAlgebra.generate_sound

class Measure {X: Type} {F: Set (Set X)} (h: SigmaAlgebra F) (μ: F → ENNReal): Prop where
  empty: μ ⟨∅, SigmaAlgebra.empty_mem h⟩ = 0 
  union (A: Nat → Set X) (h1: ∀ n: Nat, (A n) ∈ F) (h2: ∀ i j: Nat, i ≠ j → A i ∩ A j = ∅): μ ⟨Set.iUnion A, SigmaAlgebra.countable_union A h1⟩ = tsum (fun n => μ ⟨A n, h1 n⟩)

class ProbMeasure {X: Type} {F: Set (Set X)} (h: SigmaAlgebra F) (μ: F → ENNReal): Prop extends Measure h μ where
  total: μ ⟨Set.univ, SigmaAlgebra.univ⟩ = 1

-- define independence of sigma algebras
def SigmaAlgebra.indep {X: Type} {F: Set (Set X)} {h1: SigmaAlgebra F} {μ: F → ENNReal} (G: Nat → Set (Set X)) (h3: ∀ i, (G i) ⊆ F): Prop :=
  ∀ I: Finset Nat, ∀ A: I → Set X, (h4: ∀ i: I, A i ∈ G i) → μ ⟨Set.iInter A, finite_inter h1 fun n => h3 n (h4 n)⟩ = ∏ i: I, μ ⟨A i, by exact h3 i (h4 i)⟩

theorem SigmaAlgebra.indep_binary {X: Type} {F: Set (Set X)} {h1: SigmaAlgebra F} {μ: F → ENNReal} (G1 G2: Set (Set X)) {A1 A2: Set X} {h3: A1 ∈ G1} {h4: A2 ∈ G2}: μ ⟨A1 ∩ A2, sorry⟩ = μ ⟨A1, sorry⟩ * μ ⟨A2, sorry⟩ := by
  sorry

def SigmaAlgebra.indep' {X: Type} {F: Set (Set X)} (μ: F → ENNReal) (G1 G2: Set (Set X)) (h1: G1 ⊆ F) (h2: G2 ⊆ F): Prop :=
  ∀ A1 A2: Set X, (h3: A1 ∈ G1) → (h4: A2 ∈ G2) → μ ⟨A1 ∩ A2, sorry⟩ = μ ⟨A1, h1 h3⟩ * μ ⟨A2, h2 h4⟩

theorem TailAlgebra.indep {X: Type} (F: Set (Set X)) (μ: F → ENNReal) (G: Nat → Set (Set X)) (h: ∀ n, G n ⊆ F): SigmaAlgebra.indep' μ (TailAlgebra G) (TailAlgebra G) (sorry) (sorry) := by
  sorry

theorem Kolmogorov_zero_one {X: Type} (F: Set (Set X)) (μ: F → ENNReal) (G: Nat → Set (Set X)) (h: ∀ n, G n ⊆ F): ∀ A ∈ TailAlgebra G, (μ ⟨A, sorry⟩)^2 = μ ⟨A, sorry⟩ := by
  intro A hA
  calc
    μ ⟨A, sorry⟩ = μ ⟨A ∩ A, sorry⟩ := by sorry --trivial
    _ = μ ⟨A, sorry⟩ * μ ⟨A, sorry⟩ := by --independence
    _ = μ ⟨A, sorry⟩^2 := by --independence

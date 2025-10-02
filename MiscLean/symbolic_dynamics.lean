/-

Curtis–Hedlund–Lyndon theorem

References

-- "Cellular automata and groups" by Ceccherini-Silberstein and Coornaert (2010)
-- "A note on the definition of sliding block codes and the Curtis-Hedlund-Lyndon Theorem" by Sobottka and Goçcalves (2017) https://arxiv.org/abs/1507.02180
-- "Some notes on the classification of shift spaces: Shifts of Finite Type; Sofic Shifts; and Finitely Defined Shifts" by Sobottka (2020) https://arxiv.org/abs/2010.10595
-- "Symbolic dynamics" on Scholarpedia http://www.scholarpedia.org/article/Symbolic_dynamics

TODO: correct shift space

-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Logic.Function.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.UniformSpace.Pi

-- definition 1.4.1

def local_map {G A B: Type} [Mul G] {S: Set G} (τ: (G → A) → G → B) (μ: (S → A) → B): Prop :=
  ∀ x: G → A, ∀ g: G, τ x g = μ (Set.restrict S (x ∘ (leftMul g)))

def memory_set {G A B: Type} [Mul G] (τ: (G → A) → G → B) (S: Set G): Prop :=
  Finite S ∧ ∃ μ: (S → A) → B, local_map τ μ

def shift_space {M A: Type} [Mul M] [TopologicalSpace A] [DiscreteTopology A] (S: Set (M → A)): Prop :=
  IsClosed S ∧ ∀ x ∈ S, ∀ g: M, x ∘ leftMul g ∈ S

def window {A M: Type} (Λ: Set (M → A)) (N: Set M): Set (N → A) :=
  {w: N → A | ∃ x ∈ Λ, w = Set.restrict N x}

def sliding_block_code {A B M: Type} [Mul M] (Φ: (M → A) → M → B): Prop :=
  ∃ S: Set M, memory_set Φ S

def sliding_block_code_correct {A B M: Type} [Mul M] [TopologicalSpace A] [DiscreteTopology A] {Λ: Set (M → A)} (h: shift_space Λ) (Φ: Λ → M → B): Prop :=
  sorry

-- this is a special case of sliding block code where the input and output alphabets are the same, and the shift space is equal to the whole space
def cellular_automaton {G A: Type} [Mul G] (τ: (G → A) → G → A): Prop :=
  sliding_block_code τ

lemma left_mul_comp {G: Type} [Group G] {g g': G}: leftMul g⁻¹ ∘ leftMul g' = leftMul (g⁻¹ * g') := by
  ext
  simp [leftMul, mul_assoc]

def equivariant {G A B: Type} [Group G] (τ: (G → A) → G → B): Prop := ∀ x: G → A, ∀ g: G, τ (x ∘ (leftMul g⁻¹)) = (τ x) ∘ (leftMul g⁻¹)

theorem shit_continuous {A M: Type} [Mul M] [TopologicalSpace A] [DiscreteTopology A]:
  ∀ g: M, Continuous (fun x: M → A => x ∘ leftMul g) := by
    sorry

theorem shift_uniform_continuous {A M: Type} [Mul M] [UniformSpace A] (h: uniformity A = Filter.principal idRel):
  ∀ g: M, UniformContinuous (fun x: M → A => x ∘ leftMul g) := by
    sorry

-- proposition 1.4.4
theorem sliding_block_equivariant {G A: Type} [Group G] {τ: (G → A) → G → B} (h: sliding_block_code τ): equivariant τ := by
  intro x g
  obtain ⟨S, _, μ, h0⟩ := h
  ext h
  have h1: τ (x ∘ (leftMul g⁻¹)) h = μ (Set.restrict S (x ∘ (leftMul (g⁻¹ * h)))) := by
    rw [h0 (x ∘ leftMul g⁻¹) h]
    rw [Function.comp.assoc]
    rw [left_mul_comp]
  calc
    τ (x ∘ (leftMul g⁻¹)) h = μ (Set.restrict S (x ∘ (leftMul (g⁻¹ * h)))) := by rw [h1]
                          _ = (τ x) (g⁻¹ * h) := by rw [h0 x (g⁻¹ * h)]

-- neighborhood definition of continuity
-- TODO find in mathlib
lemma continuous_of_neighborhood_continuous {X Y: Type} [TopologicalSpace X] [TopologicalSpace Y] {f: X → Y} (h: ∀ x: X, ∀ V ∈ nhds (f x), ∃ U ∈ nhds x, Set.image f U ⊆ V): Continuous f := by
  sorry

-- projection map
def proj {G A: Type} (g: G): (G → A) → A :=
  fun x: G → A => x g

-- every projection map is continuous in prodiscrete topology. this seems to hold even without DiscreteTopology which is sus
theorem proj_continuous {G A: Type} [TopologicalSpace A] [DiscreteTopology A]:
  ∀ g: G, Continuous (proj g: (G → A) → A) := by
  intro g
  exact continuous_apply g

theorem proj_continuous2 {G A: Type} [TopologicalSpace A]:
  ∀ g: G, Continuous (proj g: (G → A) → A) := by
  intro g
  exact continuous_apply g

def cylinder {G A: Type} (g: G) (a: A): Set (G → A) :=
  {x: G → A | x g = a}

theorem cylinder_clopen {G A: Type} [TopologicalSpace A] [DiscreteTopology A]:
  ∀ g: G, ∀ a: A, IsClopen (cylinder g a) := by
  sorry

def V {G A: Type} (x: G → A) (Ω: Set G): Set (G → A) :=
  {y: G → A | Set.EqOn x y Ω}

theorem x_in_V {G A: Type} (x: G → A) (Ω: Set G): x ∈ V x Ω := by
  simp [V, Set.EqOn]

theorem open_contains_is_neighborhood {X: Type} [TopologicalSpace X] {U: Set X} {x: X} (h: IsOpen U) (h2: x ∈ U): U ∈ nhds x := sorry

theorem V_is_open {G A: Type} [TopologicalSpace A] [DiscreteTopology A] (x: G → A) (Ω: Set G): IsOpen (V x Ω) := sorry

theorem V_is_nhd {G A: Type} [TopologicalSpace A] [DiscreteTopology A] (x: G → A) (Ω: Set G):
  V x Ω ∈ nhds x := by
  exact open_contains_is_neighborhood (V_is_open x Ω) (x_in_V x Ω)

-- "Let x: G → A and let W be a neighborhood of τ(x). Then we can find a finite subset Ω ⊆ G such that V(τ(x), Ω) ⊆ W" why..?
theorem lemma1 {G A: Type} [Group G] [TopologicalSpace A] [DiscreteTopology A] {W: Set (G → A)} {x: G → A} (h2: W ∈ nhds x):
  ∃ Ω: Set G, Finite Ω ∧ V x Ω ⊆ W :=
    sorry

def setMul [Monoid G] (A B: Set G) : Set G :=
  (Set.image2 fun x y => x * y) A B

theorem memory_set_eq {G A: Type} [Group G] [TopologicalSpace A] [DiscreteTopology A] {τ: (G → A) → G → A} {S: Set G} (h1: sliding_block_code τ) (h2: memory_set τ S): ∀ x y: G → A, ∀ Ω: Set G, Set.EqOn x y (setMul Ω S) → Set.EqOn (τ x) (τ y) Ω := by
  intro x y Ω h
  let ⟨μ, hμ⟩ := h2
  intro g hg
  sorry

-- proposition 1.4.6
theorem cellular_automata_iff {G A: Type} [Group G] [TopologicalSpace A] [DiscreteTopology A] {τ: (G → A) → G → A} {S: Set G} (hS: Finite S) (μ: (S → A) → A):
  local_map τ μ ↔ equivariant τ ∧ ∀ x: G → A, τ x 1 = μ (Set.restrict S x) := by
  apply Iff.intro
  intro h
  have h1: sliding_block_code τ := by
    rw [sliding_block_code]
    exists S
    apply And.intro
    exact hS
    exists μ
  apply And.intro
  exact sliding_block_equivariant h1
  intro x
  rw [h x 1]
  sorry -- easy
  intro ⟨h1, h2⟩
  intro x g
  calc
    τ x g = τ (x ∘ leftMul g) 1 := by sorry
        _ = μ (S.restrict (x ∘ leftMul g)) := by sorry

-- proposition 1.4.8
theorem sliding_block_code_continuous {G A: Type} [Group G] [TopologicalSpace A] [DiscreteTopology A] {τ: (G → A) → G → A} (h: sliding_block_code τ): Continuous τ := by
  apply continuous_of_neighborhood_continuous
  intro x W hW
  obtain ⟨Ω, hΩ⟩ := lemma1 hW
  let ⟨S, hS⟩ := h
  let ΩS := setMul Ω S
  exists V x ΩS
  apply And.intro
  exact V_is_nhd x ΩS
  have h1: Set.image τ (V x ΩS) ⊆ V (τ x) Ω := by
    intro τy hτy
    simp [V] at hτy
    obtain ⟨y, hy⟩ := hτy
    simp [V, ←hy.2]
    exact memory_set_eq h hS x y Ω hy.1
  exact le_trans h1 hΩ.2

-- definition of a cover
def covers {X I : Type} [TopologicalSpace X] (U: I → Set X) (S: Set X): Prop :=
  ∀ i: I, IsOpen (U i) → S ⊆ ⋃ (i: I), U i

-- curtis hedlund theorem reverse direction
theorem sliding_block_code_of_continuous_and_equivariant {G A: Type} [Group G] [Finite A] [TopologicalSpace A] [DiscreteTopology A] (τ: (G → A) → G → A) (h1: Continuous τ) (h2: equivariant τ): sliding_block_code τ := by
  -- will need eventually: G → A is compact
  have h3: CompactSpace (G → A) := Function.compactSpace
  
  let φ: (G → A) → A := (fun x: G → A => x 1) ∘ τ

  have hφ : Continuous φ := by
    apply Continuous.comp
    exact proj_continuous 1
    exact h1
  
  -- HARD PART

  -- since φ is continuous, we can find for each x a finite subset Ωx such that if y ∈ V(x, Ωx) then τ x 1 = τ y 1... why?
  have h3: ∀ x: G → A, ∃ Ωx: Set G, Finite Ωx ∧ ∀ y: G → A, y ∈ V x Ωx → τ x 1 = τ y 1 := sorry

  have Ω: (G → A) → Set G :=
    fun x => Classical.choose (h3 x)
  

  -- these sets form a cover. since A → G is compact there is a finite subcover
  have h4: ∃ F: Set (G → A), Finite F := sorry -- ∧ covers (fun x: F => V x (Ω x)) Set.univ := sorry
  have F: Set (G → A) := Classical.choose h4
  
  let S := Set.sUnion (Set.image Ω F)
  exists S
  have h5: memory_set τ S := sorry
  exact h5

-- theorem 1.8.1
theorem curtis_hedlund_lyndon {G A: Type} [Group G] [Finite A] [TopologicalSpace A] [DiscreteTopology A] (τ: (G → A) → G → A): sliding_block_code τ ↔ (Continuous τ ∧ equivariant τ) := by
  apply Iff.intro
  exact fun h => ⟨sliding_block_code_continuous h, sliding_block_equivariant h⟩
  exact fun ⟨h1, h2⟩ => sliding_block_code_of_continuous_and_equivariant τ h1 h2

theorem uniform_continuous_of_sliding_block_code {G A: Type} [Group G] [UniformSpace A] {τ: (G → A) → G → A} (h: uniformity A = Filter.principal idRel) (h1: sliding_block_code τ): UniformContinuous τ :=
  sorry

theorem sliding_block_code_of_uniform_continuous_and_equivariant {G A: Type} [Group G] [UniformSpace A] {τ: (G → A) → G → A} (h: uniformity A = Filter.principal idRel) (h1: UniformContinuous τ) (h2:equivariant τ): sliding_block_code τ :=
  sorry

-- drops the finite assumption
theorem curtis_hedlund_lyndon_uniform {G A: Type} [Group G] [UniformSpace A] (h: uniformity A = Filter.principal idRel) (τ: (G → A) → G → A): sliding_block_code τ ↔ (UniformContinuous τ ∧ equivariant τ) := by
  apply Iff.intro
  exact fun h1 => ⟨uniform_continuous_of_sliding_block_code h h1, sliding_block_equivariant h1⟩
  exact fun ⟨h1, h2⟩ => sliding_block_code_of_uniform_continuous_and_equivariant h h1 h2

-- https://en.wikipedia.org/wiki/Arrow's_impossibility_theorem
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite

def transitive (r: A → A → Prop): Prop :=
  ∀ a b c: A, r a b → r b c → r a c
   
def complete (r: A → A → Prop): Prop :=
  ∀ a b: A, r a b ∨ r b a 

def preference (r: A → A → Prop): Prop :=
  transitive r ∧ complete r

def preference_preserving (F: (V → (A → A → Prop)) → (A → A → Prop)): Prop :=
  ∀ p: V → (A → A → Prop), (∀ v: V, preference (p v)) → preference (F p)

def pareto (F: (V → (A → A → Prop)) → (A → A → Prop)): Prop :=
  ∀ p: V → (A → A → Prop), ∀ a b: A, (∀ v: V, p v a b) → F p a b

def decisive_over (F: (V → (A → A → Prop)) → (A → A → Prop)) (S: Set V) (a b: A): Prop :=
  ∀ p: V → (A → A → Prop), (∀ i ∈ S, p i a b) → F p a b

def decisive (F: (V → (A → A → Prop)) → (A → A → Prop)) (S: Set V): Prop :=
  ∀ a b: A, decisive_over F S a b
 
-- if the choice function is Pareto, then the whole set is decisive
theorem decisive_univ (F: (V → (A → A → Prop)) → (A → A → Prop)) (h: pareto F): decisive F Set.univ := by
  intro a b p h1
  simp at h1
  exact h p a b h1

def weak_decisive_over (F: (V → (A → A → Prop)) → (A → A → Prop)) (S: Set V) (a b: A): Prop :=
  ∀ p: V → (A → A → Prop), (∀ i: V, i ∈ S ↔ p i a b) → F p a b

theorem weak_decisive_over_implies_decisive_over (F: (V → (A → A → Prop)) → (A → A → Prop)) (S: Set V) (a b: A)
  (h1: decisive_over F S a b): weak_decisive_over F S a b :=
  fun p h => h1 p (fun i => (h i).mp)

def dictator (F: (V → (A → A → Prop)) → (A → A → Prop)) (i: V): Prop :=
  decisive F {i}

def indep_irrel (F: (V → (A → A → Prop)) → (A → A → Prop)): Prop :=
  ∀ p1 p2: V → (A → A → Prop), ∀ a b: A, (∀ i: V, p1 i a b = p2 i a b) → F p1 a b = F p2 a b

lemma field_expansion {F: (V → (A → A → Prop)) → (A → A → Prop)} {G: Set V} {x y: A} (h1: pareto F) (h2: indep_irrel F) (h3: weak_decisive_over F G x y):
  decisive F G := by
  intro a b p hp
  sorry


-- if a set has ≥2 elements there exists a partition into 2 nonempty subsets
theorem nonempty_partition {X: Type} {S: Set X} (h: Set.encard S ≥ 2): ∃ S1 S2: Set X, S1 ∪ S2 = S ∧ (Disjoint S1 S2) ∧ S1.Nonempty ∧ S2.Nonempty := sorry

theorem nonempty_partition_lemma {X: Type} {S1 S2: Set X} (h1: Disjoint S1 S2): ¬ S1 ⊆ S2 := by
  sorry

theorem disjoint_symm {X: Type} {S1 S2: Set X} (h1: Disjoint S1 S2): Disjoint S2 S1 := by
  simp_all [Disjoint]

-- if a set has ≥3 elements there exist 3 distinct elements 
theorem choose_3_distinct {X: Type} (h: PartENat.card X ≥ 3): ∃ x y z: X, x ≠ y ∧ y ≠ z ∧ z ≠ x := sorry

theorem group_contraction {A V: Type} (F: (V → (A → A → Prop)) → (A → A → Prop)) (G: Set V) (h0: preference_preserving F) (h1: pareto F) (h2: indep_irrel F) (h3: PartENat.card A ≥ 3) (h4: Set.encard G ≥ 2) (h5: decisive F G):
  ∃ T ⊂ G, T.Nonempty ∧ decisive F T := by
  obtain ⟨G1, G2, hGG, hG0, hG1, hG2⟩ := nonempty_partition h4
  obtain ⟨x, y, z, hxy, hyz, hzx⟩ := choose_3_distinct h3

  -- design a voting pattern such that
  -- in G1, z < y < x
  -- in G2, y < x < z
  -- outside them, x < z < y
  have h5: ∃ p: V → (A → A → Prop),
    (∀ v: V, preference (p v)) ∧
    (∀ i ∈ G1, p i z y ∧ p i y x) ∧
    (∀ i ∈ G2, p i y x ∧ p i x z) ∧
    (∀ i ∈ Gᶜ, p i x z ∧ p i z y) := sorry
  obtain ⟨p, hp0, hp1, hp2, hp3⟩ := h5
  have hp := h0 p hp0
  -- since G is decisive, y < x
  have h6: ∀ i ∈ G, p i y x := sorry  
  have h7 := h5 y x p h6
  -- therefore either x > z or z > y... why?
  have h8: F p z x ∨ F p y z := sorry
  cases h8 with
  | inl h9 => {
    -- if z < x then...
    exists G1
    constructor
    rw [ ←  hGG]
    constructor
    exact Set.subset_union_left
    simp
    exact nonempty_partition_lemma (disjoint_symm hG0)
    constructor
    exact hG1
    have h10: weak_decisive_over F G1 x z := sorry
    exact field_expansion h1 h2 h10
  }
  | inr h9 => {
     -- if y < z then...
    exists G2
    constructor
    constructor
    rw [← hGG]
    exact Set.subset_union_right
    rw [← hGG]
    simp
    exact nonempty_partition_lemma hG0
    constructor
    exact hG2
    have h10: weak_decisive_over F G2 x z := sorry
    exact field_expansion h1 h2 h10
  }

-- if S is nonempty and |S| < 2 then S is a singleton
theorem set_singleton_squeeze {X: Type} {S: Set X} (h1: S.Nonempty) (h2: S.encard < 2):
  ∃ x: X, S = {x} := by
  apply Set.encard_eq_one.mp
  apply Eq.symm
  apply le_antisymm
  exact Set.one_le_encard_iff_nonempty.mpr h1
  exact Order.le_of_lt_add_one h2

-- if a property holds true for a finite set
-- and whenever it holds for true for a set of size ≥ b it holds true for a nonempty proper subset
-- then it holds true for a nonempty subset of size <b
theorem descent
  {X : Type} (P: Set X → Prop) (b : ℕ)
  (h1 : ∀ S: Set X, P S ∧ b ≤ Set.encard S → ∃ T : Set X, T.Nonempty ∧ T ⊂ S ∧ P T)
  (h2: ∃ S: Set X, S.Finite ∧ P S):
  ∃ S : Set X, S.Nonempty ∧ P S ∧ Set.encard S < b := by sorry

theorem arrow_impossibility
  {V A: Type} [Finite V] (F: (V → (A → A → Prop)) → (A → A → Prop))
  (h0: ∀ p: V → (A → A → Prop), (∀ v: V, preference (p v)) → preference (F p))
  (h1: pareto F)
  (h2: indep_irrel F)
  (h3: PartENat.card A ≥ 3): ∃ i: V, dictator F i := by
  have h5: ∀ S: Set V, decisive F S ∧ Set.encard S ≥ 2 → ∃ T: Set V, T.Nonempty ∧ T ⊂ S ∧ decisive F T := by
    intro S ⟨hS1, hS2⟩ 
    obtain ⟨T, hT1, hT2, hT3⟩ := group_contraction F S h0 h1 h2 h3 hS2 hS1
    exists T
  have h6: ∃ S: Set V, S.Finite ∧ decisive F S := by
    exists Set.univ
    constructor
    exact Set.finite_univ
    exact decisive_univ F h1
  obtain ⟨U, hU1, hU2, hU3⟩ := descent (fun G: Set V => decisive F G) 2 h5 h6
  obtain ⟨i, hi⟩ := set_singleton_squeeze hU1 hU3
  exists i
  rw [dictator, ←hi]
  exact hU2

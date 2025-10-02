
-- some basic results about filters
-- https://en.wikipedia.org/wiki/Filters_in_topology

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Image

-- definition of a prefilter aka filter base
class PreFilter (F: Set (Set X)): Prop where
  -- the whole set belongs to F
  univ: Set.univ ∈ F
  -- the empty set does not belong to F
  nempty: ∅ ∉ F
  -- if A ∈ F and B ∈ F then A ∩ B ∈ F
  inter_closed: ∀ A B: Set X, A ∈ F → B ∈ F → A ∩ B ∈ F

export PreFilter (univ nempty inter_closed)

-- definition of a filter
class Filter (F: Set (Set X)) extends PreFilter F where
  -- if A ∈ F and A ⊆ B then B ∈ F
  upward_closed: ∀ A B: Set X, A ∈ F → A ⊆ B → B ∈ F

export Filter (upward_closed)

-- the upward closure of a family
def upward_closure (F: Set (Set X)): Set (Set X) :=
  {B: Set X | ∃ A ∈ F, A ⊆ B}

-- every family is contained in its upward closure
theorem upward_closure_contain_self (F: Set (Set X)): F ⊆ upward_closure F := by
  intro A hA
  exists A

-- the upward closure of a prefilter is a prefilter
instance (F: Set (Set X)) [PreFilter F]: PreFilter (upward_closure F) := {
  univ := by
    exists Set.univ
    constructor
    exact univ
    rfl
  nempty := by
    apply Not.intro
    intro h
    obtain ⟨A, hA1, hA2⟩ := h
    have hA3 := Set.eq_empty_of_subset_empty hA2
    rw [hA3] at hA1
    exact nempty hA1
  inter_closed := by
    intro B1 B2 hB1 hB2
    obtain ⟨A1, hA1⟩ := hB1
    obtain ⟨A2, hA2⟩ := hB2
    exists A1 ∩ A2
    constructor
    exact inter_closed A1 A2 hA1.1 hA2.1
    exact Set.inter_subset_inter hA1.2 hA2.2
}

-- the upward closure of a prefilter is a filter
instance (F: Set (Set X)) [PreFilter F]: Filter (upward_closure F) := {
  upward_closed := by
    intro A B hA hAB
    simp_all [upward_closure]
    obtain ⟨U, hU⟩ := hA
    exists U
    constructor
    exact hU.1
    exact le_trans hU.2 hAB
}

-- the neighborhood filter at a point is the upward closure of the set containing the singleton of that point
def neighborhood_filter {X: Type} (x: X): Set (Set X) :=
  upward_closure {{x}}

-- every set in the neighborhood filter on x contains x
theorem neighbors_contain {X: Type} (x: X) {U: Set X} (h: U ∈ neighborhood_filter x): x ∈ U := by
  obtain ⟨V, hV1, hV2⟩ := h
  simp at hV1
  rw [← Set.singleton_subset_iff]
  rw [← hV1]
  exact hV2

-- given a sequence a: Nat → X, the n-th tail set is {a(n), a(n+1), a(n+2), ...} 
def tailset (a: Nat → X) (t: Nat): Set X :=
  Set.image (fun n => a (n + t)) Set.univ

-- given a sequence, the set of all tails
def tailsets (a: Nat → X): Set (Set X) :=
  Set.image (fun t => tailset a t) Set.univ

-- the sequence filter
def sequence_filter (a: Nat → X): Set (Set X) :=
  upward_closure (tailsets a)

-- filter definition of sequence convergence
def converges (a: Nat → X) (x: X): Prop :=
  neighborhood_filter x ⊆ sequence_filter a

-- equivalence to standard definition
theorem converges_iff (a: Nat → X) (x: X): converges a x ↔ ∀ U ∈ neighborhood_filter x, ∃ n: Nat, tailset a n ⊆ U := by
  constructor
  . intro h U hU
    obtain ⟨V, hV1, hV2⟩:= h hU
    obtain ⟨n, hn⟩ := hV1
    exists n
    simp_all
  . intro h U hU
    specialize h U hU
    obtain ⟨t, ht⟩ := h
    exists (tailset a t)
    constructor
    . simp [tailsets]
    . exact ht

theorem tailset_shift (a: Nat → X) (t1 t2: Nat): tailset (fun n => a (n + t1)) t2 = tailset a (t1 + t2) := by
  simp [tailset]
  rw [Nat.add_comm t1 t2]
  ext x
  constructor
  intro hx
  obtain ⟨n, hn⟩ := hx  
  exists n
  simp_all
  rw [← Nat.add_assoc]
  exact hn
  intro hx
  obtain ⟨n, hn⟩ := hx
  exists n
  simp_all
  rw [Nat.add_assoc ]
  exact hn

-- if t1 ≤ t2 then tailset a t1 ⊇ tailset a t2   
theorem tailset_subset (a: Nat → X) {t1 t2: Nat} (h: t1 ≤ t2): tailset a t2 ⊆ tailset a t1 := by
  intro x hx
  simp_all [tailset]
  obtain ⟨n, hn⟩ := hx
  exists n + t2 - t1
  rw [Nat.add_sub_assoc]
  rw [Nat.add_assoc]
  rw [← Nat.sub_add_comm h]
  rw [Nat.add_sub_cancel]
  exact hn
  exact h

-- every constant sequence converges
theorem constant_converges {X: Type} (x: X): converges (fun _ => x) x := by
  intro U hU
  exists {x}
  constructor
  . exists 0
    simp [tailset]
  . rw [Set.singleton_subset_iff]
    exact neighbors_contain x hU

-- a sequence converges iff. all its tails converge
theorem converges_iff_tails_converge (a: Nat → X) (x: X): converges a x ↔ ∀ t: Nat, converges (fun n => a (n + t)) x := by
  constructor
  . intro h t U hU
    simp [sequence_filter, upward_closure, tailsets]
    exists t
    obtain ⟨V, hV⟩ := hU
    sorry
  . intro h
    exact h 0


-- some variations on the definition of a graph

import Mathlib.Data.Set.Basic
import Mathlib.SetTheory.Cardinal.Finite

structure DirSimpleGraph where
  node: Type
  edge: node → node → Prop

open DirSimpleGraph

inductive Path {G: DirSimpleGraph}: G.node → G.node → Type
| nil (x: G.node): Path x x 
| cons {x y z: G.node}: Path x y → G.edge y z → Path x z



structure UndirSimpleGraph where
  node: Type
  edge: node → node → Prop
  symm: ∀ x y: node, edge x y → edge x y

open UndirSimpleGraph

inductive Path2 {G: UndirSimpleGraph}: G.node → G.node → Type
| nil (x: G.node): Path2 x x 
| cons {x y z: G.node}: Path2 x y → G.edge y z → Path2 x z

def swap_path {G: UndirSimpleGraph} {x y: G.node} (p: Path2 x y): Path2 y x :=
  sorry

def UndirSimpleGraph_to_DirSimpleGraph (G: UndirSimpleGraph): DirSimpleGraph := {
  node := G.node
  edge := G.edge
}

def DirSimpleGraph_to_UndirSimpleGraph (G: DirSimpleGraph): UndirSimpleGraph := {
  node := G.node
  edge := fun x y => G.edge x y ∨ G.edge y x
  symm := by intro; simp
}

structure DirNonsimpleGraph where
  node: Type
  edge: Type
  fst: edge → node
  snd: edge → node

structure UndirNonsimpleGraph_v1 where
  node: Type
  edge: Type
  fst: edge → node
  snd: edge → node
  symm: ∀ e: edge, ∃ e': edge, fst e = snd e' ∧ snd e = fst e'

def UnorderedPair (X: Type): Type :=
  @Quotient (X × X) {
    r := by
      intro a b
      exact a = b ∨ a = ⟨b.2, b.1⟩
    iseqv := {
      refl := by
        intro
        simp_all
      symm := by
        intro _ _ h
        match h with
        | Or.inl _ => simp_all
        | Or.inr _ => simp_all
      trans := by
        intro x y z h1 h2
        match h1 with
        | Or.inl _ =>
          match h2 with
          | Or.inl _ => simp_all
          | Or.inr _ => simp_all
        | Or.inr _ =>
          match h2 with
          | Or.inl _ => simp_all
          | Or.inr _ => simp_all
    }
  }

structure Graph5 where
  node: Type
  edge: Type
  bd: edge → UnorderedPair node

def Length2Multiset (X: Type): Type :=
  { s: Multiset X // Multiset.card s = 2 }

def pair_to_length2multiset {X: Type} (x: X × X): Length2Multiset X := ⟨{x.1, x.2}, rfl⟩

noncomputable def length2multiset_to_pair {X: Type} (m: Length2Multiset X): X × X := by
  let L := Multiset.toList m.val
  have hL2 : 2 ≤ L.length := by simp [Multiset.length_toList, le_refl, L]
  exact (L.get ⟨0, by omega⟩, L.get ⟨1, by omega⟩)

structure Graph6 where
  node: Type
  edge: Type
  bd: edge → Multiset node
  cond: ∀ e: edge, Multiset.card (bd e) = 2

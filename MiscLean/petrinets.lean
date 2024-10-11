
-- categories of nets https://arxiv.org/pdf/2101.04238

import Mathlib.Data.Multiset.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

-- definition 4.1
class PreNet where
  specie: Type u
  trans: Type v
  source: trans → List specie
  target: trans → List specie

class PreNet.map (P1 P2: PreNet) where
  smap: P1.specie → P2.specie
  tmap: P1.trans → P2.trans
  h1: (List.map smap) ∘ P1.source = P2.source ∘ tmap
  h2: (List.map smap) ∘ P1.target = P2.target ∘ tmap

def PreNet.id (P: PreNet): PreNet.map P P := {
  smap := fun x => x
  tmap := fun x => x
  h1 := by ext; simp
  h2 := by ext; simp
}

def PreNet.comp {P1 P2 P3: PreNet} (f1: PreNet.map P1 P2) (f2: PreNet.map P2 P3): PreNet.map P1 P3 := {
  smap := f2.smap ∘ f1.smap
  tmap := f2.tmap ∘ f1.tmap
  h1 := by
    rw [←Function.comp.assoc]
    rw [←f2.h1]
    rw [Function.comp.assoc]
    rw [←f1.h1]
    rw [←Function.comp.assoc]
    rw [List.map_comp_map] -- diagram chasing is less fun
  h2 := by
    rw [←Function.comp.assoc]
    rw [←f2.h2]
    rw [Function.comp.assoc]
    rw [←f1.h2]
    rw [←Function.comp.assoc]
    rw [List.map_comp_map]
}

-- prenets form a category
instance: Category PreNet where
  Hom := PreNet.map
  id := PreNet.id
  comp := PreNet.comp
  -- axioms deduced by `aesop_cat` tactic

class PetriNet where
  specie: Type
  trans: Type
  source: trans → Multiset specie
  target: trans → Multiset specie

class PetriNet.map (P1 P2: PetriNet) where
  smap: P1.specie → P2.specie
  tmap: P1.trans → P2.trans
  h1: (Multiset.map smap) ∘ P1.source = P2.source ∘ tmap
  h2: (Multiset.map smap) ∘ P1.target = P2.target ∘ tmap

def PreNet.toPetriNet (P: PreNet): PetriNet := {
  specie := P.specie
  trans := P.trans
  source := Multiset.ofList ∘ P.source
  target := Multiset.ofList ∘ P.target
}

def PetriNet.id (P: PetriNet): PetriNet.map P P := {
  smap := fun x => x
  tmap := fun x => x
  h1 := by ext; simp
  h2 := by ext; simp
}

lemma Multiset.map_comp_map: Multiset.map f ∘ Multiset.map g = Multiset.map (f ∘ g) := by
  ext
  apply map_map

def PetriNet.comp {P1 P2 P3: PetriNet} (f1: PetriNet.map P1 P2) (f2: PetriNet.map P2 P3): PetriNet.map P1 P3 := {
  smap := f2.smap ∘ f1.smap
  tmap := f2.tmap ∘ f1.tmap
  h1 := by
    rw [←Function.comp.assoc]
    rw [←f2.h1]
    rw [Function.comp.assoc]
    rw [←f1.h1]
    rw [←Function.comp.assoc]
    rw [←Multiset.map_comp_map]
  h2 := by
    rw [←Function.comp.assoc]
    rw [←f2.h2]
    rw [Function.comp.assoc]
    rw [←f1.h2]
    rw [←Function.comp.assoc]
    rw [←Multiset.map_comp_map]
}

instance: Category PetriNet where
  Hom := PetriNet.map
  id := PetriNet.id
  comp := PetriNet.comp

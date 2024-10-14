
import Mathlib.Data.Multiset.Basic
import Mathlib.CategoryTheory.Monoidal.Category

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
  h1 := by rw [←Function.comp.assoc, ←f2.h1, Function.comp.assoc, ←f1.h1, ←Function.comp.assoc, List.map_comp_map]
  h2 := by rw [←Function.comp.assoc, ←f2.h2, Function.comp.assoc, ←f1.h2, ←Function.comp.assoc, List.map_comp_map]
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
  h1 := by rw [←Function.comp.assoc, ←f2.h1, Function.comp.assoc, ←f1.h1, ←Function.comp.assoc, ←Multiset.map_comp_map]
  h2 := by rw [←Function.comp.assoc, ←f2.h2, Function.comp.assoc, ←f1.h2, ←Function.comp.assoc, ←Multiset.map_comp_map]
}

def Petri: Category PetriNet where
  Hom := PetriNet.map
  id := PetriNet.id
  comp := PetriNet.comp

structure DepPetriNet where
  specie : Type
  transmatrix : Multiset specie → Multiset specie → Type

/-
axiom Path {P: DepPetriNet} (x y: Multiset P.specie): Type

axiom Path.empty {P: DepPetriNet} (x: Multiset P.specie): Path x x := Path.nil

axiom Path.trans {P: DepPetriNet} {x y: Multiset P.specie} (t : P.transmatrix x y): Path x y :=
  Path.cons t x y

axiom Path.empty {P: DepPetriNet} (x: Multiset P.specie): Path x x

axiom Path.trans {P: DepPetriNet} {x y: Multiset P.specie} (t : P.transmatrix x y): Path x y

axiom Path.compose {P: DepPetriNet} {x y z: Multiset P.specie} (p: Path x y) (q: Path y z): Path x z

axiom Path.sum {P : DepPetriNet} {x x' y y' : Multiset P.specie} (p : Path x y) (q : Path x' y') : Path (Multiset.add x x') (Multiset.add y y')

axiom Path.sum.commutes {P : DepPetriNet}: forall x x' y y': Multiset P.specie, forall p : Path x y, forall p' : Path x' y', Path.sum p p' = Path.sum p' p

axiom Path.interchange {P : DepPetriNet}: forall x x' y y' z z' : Multiset P.specie, forall p : Path x y, forall q: Path y z, forall p' : Path x' y', forall q' : Path y' z', Path.sum (Path.compose p q) (Path.compose p' q') = Path.compose (Path.sum p p') (Path.sum q q')

axiom Path.compose.empty_left {P: DepPetriNet}: forall x y: Multiset P.specie, forall p: Path x y, Path.compose (Path.empty x) p = p

axiom Path.compose.empty_right {P: DepPetriNet}: forall x y: Multiset P.specie, forall p: Path x y, Path.compose p (Path.empty y) = p
-/

inductive Path {P : DepPetriNet}: Multiset P.specie → Multiset P.specie → Type where
  | id (x : Multiset P.specie): Path x x
  | unit (t: P.transmatrix x y): Path x y
  | comp (p: Path x y) (q: Path y z): Path x z
  | tensor (p : Path x1 y1) (q : Path x2 y2): Path (x1 + x2) (y1 + y2)

open CategoryTheory

def FreeGraph (P : DepPetriNet): Category (Multiset P.specie) := {
  Hom := Path
  id := Path.id
  comp := Path.comp
  assoc := sorry
  id_comp := sorry
  comp_id := sorry
}

instance (P: DepPetriNet): Category (Multiset P.specie) := FreeGraph P

example (P: DepPetriNet): MonoidalCategory (Multiset P.specie) := {
  tensorObj := Multiset.add
  whiskerLeft := sorry
  whiskerRight := sorry
  tensorUnit := {}
  associator := sorry
  leftUnitor := sorry
  rightUnitor := sorry
}

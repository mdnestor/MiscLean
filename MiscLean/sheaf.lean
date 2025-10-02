
import Mathlib.Topology.Sets.Opens -- allows us to use the type `Opens X` of open sets
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic

open TopologicalSpace CategoryTheory

-- helpers for working with `Opens`, not sure why these aren't in mathlib
instance (X: Type*) [TopologicalSpace X]: HasSubset (Opens X) := {
  Subset := fun U V => U.carrier ⊆ V.carrier
}

instance (X: Type*) [TopologicalSpace X]: IsTrans (Opens X) fun U V => U ⊆ V := {
  trans := fun _ _ _ h1 h2 _ h3 => h2 (h1 h3)
}

instance (X: Type*) [TopologicalSpace X]: Inter (Opens X) := {
  inter := fun U V => ⟨U.carrier ∩ V.carrier, IsOpen.inter U.is_open' V.is_open'⟩
}

structure Presheaf (X C: Type*) [TopologicalSpace X] [Category C] where
  sect (U: Opens X): C
  res {U V: Opens X} (h: U ⊆ V): sect V ⟶ sect U
  res_refl (U: Opens X): res (subset_refl U.carrier) = 𝟙 (sect U)
  comp {U V W: Opens X} (UV: U ⊆ V) (VW: V ⊆ W): res VW ≫ res UV = res (subset_trans UV VW)

-- simple example of a presheaf: the set of functions U → Y where Y is some type
-- uses the (large) category instance `CategoryTheory.types`
example (X: Type u) (Y: Type v) [TopologicalSpace X]: Presheaf X (Type (max u v)) := {
  sect := fun U => U → Y
  res := fun UV f ⟨x, hx⟩ => f ⟨x, UV hx⟩
  res_refl := by intro; rfl
  comp := by intros; rfl
}

-- define presheaf homomorphism
structure Presheaf.hom {X C: Type*} [TopologicalSpace X] [Category C] (F G: Presheaf X C) where
  map: (U: Opens X) → F.sect U ⟶ G.sect U
  compat: ∀ U V: Opens X, (UV: U ⊆ V) → F.res UV ≫ map U = map V ≫ G.res UV

-- show the identity is a presheaf morphism
def Presheaf.id {X C: Type*} [TopologicalSpace X] [Category C] (F: Presheaf X C): Presheaf.hom F F := {
  map := fun U => 𝟙 (F.sect U)
  compat := by intro; simp
}

-- define composition of presheaf morphisms
def Presheaf.hom_comp {X C: Type*} [TopologicalSpace X] [Category C] {F1 F2 F3: Presheaf X C} (φ1: Presheaf.hom F1 F2) (φ2: Presheaf.hom F2 F3): Presheaf.hom F1 F3 := {
  map := fun U => φ1.map U ≫ φ2.map U
  compat := by
    intro _ _ UV
    simp [←Category.assoc (F1.res UV), φ1.compat, Category.assoc, φ2.compat]
}

-- turns out to talk about individual sections, we need to reference the underlying type of each section
-- so we need to invoke all this ugly code about concrete categogries
-- I only the index of the cover to be universe level 0
structure Sheaf (X C: Type*) [TopologicalSpace X] [Category C] {FC: C → C → Type*} {CC: C → Type*} [(X Y: C) → FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] extends Presheaf X C where
  locality {U: Opens X} {I: Type} {V: I → Opens X} {s t: CC (sect U)}
    (h1: ∀ i, (V i) ⊆ U)
    (h2: U = Set.iUnion (fun i => (V i).carrier))
    (h3: ∀ i, res (h1 i) s = res (h1 i) t): s = t
  gluing {U: Opens X} {I: Type} {V: I → Opens X} {s: (i: I) → CC (sect (V i))}
    (h1: ∀ i, (V i) ⊆ U)
    (h2: U = Set.iUnion (fun i => (V i).carrier))
    (h3: ∀ i j, @res (V i ∩ V j) (V i) (fun _ => Set.mem_of_mem_inter_left) (s i) = @res (V i ∩ V j) (V j) (fun _ => Set.mem_of_mem_inter_right) (s j)):
    ∃ t: CC (sect U), ∀ i, @res (V i) U (fun _ a => h1 i a) t = s i

-- turns out the category of types is not a concrete category (???) so here is another version using the hasforget instance
structure Sheaf2 (X C: Type*) [TopologicalSpace X] [Category C] [HasForget C] extends Presheaf X C where
  locality {U: Opens X} {I: Type} {V: I → Opens X} {s t: (forget C).obj (sect U)}
    (h1: ∀ i, (V i) ⊆ U)
    (h2: U = Set.iUnion (fun i => (V i).carrier))
    (h3: ∀ i, (forget C).map (res (h1 i)) s = (forget C).map (res (h1 i)) t): s = t
  gluing {U: Opens X} {I: Type} {V: I → Opens X} {s: (i: I) → (forget C).obj (sect (V i))}
    (h1: ∀ i, (V i) ⊆ U)
    (h2: U = Set.iUnion (fun i => (V i).carrier))
    (h3: ∀ i j, (forget C).map (@res (V i ∩ V j) (V i) (fun _ => Set.mem_of_mem_inter_left)) (s i) = (forget C).map (@res (V i ∩ V j) (V j) (fun _ => Set.mem_of_mem_inter_right)) (s j)):
    ∃ t: (forget C).obj (sect U), ∀ i, (forget C).map (@res (V i) U (fun _ a => h1 i a)) t = s i

-- show the section obtains by the gluing axioms is unique
theorem Sheaf.glue_unique (X C: Type*) [TopologicalSpace X] [Category C] {FC: C → C → Type*} {CC: C → Type*} [(X Y: C) → FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] (F: Sheaf X C)
  {U: Opens X} {I: Type} {V: I → Opens X} (s: (i: I) → CC (F.sect (V i)))
  (h1: ∀ i, (V i) ⊆ U)
  (h2: U = Set.iUnion (fun i => (V i).carrier))
  (h3: ∀ i j, @F.res (V i ∩ V j) (V i) (fun _ => Set.mem_of_mem_inter_left) (s i) = @F.res (V i ∩ V j) (V j) (fun _ => Set.mem_of_mem_inter_right) (s j)):
  ∃! t: CC (F.sect U), ∀ i, @F.res (V i) U (fun _ a => h1 i a) t = s i := by
  obtain ⟨t, ht⟩ := F.gluing h1 h2 h3
  exists t
  constructor
  . exact ht
  . intro t' ht'
    apply F.locality h1 h2
    intro
    simp_all [Opens.carrier_eq_coe]


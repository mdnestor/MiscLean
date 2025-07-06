
import Mathlib.Topology.Sets.Opens -- allows us to use the type `Opens X` of open sets
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic

open TopologicalSpace CategoryTheory

-- convenient helpers, not sure why these aren't in mathlib
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
  id (U: Opens X): res (subset_refl U.carrier) = 𝟙 (sect U)
  comp {U V W: Opens X} (UV: U ⊆ V) (VW: V ⊆ W): res VW ≫ res UV = res (subset_trans UV VW)

-- turns out to talk about individual sections, we need to reference the underlying type of each section
-- so we need to invoke all this ugly code about concrete categogries
structure Sheaf (X C: Type*) [TopologicalSpace X] [Category C] {FC : C → C → Type*} {CC : C → Type*} [(X Y : C) → FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] extends Presheaf X C where
  locality {U: Opens X} {I: Type w} {V: I → Opens X} (s t: CC (sect U))
    (h1: ∀ i, (V i) ⊆ U)
    (h2: U = Set.iUnion (fun i => (V i).carrier))
    (h3: ∀ i, res (h1 i) s = res (h1 i) t): s = t
  gluing {U: Opens X} {I: Type w} {V: I → Opens X} (s: (i: I) → CC (sect (V i)))
    (h1: ∀ i, (V i) ⊆ U)
    (h2: U = Set.iUnion (fun i => (V i).carrier))
    (h3: ∀ i j, @res (V i ∩ V j) (V i) (fun _ => Set.mem_of_mem_inter_left) (s i) = @res (V i ∩ V j) (V j) (fun _ => Set.mem_of_mem_inter_right) (s j)):
    ∃ t: CC (sect U), ∀ i, @res (V i) U (fun _ a => h1 i a) t = s i


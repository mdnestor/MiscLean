/-
Lawvere's fixed point theorem for Cartesian closed categories

Prior formalizations:
-- In Lean 3 by Matt Diamond (2022): https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/golfing.20Lawvere's.20fixed-point.20theorem
-- In Agda by Martin Escardo (2018): https://www.cs.bham.ac.uk/~mhe/agda-new/LawvereFPT.html

References:
-- "Substructural fixed-point theorems and the diagonal argument: theme and variations" by Roberts (2021): https://arxiv.org/abs/2110.00239
-- "A universal approach to self-referential paradoxes, incompleteness and fixed points" by Yanofsky (2005): https://arxiv.org/abs/math/0305282
-- "Diagonal arguments and cartesian closed categories" by Lawvere (1969): http://tac.mta.ca/tac/reprints/articles/15/tr15.pdf

-- TODO relation between representable and fixed point properties?
-/

import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Closed.Cartesian

-- import Mathlib.Logic.Function.Defs
-- import Mathlib.CategoryTheory.Closed.Types

open CategoryTheory Limits CartesianClosed

@[simp]
def t_point_surjective {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) (t : C) : Prop :=
  ∀ y: t ⟶ Y, ∃ x: t ⟶ X, x ≫ f = y

@[simp]
def point_surjective {C: Type u} [Category.{v} C] [HasTerminal C] {X Y: C} (f: X ⟶ Y) : Prop :=
  t_point_surjective f (⊤_ C)

@[simp]
def weak_point_surjective {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A X Y : C} (g : X ⟶ A ⟹ Y) : Prop :=
  ∀ f : A ⟶ Y, ∃ x : ⊤_ C ⟶ X, ∀ a : ⊤_C ⟶ A, a ≫ prod.lift (𝟙 A) (terminal.from A) ≫ uncurry (x ≫ g) = a ≫ f

@[simp]
def fixed_point {C : Type u} [Category.{v} C] {X t : C} (f : X ⟶ X) (x : t ⟶ X) : Prop :=
  x ≫ f = x

@[simp]
def t_fixed_point_property {C : Type u} [Category.{v} C] (X t : C) : Prop :=
  ∀ f : X ⟶ X, ∃ x : t ⟶ X, fixed_point f x

@[simp]
def fixed_point_property {C : Type u} [Category.{v} C] [HasTerminal C] (X : C) : Prop :=
  t_fixed_point_property X (⊤_ C)

theorem weak_point_surjective_of_point_surjective {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A X Y : C} {g : X ⟶ A ⟹ Y} (h : point_surjective g) : weak_point_surjective g := by
  intro f
  obtain ⟨x, hx⟩ := h (curry ((prod.rightUnitor A).hom ≫ f))
  exists x
  simp [hx]

-- couple useful lemmas
lemma uncurry_decomp {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A X Y : C} (f : X ⟶ A ⟹ Y) (x : ⊤_ C ⟶ X) (a : ⊤_ C ⟶ A) : a ≫ prod.lift (𝟙 A) (terminal.from A) ≫ uncurry (x ≫ f) = prod.lift a x ≫ uncurry f := by
  simp [uncurry_natural_left]
  repeat rw [←Category.assoc]
  simp [eq_whisker]
  rw [←Category.assoc, terminal.hom_ext (a ≫ terminal.from A), Category.id_comp]

lemma uncurry_decomp_diag {C: Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A Y: C} (x: ⊤_ C ⟶ A) (g: A ⟶ A ⟹ Y): x ≫ prod.lift (𝟙 A) (terminal.from A) ≫ uncurry (x ≫ g) = x ≫ diag A ≫ uncurry g := by
    rw [diag, ←Category.assoc x (prod.lift (𝟙 A) (𝟙 A)), prod.comp_lift x (𝟙 A) (𝟙 A), Category.comp_id x]
    exact uncurry_decomp g x x

-- Lawvere's fixed point theorem
theorem lawvere_fixed_point {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A Y : C} {g : A ⟶ A ⟹ Y} (h : weak_point_surjective g) : fixed_point_property Y := by
  intro t
  obtain ⟨x, hx⟩ := h (diag A ≫ uncurry g ≫ t)
  exists x ≫ diag A ≫ uncurry g
  simp [Category.assoc]
  rw [←uncurry_decomp_diag, hx x]

theorem lawvere_diagonal_weak {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A Y : C} (g : A ⟶ A ⟹ Y) (h : ¬ fixed_point_property Y) : ¬ weak_point_surjective g :=
  mt lawvere_fixed_point h

theorem lawvere_diagonal {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A Y : C} (g : A ⟶ A ⟹ Y) (h : ¬ fixed_point_property Y) : ¬ point_surjective g :=
  mt weak_point_surjective_of_point_surjective (lawvere_diagonal_weak g h)

-- Yankofsky (2005) gives a genearlization that does not depend on Cartesian closed, only on binary products and terminal object
-- https://arxiv.org/abs/math/0305282
def representable {C : Type u} [Category.{v} C] [HasTerminal C] {T T' Y : C} [HasBinaryProduct T T'] (f : T ⨯ T' ⟶ Y) (g : T ⟶ Y) : Prop :=
  ∃ t0 : ⊤_C ⟶ T', ∀ t : ⊤_C ⟶ T, t ≫ g = (prod.lift t t0) ≫ f

theorem representable_of_weak_point_surjective {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A X Y: C} {f: X ⟶ A ⟹ Y} (h: weak_point_surjective f): ∀ g: A ⟶ Y, representable (uncurry f) g := by
  intro g
  obtain ⟨t0, ht0⟩ := h g
  exists t0
  intro t
  specialize ht0 t
  rw [←ht0, uncurry_decomp f t0 t]

theorem representable_of_point_surjective {C : Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A X Y: C} {f: X ⟶ A ⟹ Y} (h: weak_point_surjective f): ∀ g: A ⟶ Y, representable (uncurry f) g := by
  sorry

-- Yanofsky's version of Lawvere's fixed point theorem
theorem yanofsky_fixed_point {C: Type u} [Category.{v} C] [HasTerminal C] {Y T S: C} [HasBinaryProduct T S] {β: T ⟶ S} {f: T ⨯ S ⟶ Y}
  (h1: ∀ g: T ⟶ Y, representable f g) (h2: IsSplitEpi β): fixed_point_property Y := by
  intro σ
  specialize h1 ((prod.lift (𝟙 T) β) ≫ f ≫ σ)
  obtain ⟨t, ht⟩ := h1
  obtain ⟨βbar, hβ⟩ := h2
  exists t ≫ (prod.lift βbar (𝟙 S)) ≫ f
  simp
  specialize ht (t ≫ βbar)
  simp at ht
  calc
    t ≫ prod.lift βbar (𝟙 S) ≫ f ≫ σ = t ≫ prod.lift βbar (βbar ≫ β) ≫ f ≫ σ := by rw [hβ]
                                   _ = t ≫ prod.lift (βbar ≫ (𝟙 T)) (βbar ≫ β) ≫ f ≫ σ := by rw [Category.comp_id]
                                   _ = t ≫ (βbar ≫ prod.lift (𝟙 T) β) ≫ f ≫ σ := by rw [prod.comp_lift]
                                   _ = t ≫ βbar ≫ prod.lift (𝟙 T) β ≫ f ≫ σ := by rw [Category.assoc]
                                   _ = prod.lift (t ≫ βbar) t ≫ f := ht
                                   _ = prod.lift (t ≫ βbar) (t ≫ (𝟙 S)) ≫ f := by rw [Category.comp_id]
                                   _ = t ≫ prod.lift βbar (𝟙 S) ≫ f := by rw [←Category.assoc, prod.comp_lift]


theorem lawvere_fixed_point.proof2 {C: Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A Y: C} {g: A ⟶ A ⟹ Y} (h: weak_point_surjective g): fixed_point_property Y :=
  yanofsky_fixed_point (representable_of_weak_point_surjective h) (IsSplitEpi.of_iso (𝟙 A))

-- theorem 14 in Roberts (2023)
-- https://arxiv.org/pdf/2110.00239
theorem magmoidal_fixed_point {C: Type u} [Category.{v} C] {A B t: C}
  {H: Functor (C × C) C}
  {δ: NatTrans (𝟭 C) (Functor.diag C ⋙ H)}
  {F: H.obj (A, A) ⟶ B}
  {σ: B ⟶ B} {a0: t ⟶ A}
  (h: ∀ a: t ⟶ A, a ≫ (δ.app A) ≫ F ≫ σ = (δ.app t) ≫ (H.map ((a0, a): (t, t) ⟶ (A, A))) ≫ F):
    ∃ b: t ⟶ B, fixed_point σ b := by
  exists a0 ≫ (δ.app A) ≫ F
  simp [h a0]
  have := δ.naturality a0
  have hδ: a0 ≫ δ.app A = δ.app t ≫ H.map ((a0, a0): (t, t) ⟶ (A, A)) := by simpa
  simp [←Category.assoc, eq_whisker hδ F]


theorem lawvere_fixed_point.proof3 {C: Type u} [Category.{v} C] [HasFiniteProducts C] [CartesianClosed C] {A Y: C} {g: A ⟶ A ⟹ Y} (h: weak_point_surjective g): fixed_point_property Y := by
  let H: Functor (C × C) C := uncurry.obj prod.functor
  let δ: NatTrans (𝟭 C) (Functor.diag C ⋙ H) := {
    app := fun X => diag X
    naturality := by simp [H]
  }
  let F: H.obj (A, A) ⟶ Y := by
    simp [H]
    exact uncurry g
  intro σ
  simp at h
  obtain ⟨a0, ha0⟩ := h (diag A ≫ F ≫ σ)
  have h1: ∀ a: ⊤_ C ⟶ A, a ≫ (δ.app A) ≫ F ≫ σ = (δ.app (⊤_ C)) ≫ (H.map ((a0, a): (⊤_ C, ⊤_ C) ⟶ (A, A))) ≫ F := by
    intro a
    simp [H]
    have h2: prod.lift a0 a ≫ F = a ≫ prod.lift (𝟙 A) (terminal.from A) ≫ CartesianClosed.uncurry (a0 ≫ g) := by
      simp [F, uncurry_decomp g a0 a]
      sorry -- why is order flipped ??
    rw [← ha0 a, h2] 
  exact magmoidal_fixed_point h1

-- theorem 15 in Roberts (2023)
theorem magmoidal_fixed_point_yanofsky {C: Type u} [Category.{v} C] {A A' B t: C}
  {H: Functor (C × C) C}
  {δ: NatTrans (𝟭 C) (Functor.diag C ⋙ H)}
  {F: H.obj (A, A') ⟶ B}
  {σ: B ⟶ B} {a: t ⟶ A} {p: A' ⟶ A}
  (h1: ∀ a': t ⟶ A', a' ≫ δ.app A' ≫ (H.map ((p, 𝟙 A'): (A', A') ⟶ (A, A'))) ≫ F ≫ σ = δ.app t ≫ (H.map ((a, a'): (t, t) ⟶ (A, A'))) ≫ F)
  (h2: t_point_surjective p t):
    ∃ b: t ⟶ B, fixed_point σ b := by
  obtain ⟨l, hl⟩ := h2 a
  exists l ≫ (δ.app A') ≫ (H.map ((p, 𝟙 A'): (A', A') ⟶ (A, A'))) ≫ F
  simp [h1 l]
  have h3: (H.map ((a, l): (t, t) ⟶ (A, A'))) = (H.map ((l, l): (t, t) ⟶ (A', A'))) ≫ (H.map ((p, 𝟙 A'): (A', A') ⟶ (A, A'))) := by
    simp [←Functor.map_comp, hl]
  have := δ.naturality l
  have h4: l ≫ (δ.app A') = (δ.app t) ≫ (H.map ((l, l): (t, t) ⟶ (A', A'))) := by simpa
  simp [h3, ←Category.assoc, h4]

theorem magmoidal_fixed_point.proof2 {C: Type u} [Category.{v} C] {A B t: C}
  {H: Functor (C × C) C}
  {δ: NatTrans (𝟭 C) (Functor.diag C ⋙ H)}
  {F: H.obj (A, A) ⟶ B}
  {σ: B ⟶ B} {a0: t ⟶ A}
  (h: ∀ a: t ⟶ A, a ≫ (δ.app A) ≫ F ≫ σ = (δ.app t) ≫ (H.map ((a0, a): (t, t) ⟶ (A, A))) ≫ F):
    ∃ b: t ⟶ B, b ≫ σ = b := by
  have h1: ∀ a: t ⟶ A, a ≫ δ.app A ≫ (H.map ((𝟙 A, 𝟙 A): (A, A) ⟶ (A, A))) ≫ F ≫ σ = δ.app t ≫ (H.map ((a0, a): (t, t) ⟶ (A, A))) ≫ F := by
    rw [← CategoryTheory.prod_id]
    have h2: (H.map ((𝟙 A, 𝟙 A): (A, A) ⟶ (A, A))) = 𝟙 (H.obj (A, A)) := by
      rw [← CategoryTheory.prod_id]
      rw [CategoryTheory.Functor.map_id]
    simp [h2]
    exact h
  exact magmoidal_fixed_point_yanofsky h1 (by simp)



-- epilogue: taking the category of types as a special case yields Cantor's theorem
/-
theorem surjective_iff_point_surjective {X Y: Type u} {f: X → Y}: Function.Surjective f ↔ point_surjective (↾f) := by
  apply Iff.intro
  intro h yhom
  let y := (Types.terminalIso.inv ≫ yhom) PUnit.unit
  obtain ⟨x, hx⟩ := h y
  let xhom := Types.terminalIso.hom ≫ homOfElement x
  exists Types.terminalIso.hom ≫ homOfElement x
  sorry
  intro h y
  let yhom := Types.terminalIso.hom ≫ homOfElement y
  obtain ⟨xhom, hx⟩ := h yhom
  exists (Types.terminalIso.inv ≫ xhom) PUnit.unit
  rw [←types_comp_apply (Types.terminalIso.inv ≫ xhom) f, Category.assoc, hx]
  rfl

theorem prop_fixed_point_property_false: ¬ fixed_point_property Prop := by
  simp
  exists Not
  intro h
  -- obtain ⟨y, hy⟩ := h -- hy: y ≫ Not = y
  sorry

-- Cantor's theorem for types
theorem no_surjective_to_powerset {X: Type} (f: X → Set X): ¬ Function.Surjective f := by
  -- interpret f as a map X ⟶ X ⟹ Prop
  -- then show that ∃ t: Prop ⟶ Prop, ∀ y: ⊤_ C ⟶ Prop, y ≫ t ≠ y, i.e. that Prop does NOT have the fixed point property
  rw [Set] at f
  have f_uncurried: X ⟶ X ⟹ Prop := sorry
  have h1 := prop_fixed_point_property_false
  have h2 := diagonal h1
  specialize h2 X f_uncurried
  have h4 := weak_point_surjective_of_point_surjective.mt h2
  have h5 := (Iff.not surjective_iff_point_surjective).mp h4
  sorry
-/

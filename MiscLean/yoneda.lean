
import Mathlib.Tactic


namespace CatTheory

structure Cat.{u, v} where
  obj: Type u
  hom: obj → obj → Type v
  id (x: obj): hom x x
  comp {x y z: obj} (f: hom x y) (g: hom y z): hom x z
  id_left: ∀ {x y: obj}, ∀ f: hom x y, comp (id x) f = f
  id_right: ∀ {x y: obj}, ∀ f: hom x y, comp f (id y) = f
  assoc: ∀ {x y z W: obj}, ∀ f: hom x y, ∀ g: hom y z, ∀ h: hom z W,
    comp (comp f g) h = comp f (comp g h)

def Cat.op (C: Cat): Cat := {
  obj := C.obj
  hom := λ x y ↦ C.hom y x
  id := λ x ↦ C.id x
  comp := λ f g ↦ C.comp g f
  id_left := C.id_right
  id_right := C.id_left
  assoc := λ f g h => Eq.symm (C.assoc h g f)
}

def mono {C: Cat} {x y: C.obj} (f: C.hom x y): Prop :=
  ∀ W: C.obj, ∀ e₁ e₂: C.hom W x,
    C.comp e₁ f = C.comp e₂ f → e₁ = e₂

def epi {C: Cat} {x y: C.obj} (f: C.hom x y): Prop :=
  @mono (C.op) y x f

def iso {C: Cat} {x y: C.obj} (f: C.hom x y): Prop :=
  mono f ∧ epi f

theorem mono_if {C: Cat} {x y: C.obj} {f: C.hom x y} (g: C.hom y x) (h: C.comp f g = C.id x): mono f := by
  intro _ e₁ e₂ h₂
  rw [←C.id_right e₁, ←h, ←C.assoc, h₂, C.assoc, h, C.id_right]

theorem epi_if {C: Cat} {x y: C.obj} {f: C.hom x y} (g: C.hom y x) (h: C.comp g f = C.id y): epi f := by
  exact mono_if _ h

@[simp]
def Set: Cat.{u + 1} := {
  obj := Type u
  hom := λ x y ↦ x → y
  id := λ _ ↦ id
  comp := λ f g ↦ g ∘ f
  id_left := by intros; rfl
  id_right := by intros; rfl
  assoc := by intros; rfl
}

theorem set_mono {x y: Set.obj} {f: Set.hom x y}: mono f ↔ Function.Injective f := by
  sorry

theorem set_epi {x y: Set.obj} {f: Set.hom x y}: epi f ↔ Function.Surjective f := by
  sorry

def Product (C D: Cat): Cat := {
  obj := C.obj × D.obj
  hom := λ x y ↦ C.hom x.1 y.1 × D.hom x.2 y.2
  id := λ x ↦ (C.id x.1, D.id x.2)
  comp := by
    intro x y z f g
    exact (C.comp f.1 g.1, D.comp f.2 g.2)
  id_left := by
    intros
    ext
    apply C.id_left
    apply D.id_left
  id_right := by
    intros
    ext
    apply C.id_right
    apply D.id_right
  assoc := by
    intros
    ext
    apply C.assoc
    apply D.assoc
}

structure Functor (C D: Cat) where
  obj: C.obj → D.obj
  hom {x y: C.obj}: C.hom x y → D.hom (obj x) (obj y)
  id_preserve: ∀ x, hom (C.id x) = D.id (obj x)
  comp_preserve: ∀ x y z, ∀ f: C.hom x y, ∀ g: C.hom y z,
    hom (C.comp f g) = D.comp (hom f) (hom g)

def Functor.id (C: Cat): Functor C C := {
  obj := λ x ↦ x
  hom := λ f ↦ f
  id_preserve := by intros; rfl
  comp_preserve := by intros; rfl
}

def Functor.comp {C D E: Cat} (F: Functor C D) (G: Functor D E): Functor C E := {
  obj := G.obj ∘ F.obj
  hom := G.hom ∘ F.hom
  id_preserve := by simp [F.id_preserve, G.id_preserve]
  comp_preserve := by simp [F.comp_preserve, G.comp_preserve]
}

-- (u+1)-Cat of u-Categories
example: Cat.{u + 1} := {
  obj := Cat.{u}
  hom := Functor
  id := Functor.id
  comp := Functor.comp
  id_left := by intros; rfl
  id_right := by intros; rfl
  assoc := by intros; rfl
}

-- natural transformation bewteen functors
structure NatTrans {C D: Cat} (F G: Functor C D) where
  component (x: C.obj): D.hom (F.obj x) (G.obj x)
  commute: ∀ x y: C.obj, ∀ f: C.hom x y,
    D.comp (F.hom f) (component y) = D.comp (component x) (G.hom f)

def NatTrans.id {C D: Cat} (F: Functor C D):
  NatTrans F F := {
  component := fun x => D.id (F.obj x)
  commute := by
    intros
    repeat rw [←F.id_preserve]
    repeat rw [←F.comp_preserve]
    rw [C.id_left, C.id_right]
}

def NatTrans.comp {C D: Cat} {F G H: Functor C D}
  (η: NatTrans F G) (ε: NatTrans G H):
  NatTrans F H := {
  component := fun x => D.comp (η.component x) (ε.component x)
  commute := by
    intro x y f
    sorry
}

def FunctorCat (C D: Cat): Cat := {
  obj := Functor C D
  hom := NatTrans
  id := NatTrans.id
  comp := NatTrans.comp
  id_left := by
    intros
    simp [NatTrans.comp]
    congr
    ext
    apply D.id_left
  id_right := by
    intros
    simp [NatTrans.comp]
    congr
    ext
    apply D.id_right
  assoc := by
    intros
    simp [NatTrans.comp]
    ext
    apply D.assoc
}

def NatIso {C D: Cat} {F G: Functor C D} (η: NatTrans F G): Prop :=
  @iso (FunctorCat C D) F G η

-- https://proofwiki.org/wiki/Equivalence_of_Definitions_of_Natural_Isomorphism_between_Covariant_Functors
theorem NatTrans.iso_iff {C D: Cat} {F G: Functor C D} {η: NatTrans F G}: NatIso η ↔ ∀ x, iso (η.component x) := by
  sorry

-- hom functor
def Functor.homFunctor (C: Cat): Functor (Product C.op C) Set := {
  obj := λ x ↦ C.hom x.1 x.2
  hom := λ f q ↦ C.comp (C.comp f.1 q) f.2
  id_preserve := by
    intro (_, _)
    simp [Product, Set]
    ext f
    simp [C.id_right]
    exact C.id_left f
  comp_preserve := by
    intros _ _ _ f g
    simp_all [Set]
    ext q
    simp [C.assoc]
    exact C.assoc g.fst f.fst (C.comp q (C.comp f.snd g.snd))
}

def Functor.left_inj (C D: Cat) (A: C.obj): Functor D (Product C D) := {
  obj := λ B ↦ (A, B)
  hom := λ f ↦ (C.id A, f)
  id_preserve := by intro; rfl
  comp_preserve := by simp [Product, C.id_left]
}

def Functor.right_inj (C D: Cat) (B: D.obj): Functor C (Product C D) := {
  obj := λ A ↦ (A, B)
  hom := λ f ↦ (f, D.id B)
  id_preserve := by intro; rfl
  comp_preserve := by simp [Product, D.id_right]
}

def Functor.repr {C: Cat} (A: C.obj): Functor C.op Set :=
  comp (right_inj C.op C A) (homFunctor C)

def Functor.corepr {C: Cat} (A: C.obj): Functor C Set :=
  comp (left_inj C.op C A) (homFunctor C)

@[simp] theorem corepr_obj (C : Cat) (B x : C.obj) :
  (Functor.corepr (C:=C) B).obj x = C.hom B x := rfl

@[simp] theorem corepr_hom (C : Cat) (B : C.obj) {x y : C.obj}
  (h : C.hom x y) (g : C.hom B x) :
  (Functor.corepr (C:=C) B).hom h g = C.comp g h := by
  simp [Functor.corepr, Functor.comp, Functor.left_inj, Functor.homFunctor]
  have: C.comp (C.op.id B) g = g := by exact C.id_left g
  rw [this]

def Functor.corepr_precompose {C : Cat} {A B : C.obj} (f : C.hom A B) :
  NatTrans (corepr B) (corepr A) := {
  component := fun x g => C.comp f g
  commute := by
    intros
    funext
    simp [C.assoc]
}

def yoneda.LHS (C: Cat): Functor (Product C (FunctorCat C Set)) Set := {
  obj := λ x ↦ NatTrans (Functor.corepr x.1) x.2
  hom := λ x ε ↦ NatTrans.comp (NatTrans.comp (Functor.corepr_precompose x.1) ε) x.2
  id_preserve := by
    intro
    funext
    simp [Product, FunctorCat, NatTrans.comp]
    congr
    ext _ f
    simp [NatTrans.id, Functor.corepr_precompose]
    rw [C.id_left f]
  comp_preserve := by
    intros
    simp [Product, Functor.corepr_precompose, C.assoc]
    rfl
}

def yoneda.RHS (C: Cat): Functor (Product C (FunctorCat C Set)) Set := {
  obj := λ (A, F) ↦ F.obj A
  hom := by
    intro (_, F) _ (f, η) ε
    exact η.component _ (F.hom f ε)
  id_preserve := by
    intro (A, F)
    simp [Product, Functor.id_preserve]
    rfl
  comp_preserve := by
    intro (A, F) (B, _) (C', _) (f₁, η₁) (f₂, η₂)
    funext ε
    simp [Product]
    have h := congrArg (fun k => k (F.hom f₁ ε)) (η₁.commute B C' f₂)
    have hF: F.hom (C.comp f₁ f₂) ε = F.hom f₂ (F.hom f₁ ε) := by
      have := F.comp_preserve A B C' f₁ f₂
      simpa [Set] using congrArg (fun k => k ε) this
    simp [hF]
    exact congrArg (fun t => η₂.component C' t) h
}

def yoneda.NatTransLeft (C: Cat): NatTrans (yoneda.LHS C) (yoneda.RHS C) := {
  component := by
    intro (A, F)
    simp [yoneda.RHS]
    intro η
    exact η.component A (C.id A)
  commute := by
    intro (x, F) (y, G) ⟨f, η⟩
    simp [Set, yoneda.LHS, Functor.corepr]
    ext ε
    simp [Functor.corepr_precompose, NatTrans.comp]
    rw [C.id_right]
    have hε : ε.component y f = F.hom f (ε.component x (C.id x)) := by
      have h := congrFun (ε.commute x y f) (C.id x)
      simp [Function.comp] at h
      sorry -- rw [C.id_left] at h
      -- sorry -- exact h
    exact congrArg (η.component y) hε
}

theorem Yoneda (C: Cat): NatIso (yoneda.NatTransLeft C) := by
  apply NatTrans.iso_iff.mpr
  intro (A, F)
  let g: F.obj A → NatTrans (Functor.corepr A) F := fun a ↦ {
  component := λ _ f ↦ (F.hom f) a
  commute := by
    intros
    simp [Set, Functor.corepr]
    ext
    simp [F.comp_preserve]
    sorry -- rfl
  }
  constructor
  apply mono_if g
  funext η
  simp [yoneda.NatTransLeft, Set, g]
  congr
  ext _ f
  have := congrFun (η.commute _ _ f) (C.id A)
  simp_all [Set, Functor.corepr]
  sorry
  sorry
  -- rw [←this, C.id_left]
  -- apply epi_if g
  -- funext
  -- simp [g, Set, yoneda.NatTransLeft, F.id_preserve]

def yoneda.embedding (C: Cat): Functor C (FunctorCat C.op Set) := {
  obj := λ A ↦ Functor.corepr A
  hom := λ f ↦ Functor.corepr_precompose f
  id_preserve := by
    intro
    simp [Functor.corepr]
    congr
    sorry -- apply C.op.id_left
  comp_preserve := by
    intros
    simp [Functor.corepr]
    congr
    sorry -- ext
    -- apply C.op.assoc
}

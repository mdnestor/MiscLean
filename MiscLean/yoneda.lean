
import Aesop.Main

structure Category (m n: Nat) where
  obj: Type m
  hom (x y: obj) : Type n
  id (a: obj): hom a a
  comp (f: hom a b) (g: hom b c): hom a c
  id_comp (f: hom a b): comp (id a) f = f
  comp_id (f: hom a b): comp f (id b) = f
  assoc: comp f (comp g h) = comp (comp f g) h

structure functor (C D: Category m n) where
  func0: C.obj → D.obj
  func1: C.hom x y → D.hom (func0 x) (func0 y)
  id_preserving: func1 (C.id x) = D.id (func0 x)
  comp_preserving: func1 (C.comp f g) = D.comp (func1 f) (func1 g)

@[ext]
structure NatTrans {C D: Category m n} (F G: functor C D) where
  component (x: C.obj): D.hom (F.func0 x) (G.func0 x)
  ok (f: C.hom x y): D.comp (F.func1 f) (component y) = D.comp (component x) (G.func1 f)

def NatTrans.id {C D: Category m n} (F: functor C D): NatTrans F F := {
  component := fun x => D.id (F.func0 x)
  ok := by
    intros
    rw [D.comp_id, D.id_comp]
}

def NatTrans.comp {C D: Category m n} {F G H: functor C D} (η: NatTrans F G) (μ: NatTrans G H): NatTrans F H := {
  component := fun x => D.comp (η.component x) (μ.component x)
  ok := by
    intros
    rw [D.assoc, η.ok, ←D.assoc, μ.ok, D.assoc]
}

def Set: Category 1 1 := {
  obj := Type,
  hom := fun x y => (x → y)
  id := @id
  comp := fun f g x => g (f x)
  id_comp := by simp
  comp_id := by simp
  assoc := by simp
}

def HomSet {C: Category m n} (x y: C.obj): Type n := C.hom x y

def HomFunctor (C: Category 1 1) (A: C.obj): functor C Set := {
  func0 := HomSet A
  func1 := fun f g => C.comp g f
  id_preserving := by
    intro
    simp [Set]
    ext
    rw [C.comp_id]
    rfl
  comp_preserving := by
    intros
    simp [Set]
    ext
    apply C.assoc
}

-- product Category
def prodCategory (C D: Category m n): Category m n := {
  obj := C.obj × D.obj
  hom := fun x y => (C.hom x.1 y.1) × (D.hom x.2 y.2)
  id := fun x => ⟨C.id x.1, D.id x.2⟩
  comp := fun f g => ⟨C.comp f.1 g.1, D.comp f.2 g.2⟩
  id_comp := by simp [C.id_comp, D.id_comp]
  comp_id := by simp [C.comp_id, D.comp_id]
  assoc := by simp [C.assoc, D.assoc]
}

-- the exponential Category
-- given Categories C and D, this is the Category of functors C → D
def expCategory (C D: Category m n): Category m n := {
  obj := functor C D
  hom := NatTrans
  id := NatTrans.id
  comp := NatTrans.comp
  id_comp := by simp [NatTrans.comp, NatTrans.id, D.id_comp]
  comp_id := by simp [NatTrans.comp, NatTrans.id, D.comp_id]
  assoc := by simp [NatTrans.comp, D.assoc]
}

def monomorphism {C: Category m n} {X Y: C.obj} (f: C.hom X Y): Prop :=
  ∀ Z: C.obj, ∀ g1 g2: C.hom Y Z, C.comp f g1 = C.comp f g2 → g1 = g2

def epimorphism {C: Category m n} {X Y: C.obj} (f: C.hom X Y): Prop :=
  ∀ W: C.obj, ∀ g1 g2: C.hom W X, C.comp g1 f = C.comp g2 f → g1 = g2

def isomorphism {C: Category m n} {X Y: C.obj} (f: C.hom X Y): Prop :=
  monomorphism f ∧ epimorphism f

def isomorphic {C: Category m n} (X Y: C.obj): Prop :=
  ∃ f: C.hom X Y, isomorphism f

def functor_isomorphic {C D: Category m n} (f g: functor C D): Prop :=
  @isomorphic m n (expCategory C D) f g

def YonedaLeft (C: Category 1 1): functor (prodCategory C (expCategory C Set)) Set := {
  func0 := fun ⟨x1, x2⟩ => NatTrans (HomFunctor C x1) x2
  func1 := fun f η => {
      component := fun x h => (f.2.component x) ((η.component x) (C.comp f.1 h))
      ok := by
        intro a b g
        simp [HomFunctor, Set]
        ext S
        sorry
  }
  id_preserving := by
    intro
    simp [Set]
    ext η
    simp
    sorry
  comp_preserving := by
    intros
    simp
    sorry
}

def YonedaRight (C: Category 1 1): functor (prodCategory C (expCategory C Set)) Set := {
  func0 := fun ⟨A, F⟩ => F.func0 A
  func1 := by
    intro x y f
    simp
    sorry
  id_preserving := by
    intro x
    simp
    sorry
  comp_preserving := by
    intros
    simp
    sorry
}

theorem Yoneda (C: Category 1 1): functor_isomorphic (YonedaLeft C) (YonedaRight C) := by
  sorry

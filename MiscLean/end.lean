/-

Formalizing ends and coends

Given a functor F: C^op x C → D,
- An end is an object e of X equipped with a universal extranatural transformation from e to F.
- Equivalently, an end is a universal dinatural transformation from an object e of X to F.

References:
- nLab
- https://golem.ph.utexas.edu/Categoryegory/2014/01/ends.html

-/

structure Category where
  obj: Type
  hom: obj → obj → Type
  id (a: obj): hom a a
  comp (f: hom a b) (g: hom b c): hom a c
  id_left: ∀ a b: obj, ∀ f: hom a b, f = comp (id a) f
  id_right: ∀ a b: obj, ∀ f: hom a b, f = comp f (id b)
  assoc: ∀ a b c d: obj, ∀ f: hom a b, ∀ g: hom b c, ∀ h: hom c d, comp f (comp g h) = comp (comp f g) h

def opposite (C: Category): Category := {
  obj := C.obj
  hom := fun x y => C.hom y x
  id := C.id
  comp := by intro _ _ _ f g; exact C.comp g f
  id_left := by intros; apply C.id_right
  id_right := by intros; apply C.id_left
  assoc := by intros; rw [C.assoc]
}

/-
def Product (C D: Category): Category := {
  obj := C.obj × D.obj
  hom := fun (x1, x2) (y1, y2) => C.hom x1 y1 × D.hom x2 y2
  id := fun (x, y) => (C.id x, D.id y)
  comp := fun (f1, f2) (g1, g2) => (C.comp f1 g1, D.comp f2 g2)
  id_left := by simp; intro _ _ (_, _); simp; apply And.intro; apply C.id_left; apply D.id_left
  id_right := by simp; intro _ _ (_, _); simp; apply And.intro; apply C.id_right; apply D.id_right
  assoc := by simp; intro x y z w f g h; apply And.intro; apply C.assoc; apply D.assoc
}

structure functor (C D: Category) where
  func0: C.obj → D.obj
  func1: C.hom x y → D.hom (func0 x) (func0 y)
  id_preserving (x: C.obj):
    func1 (C.id x) = D.id (func0 x)
  comp_preserving (f: C.hom x y) (g: C.hom y z):
    func1 (C.comp f g) = D.comp (func1 f) (func1 g)

structure wedge {C D: Category} (e: D.obj) (F: functor (Product (opposite C) C) D) where
  component (c: C.obj): D.hom e (F.func0 (c, c))
  cond: ∀ c': C.obj, ∀ f: C.hom c c', by
    have Tf1: D.hom (F.func0 (c', c')) (F.func0 (c, c')) := sorry
    have T1f: D.hom (F.func0 (c, c)) (F.func0 (c, c')) := sorry /- tricky -/
    exact D.comp (component c) T1f = D.comp (component c') Tf1

structure end2 {C D: Category} (e: D.obj) (F: functor (Product (opposite C) C) D) where
  w: wedge e F
  universal_exists:
    ∀ e': D.obj,
    ∀ w': wedge e' F,
    ∃ f: D.hom e' e,
    ∀ c: C.obj,
    D.comp f (w.component c) = (w'.component c)

-/

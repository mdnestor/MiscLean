
-- algebraic objects and categories using structures
-- question: why are classes used over structures in mathlib?
-- answer probably has to do with type class inference

-- define a magma
structure Magma where
  elt: Type
  mul: elt → elt → elt

-- define a homomorphism between magmas

namespace Magma

structure Homomorphism (M0 M1: Magma) where
  func: M0.elt → M1.elt
  cond: ∀ x y: M0.elt, M1.mul (func x) (func y) = func (M0.mul x y)

def HomomorphismId (M: Magma): Homomorphism M M := {
  func := id (α := M.elt)
  cond := by simp
}

def HomomorphismComp {M0 M1 M2: Magma} (f: Homomorphism M0 M1) (g: Homomorphism M1 M2): Homomorphism M0 M2 := {
  func := g.func ∘ f.func
  cond := by simp [g.cond, f.cond]
}

end Magma

-- define monoids and groups as extensions of magmas
structure Monoid extends Magma where
  unit: elt
  assoc: ∀ x y z: elt, mul (mul x y) z = mul x (mul y z)
  unit_left: ∀ x: elt, mul unit x = x
  unit_right: ∀ x: elt, mul x unit = x

structure Group extends Monoid where
  inv: elt → elt
  inv_left: ∀ x: elt, mul (inv x) x = unit
  inv_right: ∀ x: elt, mul x (inv x) = unit

-- some sanity checks
theorem right_cancellation (G: Group) (x y z: G.elt): G.mul x z = G.mul y z → x = y := by
  intro h
  calc
    x = G.mul x G.unit := by rw [G.unit_right x]
    _ = G.mul x (G.mul z (G.inv z)) := by rw [G.inv_right]
    _ = G.mul (G.mul x z) (G.inv z) := by rw [G.assoc]
    _ = G.mul (G.mul y z) (G.inv z) := by rw [h]
    _ = G.mul y (G.mul z (G.inv z)) := by rw [G.assoc]
    _ = G.mul y G.unit := by rw [G.inv_right]
    _ = y := by rw [G.unit_right]

theorem homomorphism_preserves_unit (G0 G1: Group) (f: Magma.Homomorphism (G0.toMagma) (G1.toMagma)): f.func G0.unit = G1.unit := by
  apply right_cancellation (z := f.func G0.unit)
  rw [f.cond, G0.unit_left, G1.unit_left]

-- define a category
structure Category where
  obj: Type u
  hom : obj → obj → Type
  comp {x y z: obj}: hom x y → hom y z → hom x z
  id (x: obj): hom x x
  assoc: ∀ f: hom x y, ∀ g: hom y z, ∀ h: hom z w, comp (comp f g) h = comp f (comp g h)
  id_left: ∀ f: hom x y, comp (id x) f = f
  id_right: ∀ f: hom x y, comp f (id y) = f

-- define the categories of magmas, monoids, and groups
def Magmas : Category := {
  obj := Magma
  hom := Magma.Homomorphism
  comp := Magma.HomomorphismComp
  id := Magma.HomomorphismId
  assoc := by
    intros
    simp [Magma.Homomorphism]
    rfl
  id_left := by
    intros
    simp [Magma.Homomorphism]
    rfl
  id_right := by
    intros
    simp [Magma.Homomorphism]
    rfl
}

def Monoids : Category := {
  obj := Monoid
  hom := fun X Y => Magma.Homomorphism (X.toMagma) (Y.toMagma)
  comp := Magmas.comp
  id := fun X => Magma.HomomorphismId (X.toMagma)
  assoc := Magmas.assoc
  id_left := Magmas.id_left
  id_right := Magmas.id_right
}

def Groups : Category := {
  obj := Group
  hom := fun X Y => Magma.Homomorphism (X.toMagma) (Y.toMagma)
  comp := Magmas.comp
  id := fun X => Magma.HomomorphismId (X.toMagma)
  assoc := Magmas.assoc
  id_left := Magmas.id_left
  id_right := Magmas.id_right
}

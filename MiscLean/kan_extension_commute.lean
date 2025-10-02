
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

open CategoryTheory

-- category of indexed sets
class ISet where
  Base: Type*
  Fiber: Base → Type*

class ISetHom (I1 I2: ISet) where
  basemap: I1.Base → I2.Base
  fibermap (x: I1.Base): I1.Fiber x → I2.Fiber (basemap x)

def ISetId (I: ISet): ISetHom I I := {
  basemap := id
  fibermap := fun _ a => a
}

def ISetComp {I1 I2 I3: ISet} (h1: ISetHom I1 I2) (h2: ISetHom I2 I3): ISetHom I1 I3 := {
  basemap := h2.basemap ∘ h1.basemap
  fibermap := fun x a => h2.fibermap (h1.basemap x) (h1.fibermap x a)
}

instance: Category ISet := {
  Hom := ISetHom
  id := ISetId
  comp := ISetComp
}

-- ISet is cocomplete
instance: Limits.HasColimits ISet := by
  simp [Limits.HasColimits]
  constructor
  intro J _
  constructor
  intro F
  -- given functor `F : J ⥤ ISet` show that `Limits.HasColimit F`
  sorry

-- given an indexed set I, DPair I is the type of dependent pairs (x: X, a: Fiber x)
class DPair (I: ISet) where
  x: I.Base
  a: I.Fiber x

-- given a morphism of indexed sets there is a corresponding map between dependent pairs
def DPairMap {I1 I2: ISet} (f: ISetHom I1 I2): DPair I1 → DPair I2 :=
  fun p => {
    x := f.basemap p.x
    a := f.fibermap p.x p.a
  }

-- for each I: ISet, the projection map proj_I sends the pair (x: I.Base, a: I.Fiber x) to x
def proj (I: ISet): DPair I → I.Base :=
  fun p => p.x

-- Grothendeick functor from ISet to Arrow(Set)
def GrothFunc: Functor ISet (Arrow Type*) := {
  obj := fun I: ISet => Arrow.mk (fun p: DPair I => p.x)
  map := fun f => {
    left := DPairMap f
    right := f.basemap
  }
}

-- Psi functor from Arrow(Set) to ISet
def Ψ: Functor (Arrow Type*) ISet := {
  obj := fun f => {
    Base := f.right
    Fiber := fun b => ↑(Set.preimage f.hom {b})
  }
  map := fun {f g} h => {
      basemap := h.right
      fibermap := fun x a => ⟨Set.restrict (Set.preimage f.hom {x}) h.left a, by {simp; sorry}⟩ -- missing proof that g.hom (h.left ↑a) = h.right x
  }
}

-- Equivalence between ISet and Arrow(Set)
def eqv: CategoryTheory.Equivalence ISet (Arrow Type*) := {
  functor := GrothFunc
  inverse := Ψ
  unitIso := {
    hom := {
      app := by {
        intro I
        simp

      }
    }
    inv := {
      app := sorry
    }
  }
  counitIso := {
    hom := sorry
    inv := sorry
  }
}

-- given category T lift to functor from [T, ISet] to [T, Arrow(Set)] via the equivalence
def eqv_comp (T: Type*) [Category T]: Functor (T ⥤ ISet) (T ⥤ Arrow Type*) := {
  obj := fun F => F ⋙ eqv.functor
  map := fun η => whiskerRight η eqv.functor -- not 100% this is corect
}

-- Arrow(Set) is cocomplete
instance: Limits.HasColimits (Arrow Type*) := CategoryTheory.Arrow.hasColimits

-- if f: T ⥤ T' is a functor between small categories and C is cocomplete then every functor F: T ⥤ C has a left kan extension along f
instance {T T' C: Type*} [SmallCategory T] [SmallCategory T'] [Category C] [Limits.HasColimits C] {f: Functor T T'}: ∀ F: Functor T C, f.HasLeftKanExtension F := sorry

theorem main {T T': Type*} [SmallCategory T] [SmallCategory T'] (f: Functor T T'):
  IsIsomorphic (Functor.lan f ⋙ eqv_comp T') (eqv_comp T ⋙ Functor.lan f) -- isomorphism in the functor category
  := by sorry

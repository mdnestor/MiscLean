
import Mathlib.Data.Set.Basic

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans


-- types definition
class TypeMonad where
  T: Type → Type
  unit {X: Type}: X → T X
  bind {X Y: Type} (x: T X) (f: X → T Y): T Y

  unit_left {X Y: Type} {x: X} {f: X → T Y}: bind (unit x) f = f x
  unit_right {X: Type} {tx: T X}: bind tx unit = tx
  assoc {X Y Z: Type} {f: X → T Y} {g: Y → T Z} {tx: T X}: bind tx (fun x => bind (f x) g) = bind (bind tx f) g

-- categorical definition
open CategoryTheory

class CategoricalMonad {C: Type u} [Category.{v} C] where
  T: Functor C C
  unit: NatTrans (𝟭 C) T
  bind: NatTrans (T ⋙ T) T

  -- i might have these switched lol
  unit_left {X: C}: unit.app (T.obj X) ≫ bind.app X = 𝟙 (T.obj X)
  unit_right {X: C}: T.map (unit.app X) ≫ bind.app X = 𝟙 (T.obj X)
  assoc {X: C}: (T.map (bind.app X)) ≫ (bind.app X) = (bind.app (T.obj X)) ≫ (bind.app X)

-- the category of types
instance: Category (Type u) where
  Hom X Y := X → Y
  id X := id (α := X)
  comp f g := g ∘ f
  id_comp f := rfl
  comp_id f := rfl
  assoc f g h := rfl

def KleisiCategory {α: Type u} [C: Category.{v} α] (M: CategoricalMonad α): Category α where
  Hom X Y := C.Hom X (M.T.obj Y)
  id X := M.unit.app X
  comp {X Y Z} f g := by
    exact f ≫ (M.T.map g) ≫ (M.bind.app Z)
  -- these should follow from monad laws
  id_comp {X Y} f := by
    simp
    sorry
  comp_id {X Y} f := by
    simp
    sorry
  assoc {X Y Z W} f g h := by
    simp
    sorry

-- EilenbergMooreCategory idek

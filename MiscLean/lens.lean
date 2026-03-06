
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

-- Lenses https://ncatlab.org/nlab/show/lens+(in+computer+science)
-- Note this implementation does not deal with optics.

open CategoryTheory
open CategoryTheory.Limits

variable {C: Type u} [Category C] [HasBinaryProducts C]

structure Lens (S V: C) where
  get: S ⟶ V
  put: V ⨯ S ⟶ S

noncomputable def Lens.id (X: C): Lens X X := {
  get := 𝟙 X
  put := prod.fst
}

noncomputable def Lens.comp {X Y Z: C} (f: Lens X Y) (g: Lens Y Z): Lens X Z := {
  get := f.get ≫ g.get
  put := prod.map (𝟙 Z) (diag X) ≫
    prod.map (𝟙 Z) (prod.map f.get (𝟙 X)) ≫
    (prod.associator Z Y X).inv ≫
    prod.map g.put (𝟙 X) ≫
    f.put
}


instance (C: Type u) [Category C] [HasBinaryProducts C]: Category C := {
  Hom := fun X Y => Lens.Hom X Y
  id := Lens.Hom.id
  comp := Lens.Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry
}

structure LawfulLens (S V: C) extends Lens S V where
  putget: put ≫ get = prod.fst
  getput: diag S ≫ prod.map get (𝟙 S) ≫ put = 𝟙 S
  putput: (prod.map (𝟙 V) put) ≫ put = (prod.map (𝟙 V) prod.snd) ≫ put

structure BiLens (S T A B: C) where
  view: S ⟶ A
  update: S ⨯ B ⟶ T

noncomputable def prod.swap (X Y: C): X ⨯ Y ⟶ Y ⨯ X :=
  prod.lift prod.snd prod.fst

noncomputable def Lens.Hom.prod {C: Type u} [Category C] [HasBinaryProducts C] {X₁ X₂ Y₁ Y₂: C} (L₁: Lens X₁ Y₁) (L₂: Lens X₂ Y₂):
  Lens (X₁ ⨯ X₂) (Y₁ ⨯ Y₂) := {
    get := prod.map L₁.get L₂.get
    put :=
      (prod.associator (Y₁ ⨯ Y₂) X₁ X₂).inv ≫
      prod.map (prod.associator Y₁ Y₂ X₁).hom (𝟙 X₂) ≫
      prod.map (prod.map (𝟙 Y₁) (prod.swap Y₂ X₁)) (𝟙 X₂) ≫
      prod.map (prod.associator Y₁ X₁ Y₂).inv (𝟙 X₂) ≫
      (prod.associator (Y₁ ⨯ X₁) Y₂ X₂).hom ≫
      prod.map L₁.put L₂.put
  }

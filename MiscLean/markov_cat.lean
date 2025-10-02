import Mathlib.CategoryTheory.Monoidal.Category
namespace CategoryTheory

class SymmMonCat (T: Type u) [C: Category.{v} T] extends MonoidalCategory T where
  swap (A B: T): tensorObj A B ⟶ tensorObj B A
  h0: sorry /- missing that swap is natural in both A and B -/
  s1: ∀ A: T, swap A tensorUnit ≫ (leftUnitor A).hom = (rightUnitor A).hom
  s2: ∀ A B C: T, (associator A B C).hom ≫ swap A (tensorObj B C) ≫ (associator B C A).hom = (tensorHom (swap A B) (𝟙 C)) ≫ (associator B A C).hom ≫ (tensorHom (𝟙 B) (swap A C))
  s3: ∀ A B: T, swap A B ≫ swap B A = 𝟙 (tensorObj A B)

class MarkovCat (T: Type u) [C: Category.{v} T] extends SymmMonCat T where
  copy (X: T): X ⟶ tensorObj X X
  del (X: T): X ⟶ tensorUnit
  m1: ∀ X: T, copy X ≫ tensorHom (𝟙 X) (copy X) = copy X ≫ tensorHom (copy X) (𝟙 X) ≫ (associator X X X).hom
  m2_left: ∀ X: T, copy X ≫ tensorHom (del X) (𝟙 X) ≫ (leftUnitor X).hom = 𝟙 X
  m2_right: ∀ X: T, copy X ≫ tensorHom (𝟙 X) (del X) ≫ (rightUnitor X).hom = 𝟙 X
  m3: ∀ X: T, copy X ≫ swap X X = copy X
  /- compatibility -/
  m4: ∀ X Y: T, del (tensorObj X Y) = tensorHom (del X) (del Y) ≫ (leftUnitor tensorUnit).hom /- the choice of leftUnitor is artbirary (!!)! but I am left handed so.. -/
  m5: sorry
  m6: ∀ X: T, ∀ f: X ⟶ X, f ≫ (del X) = del X

def Stoch (T: Type u) [C: Category.{v} T]: MarkovCat T := sorry
def FinStoch (T: Type u) [C: Category.{v} T]: MarkovCat T := sorry

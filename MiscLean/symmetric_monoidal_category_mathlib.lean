import Mathlib.CategoryTheory.Monoidal.Category
namespace CategoryTheory

class SymmMonCat (T: Type u) [C: Category.{v} T] extends MonoidalCategory T where
  swap (A B: T): tensorObj A B ⟶ tensorObj B A
  h0: sorry /- missing that swap is natural in both A and B -/
  h1: ∀ A: T, (swap A tensorUnit) ≫ (leftUnitor A).hom = (rightUnitor A).hom
  h2: ∀ A B C: T, (associator A B C).hom ≫ (swap A (tensorObj B C)) ≫ (associator B C A).hom = (tensorHom (swap A B) (𝟙 C)) ≫ (associator B A C).hom ≫ (tensorHom (𝟙 B) (swap A C))
  h3: ∀ A B: T, (swap A B) ≫ (swap B A) = 𝟙 (tensorObj A B)

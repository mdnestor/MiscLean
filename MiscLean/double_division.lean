
-- "Single axioms for groups and Abelian groups with various operations" (McCune 1993)
-- https://link.springer.com/article/10.1007/BF00881862

structure DD where
  elem: Type
  div: elem → elem → elem
  e: elem

  law: div (div x (div (div (div x y) z) (div y e))) (div e e) = z

structure Group where
  elem: Type
  mul: elem → elem → elem
  e: elem
  inv: elem → elem
  assoc: ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mul_id: mul x e = x
  id_mul: mul e x = x
  mul_inv: mul x (inv x) = e
  inv_mul: mul (inv x) x = e

def DD.toGroup (D: DD): Group := {
  elem := D.elem
  mul := fun x y => D.div (D.div x D.e) (D.div y D.e)
  e := D.e
  inv := fun x => D.div x D.e
  assoc := sorry
  mul_id := sorry
  id_mul := sorry
  mul_inv := sorry
  inv_mul := sorry
}

@[simp]
def inv_id {G: Group}: G.inv G.e = G.e := by
  calc
    G.inv G.e = G.mul (G.inv G.e) G.e := by rw [G.mul_id]
            _ = G.e := by rw [G.inv_mul]

@[simp]
def inv_inv {G: Group}: ∀ x, G.inv (G.inv x) = x := by
  intro x
  calc
    G.inv (G.inv x) = G.mul (G.inv (G.inv x)) G.e := by sorry
                  _ = G.mul (G.inv (G.inv x)) (G.mul (G.inv x) x) := by sorry
                  _ = G.mul (G.mul (G.inv (G.inv x)) (G.inv x)) x := by sorry
                  _ = G.mul G.e x := sorry
                  _ = x := sorry
    

@[simp]
def socks_shoes {G: Group}: ∀ x y, G.mul (G.inv x) (G.inv y) = G.inv (G.mul y x) := by
  sorry

def Group.toDD (G: Group): DD := {
  elem := G.elem
  div := fun x y => G.mul (G.inv x) (G.inv y)
  e := G.e
  law := by simp [←socks_shoes, G.assoc, G.inv_mul, G.mul_id]
}

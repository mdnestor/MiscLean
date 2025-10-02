-- fields and vector spaces

structure Field where
  element: Type
  add: element -> element -> element
  mul: element -> element -> element
  zero: element
  one: element
  add_associate (x y z: element): add (add x y) z = add x (add y z)
  mul_associate (x y z: element): mul (mul x y) z = mul x (mul y z)
  add_commute (x y: element): add x y = add y x
  mul_commute (x y: element): mul x y = mul y x
  zero_identity (x: element): add x zero = x
  one_identity (x: element): mul x one = x
  negative (x: element): element
  inverse (x: element) (h: x ≠ zero): element
  negative_identity (x: element): add x (negative x) = zero
  inverse_identity (x: element) (h: x ≠ zero): mul x (inverse x h) = one
  distribute (x y z: element): mul x (add y z) = add (mul x y) (mul x z)

/- some elementary properties of a field -/
example (F: Field) (x: F.element): F.mul x F.zero = F.zero := sorry
example (F: Field) (x: F.element): F.negative x = F.mul (F.negative F.one) x := sorry
example (F: Field) (x y: F.element): F.mul x y = F.zero -> (x = F.zero) ∨ (y = F.zero) := sorry
example (F: Field): F.negative F.zero = F.zero := sorry
/- to even state the next theorem, we need the lemma that 0 ≠ 1 in a field -/
theorem one_neq_zero (F: Field): F.one ≠ F.zero := sorry
example (F: Field): F.inverse F.one (one_neq_zero F) = F.one := sorry
example (F: Field) (x: F.element): F.negative (F.negative x) = x := sorry
/- similar case here -/
theorem inverse_nonzero (F: Field) (x: F.element) (h: x ≠ F.zero): F.inverse x h ≠ F.zero := sorry
example (F: Field) (x: F.element) (h: x ≠ F.zero): F.inverse (F.inverse x h) (inverse_nonzero F x h) = x := sorry

structure VectorSpace (F: Field) where
  vector: Type
  add: vector -> vector -> vector
  mul: F.element -> vector -> vector
  add_associate (x y z: vector): add x (add y z) = add (add x y) z
  add_commute (x y: vector): add x y = add y x
  zero: vector
  zero_identity (x: vector): add x zero = x
  negative (x: vector): vector
  negative_identity (x: vector): add x (negative x) = zero
  mul_compatible (a b: F.element) (x: vector): mul a (mul b x) = mul (F.mul a b) x
  mul_identity (x: vector): mul F.one x = x
  distribute (a: F.element) (x y: vector): mul a (add x y) = add (mul a x) (mul a y)
  distribute_other (a b: F.element) (x: vector): mul (F.add a b) x = add (mul a x) (mul b x)

/- some theorems -/
example (V: VectorSpace F) (x: V.vector): V.mul F.zero x = V.zero := sorry
example (V: VectorSpace F) (a: F.element): V.mul a V.zero = V.zero := sorry
example (V: VectorSpace F) (x: V.vector): V.mul (F.negative F.one) x = V.negative x := sorry
example (V: VectorSpace F) (a: F.element) (x: V.vector): V.mul a x = V.zero -> (a = F.zero) ∨ (x = V.zero) := sorry

structure LinearMap (V1 V2: VectorSpace F) where
  func: V1.vector -> V2.vector
  cond1 (x y: V1.vector): func (V1.add x y) = V2.add (func x) (func y)
  cond2 (a: F.element) (x: V1.vector): func (V1.mul a x) = V2.mul a (func x)

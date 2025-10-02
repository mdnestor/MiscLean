
/- field axioms -/

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

theorem one_neq_zero (F: Field): F.one ≠ F.zero := sorry

example (F: Field): F.inverse F.one (one_neq_zero F) = F.one := sorry

example (F: Field) (x: F.element): F.negative (F.negative x) = x := sorry

theorem inverse_nonzero (F: Field) (x: F.element) (h: x ≠ F.zero): F.inverse x h ≠ F.zero := sorry

example (F: Field) (x: F.element) (h: x ≠ F.zero): F.inverse (F.inverse x h) (inverse_nonzero F x h) = x := sorry

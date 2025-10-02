
inductive N where
| zero: N
| next: N -> N

def N.eq (x y: N): Prop :=
  match x with
  | N.zero => match y with
    | N.zero => True
    | N.next _ => False
  | N.next x_previous => match y with
    | N.zero => False
    | N.next y_previous => N.eq x_previous y_previous

infix:0 " ≃ " => N.eq

theorem N.eq_reflexive: forall x: N, x ≃ x := by
  intro x
  match x with
  | N.zero => exact by rw [eq]; simp
  | N.next x_previous => exact by rw [eq]; simp; apply N.eq_reflexive

theorem N.eq_is_symmetric: forall x y: N, (x ≃ y) -> (y ≃ x) := sorry

theorem N.eq_is_transitive: forall x y z: N, (x ≃ y) ∧ (y ≃ z) -> (x ≃ z) := sorry

def N.add (x y: N): N :=
  match x with
  | N.zero => y
  | N.next x_previous => N.next (N.add x_previous y)

infix:0 " + " => N.add

theorem N.add.assoc: forall x y z: N, (x + (y + z)) ≃ ((x + y) + z) := sorry

theorem N.add.zero: forall x: N, (x + N.zero) ≃ x := sorry

theorem N.add.commutative: forall x y: N, (x + y) ≃ (y + x) := sorry

def N.mul (x y: N): N :=
  match x with
  | N.zero => N.zero
  | N.next x_prev => N.add (N.mul x_prev y) y

infix:0 " * " => N.mul

def N.one: N := N.next N.zero

theorem N.mul.assoc: forall x y z: N, (x * (y * z)) ≃ ((x * y) * z) := sorry

theorem N.mul.one: forall x: N, (x * N.one) ≃ x := sorry

theorem N.mul.commutative: forall x y: N, (x * y) ≃ (y * x) := sorry

theorem N.distributive: forall x y z: N, (x * (y + z)) ≃ ((x * y) + (x * z)) := sorry

def Z: Type := N × N

def Z.eq (x y: Z): Prop := N.eq (N.add x.1 y.2) (N.add x.2 y.1)

infix:0 " ≃ " => Z.eq

theorem Z.eq_reflexive: forall x: Z, x ≃ x:= sorry

theorem Z.eq_is_symmetric: forall x y: Z, (x ≃ y) -> (y ≃ x) := sorry

theorem Z.eq_is_transitive: forall x y z: Z, (x ≃ y) ∧ (y ≃ z) -> (x ≃ z) := sorry

def N.toZ (x: N): Z := (x, N.zero)

def Z.zero: Z := N.toZ N.zero

def Z.one: Z := N.toZ N.one

def Z.add (x y: Z): Z := (x.1 + y.1, x.2 + y.2)

infix:0 " + " => Z.add

def Z.neg (x: Z): Z := (x.2, x.1)

def Z.mul (x y: Z): Z := ((x.1 * y.1) + (x.2 * y.2), (x.1 * y.2) + (x.2 * y.1))

infix:0 " * " => Z.mul

def Q: Type := Z × Z

def Q.eq (x y: Q): Prop := (x.1 * y.2) ≃ (x.2 * y.1)

infix:0 " ≃ " => Q.eq

/- a/b + c/d = (a*b + b*c)/ (b*d)-/

def Q.add (x y: Q): Q := ((x.1 * y.2) + (x.2 * y.1), x.2 * y.2)

infix:0 " + " => Q.add

def Q.mul (x y: Q): Q := (x.1 * y.1, x.2 * y.2)

infix:0 " * " => Q.mul

def Q.inv (x: Q): Q := (x.2, x.1)

def Z.toQ (x: Z): Q := (x, Z.one)

def N.toQ (x: N): Q := Z.toQ (N.toZ x)

def Q.zero: Q := Z.toQ Z.zero

def Q.one: Q := Z.toQ Z.one

theorem Q.add_assoc: forall x y z: Q, (x + (y + z)) ≃ ((x + y) + z) := sorry

theorem Q.mul_assoc: forall x y z: Q, (x + (y + z)) ≃ ((x + y) + z) := sorry

theorem Q.add_inverse: forall x: Q, ¬ (x ≃ Q.zero) -> ((x * (Q.inv x)) ≃ Q.one) := sorry

structure Field where
  element: Type
  add: element -> element -> element
  mul: element -> element -> element
  zero: element
  one: element
  add_assoc (x y z: element): add (add x y) z = add x (add y z)
  mul_assoc (x y z: element): mul (mul x y) z = mul x (mul y z)
  add_comm (x y: element): add x y = add y x
  mul_comm (x y: element): mul x y = mul y x
  zero_identity (x: element): add x zero = x
  one_identity (x: element): mul x one = x
  negative (x: element): element
  inverse (x: element) (h: x ≠ zero): element
  negative_identity (x: element): add x (negative x) = zero
  inverse_identity (x: element) (h: x ≠ zero): mul x (inverse x h) = one
  distribute (x y z: element): mul x (add y z) = add (mul x y) (mul x z)

example: Field := {
  element := Q
  add := Q.add
  mul := Q.mul
  zero := Q.zero
  one := Q.one
  add_assoc := sorry
  mul_assoc := sorry
  add_comm := sorry
  mul_comm := sorry
  zero_identity := sorry
  one_identity := sorry
  negative := sorry
  inverse := sorry
  negative_identity := sorry
  inverse_identity := sorry
  distribute := sorry
}

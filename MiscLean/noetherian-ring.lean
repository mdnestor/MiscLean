
structure Ring where
  element: Type
  add: element -> element -> element
  mul: element -> element -> element
  zero: element
  one: element
  neg: element -> element
  add_zero_left: forall x: element, add zero x = x
  add_zero_right: forall x: element, add x zero = x
  mul_one_left: forall x: element, mul one x = x
  mul_one_right: forall x: element, mul x one = x
  add_neg: forall x: element, add x (neg x) = zero
  add_associative: forall x y z: element, add x (add y z) = add (add x y) z
  mul_associative: forall x y z: element, mul x (mul y z) = mul (mul x y) z
  add_commutative: forall x y: element, add x y = add y x
  distributive: forall x y z: element, mul x (add y z) = add (mul x y) (mul x z)

structure CommutativeRing extends Ring where
  mul_commutative: forall x y: element, mul x y = mul y x

def subset (T: Type): Type := T -> Prop
def subset_of {T: Type} (A B: subset T): Prop := forall x: T, A x -> B x

structure Ideal (R: CommutativeRing) where
  element: subset R.element
  subgroup1: element R.zero
  subgroup2: forall x y: R.element, (element x) ∧ (element y) -> element (R.add x y)
  subgroup3: forall x: R.element, element x -> element (R.neg x)
  absorb: forall x y: R.element, element x -> element (R.mul x y)

def chain (R: CommutativeRing): Type := Nat -> Ideal R

def chain.ascending {R: CommutativeRing} (c: chain R): Prop :=
  forall n: Nat, subset_of (c n).element (c (n + 1)).element

def chain.bounded {R: CommutativeRing} (c: chain R): Prop :=
  exists m: Nat, forall n: Nat, m ≤ n -> c m = c n

def Noetherian (R: CommutativeRing): Prop :=
  forall c: Nat -> Ideal R, (chain.ascending c) ∧ (chain.bounded c)

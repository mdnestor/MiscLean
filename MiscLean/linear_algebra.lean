import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.commandStart false

namespace LinearAlgebra



-- Definition of a vector space over a field F with X the set of vectors.

class VectorSpace (F: Type) [Field F] (X: Type) [AddCommGroup X] extends MulAction F X where
  distrib_left: ∀ (a: F) (x y: X), a • (x + y) = a • x + a • y
  distrib_right: ∀ (a b: F) (x: X), (a + b) • x = a • x + b • x

-- From now on assume the field F is given.

variable {F: Type} [Field F]

-- Simple properties of a vector space:

theorem zero_scale {X: Type} [AddCommGroup X] [VectorSpace F X] (x: X): 0 • x = 0 := by
  sorry

theorem scale_zero {X: Type} [AddCommGroup X] [VectorSpace F X] (a: F): a • (0: X) = 0 := by
  sorry

theorem scale_neg {X: Type} [AddCommGroup X] [VectorSpace F X] (x: X): (-1) • x = -x := by
  exact neg_one_zsmul x

-- Examples of vector spaces:
-- The trivial vector space consisting of 1 point (here represented by the `Unit` type).

def SingletonSpace: VectorSpace F Unit := {
  distrib_left := by
    intro _ _ _
    rfl
  distrib_right := by
    intro _ _ _
    rfl
}

-- The vector space of F over itself. Call it the "scalar space"?

def ScalarSpace: VectorSpace F F := {
  distrib_left := by
    intro a b c
    exact smul_add a b c
  distrib_right := by
    intro a b c
    exact add_smul a b c
}

-- The product of two vector spaces is a vector space.

def ProductSpace {X Y: Type} [AddCommGroup X] [AddCommGroup Y] [VectorSpace F X] [VectorSpace F Y]: VectorSpace F (X × Y) := {
  distrib_left := by
    intro a (x1, y1) (x2, y2)
    simp; constructor
    · exact VectorSpace.distrib_left a x1 x2
    · exact VectorSpace.distrib_left a y1 y2
  distrib_right := by
    intro a b (x, y)
    simp; constructor
    · exact VectorSpace.distrib_right a b x
    · exact VectorSpace.distrib_right a b y
}



-- Definition of a subspace.

structure isSubspace (F: Type) [Field F] {X: Type} [AddCommGroup X] [VectorSpace F X] (S: Set X): Prop where
  sum_closed: ∀ (x y: X), x ∈ S → y ∈ S → x + y ∈ S
  scalar_closed: ∀ (a: F) (x: X), x ∈ S → a • x ∈ S

-- Ideally we should also define a map that turns a set which is a subspace into an actual VectorSpace object.

-- Examples of subspaces: the whole space and the single point zero.

theorem full_subspace {X: Type} [AddCommGroup X] [VectorSpace F X]: isSubspace F (@Set.univ X) := {
  sum_closed := by intros; trivial
  scalar_closed := by intros; trivial
}

theorem singleton_subspace {X: Type} [AddCommGroup X] [VectorSpace F X]: isSubspace F (Set.singleton (0: X)) := {
  sum_closed := by
    intro x y hx hy
    simp_all [Set.singleton]
  scalar_closed := by
    intro a x hx
    simp_all [Set.singleton]
    exact scale_zero a
}

-- TODO: sum of subspaces.



-- Linear maps between vector spaces.
-- For convenience assume X, Y, Z are given commutative groups.

variable {X Y Z: Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]

-- Definition of a linear map between two vector spaces over a shared field F.

structure linear_map (F: Type) [Field F] [VectorSpace F X] [VectorSpace F Y] (f: X → Y): Prop where
  additive: ∀ (x y: X), f (x + y) = f x + f y
  homogeneous: ∀ (a: F) (x: X), a • (f x) = f (a • x)

-- The identity map is linear.

theorem linear_identity [VectorSpace F X]: linear_map F (@id X) := by
  constructor
  · intro x y
    rfl
  · intro a x
    rfl

-- The composition of linear maps is linear.

theorem linear_composition [VectorSpace F X] [VectorSpace F Y] [VectorSpace F Z]
  {f: X → Y} {g: Y → Z} (hf: linear_map F f) (hg: linear_map F g): linear_map F (g ∘ f) := by
  constructor
  · intro x y
    simp [hf.additive, hg.additive]
  · intro a x
    simp [hf.homogeneous, hg.homogeneous]

-- The image of a linear map is a subspace.

def image (f: X → Y): Set Y :=
  Set.range f

theorem image_subspace [VectorSpace F X] [VectorSpace F Y] {f: X → Y} (h: linear_map F f): isSubspace F (image f) := by
  constructor
  · intro y1 y2 hy1 hy2
    obtain ⟨x1, hx1⟩ := hy1
    obtain ⟨x2, hx2⟩ := hy2
    exists x1 + x2
    rw [←hx1, ←hx2, h.additive]
  · intro a y hy
    obtain ⟨x, hx⟩ := hy
    exists a • x
    rw [←hx, h.homogeneous]

-- The kernel of a linear map is a subspace.

def kernel (f: X → Y): Set X :=
  Set.preimage f {0}

theorem kernel_subspace [VectorSpace F X] [VectorSpace F Y] {f: X → Y} (h: linear_map F f): isSubspace F (kernel f) := by
  constructor
  · intro x y hx hy
    simp_all [kernel]
    rw [h.additive, hx, hy, zero_add]
  · intro a x hx
    simp_all [kernel]
    rw [←h.homogeneous, hx, scale_zero]



-- Eigenvectors / eigenvalues.

-- An eigenpair (x, Λ) of a map f: X → X consists of a vector x and scalar Λ such that f(x) = Λ*x.
-- x is called an eigenvector if there exists a corresponding eigenvalue and vice versa.

def eigenpair (F: Type) [Field F] {X: Type} [AddCommGroup X] [VectorSpace F X] (f: X → X) (x: X) (Λ: F): Prop :=
  f x = Λ • x

def eigenvector {X: Type} [AddCommGroup X] [VectorSpace F X] (f: X → X) (x: X) : Prop :=
  ∃ Λ, eigenpair F f x Λ

def eigenvalue {X: Type} [AddCommGroup X] [VectorSpace F X] (f: X → X) (Λ: F) : Prop :=
  ∃ x, eigenpair F f x Λ

-- If f1 has eigenpair (x, Λ1) and f2 has eigenpair (x, Λ2) then f2 ∘ f1 has eigenpair (x, Λ1*Λ2).

def eigenvalue_mul {X: Type} [AddCommGroup X] [VectorSpace F X] (f1 f2: X → X) (x: X) (Λ1 Λ2: F) (h1: eigenpair F f1 x Λ1) (h2: eigenpair F f2 x Λ2): eigenpair F (f2 ∘ f1) x (Λ1 * Λ2) := by
  sorry

-- The identity map has eigenpairs (x, 1) for every x.

def eigenvalue_identity {X: Type} [AddCommGroup X] [VectorSpace F X] (x: X): eigenpair F id x 1 := by
  sorry

-- If x is in the kernel of f then its eigenvalue is zero.

def eigenvalue_kernel {X: Type} [AddCommGroup X] [VectorSpace F X] (f: X → X) (x: X) (hx: x ∈ kernel f): eigenpair F f x 0 := by
  sorry



-- Todo: the hom set of linear maps between two vector spaces forms a vector space. Also the dual.



-- Next we can introduce the coordinate spaces.
-- First some bookkeeping to show that the additive group on F gives an additive group on coordinates, and hence a vector space.

instance AddCommGroup.pointwise [Field F] (I: Type): AddCommGroup (I → F) := {
  add  := fun x y ↦ fun i ↦ (x i) + (y i)
  zero := fun i ↦ 0
  neg  := fun x ↦ fun i ↦ -(x i)
  nsmul := fun n ↦ fun x ↦ fun i ↦ n • (x i)
  zsmul := fun n ↦ fun x ↦ fun i ↦ n • (x i)
  add_assoc  := by apply add_assoc
  zero_add   := by simp
  add_zero   := by simp
  add_comm   := by apply add_comm
  neg_add_cancel := by apply neg_add_cancel
  sub_eq_add_neg := by apply sub_eq_add_neg
  nsmul_zero  := by apply zero_nsmul
  nsmul_succ  := by intros; simp; apply add_one_mul
  zsmul_zero' := by intros; ext; apply zero_smul
  zsmul_succ' := by intros; simp; apply add_one_mul
  zsmul_neg'  := by intros; simp; ring_nf
}

instance VectorSpace.pointwise (I: Type): VectorSpace F (I → F) := {
  smul := sorry,
  one_smul := sorry,
  mul_smul := sorry,
  distrib_left := sorry,
  distrib_right := sorry
}



-- Coordinate vectors.

def Vector (F: Type) (n: Nat): Type :=
  Fin n → F

-- Coordinate vectors form a vector space.

instance [Field F] (n: Nat): AddCommGroup (Vector F n) :=
  AddCommGroup.pointwise (Fin n)

instance [Field F] (n: Nat): VectorSpace F (Vector F n) :=
  VectorSpace.pointwise (Fin n)

-- Definition of unit vectors.

def unit_vector (F: Type) [Field F] {n: Nat} (i: Fin n): Vector F n :=
  fun j ↦ if i = j then 1 else 0

-- Coordinate representation in terms of unit vectors.

theorem coordinate_representation [Field F] (n: Nat) (x: Vector F n): x = ∑ i, (x i) • unit_vector F i := by
  simp [Vector]
  ext j
  sorry

-- Definition of a matrix.

def Matrix (F: Type) (m n: Nat): Type :=
  Fin m × Fin n → F

-- Matrices also form a vector space.

instance [Field F] (m n: Nat): AddCommGroup (Matrix F m n) :=
  AddCommGroup.pointwise (Fin m × Fin n)

instance [Field F] (m n: Nat): VectorSpace F (Matrix F m n) :=
  VectorSpace.pointwise (Fin m × Fin n)



-- Matrix algebra. Let m, n be natural numbers.

variable {m n: Nat}

-- Definition of the transpose.

def transpose (M: Matrix F m n): Matrix F n m :=
  fun (i, j) ↦ M (j, i)

-- Transpose is idempotent.

theorem transpose_transpose (M: Matrix F m n): transpose (transpose M) = M := by
  exact rfl

-- A square matrix symmetric if it's equal to its transpose.

def symmetric (M: Matrix F n n): Prop :=
  transpose M = M

-- Matrix and vector operations.
-- Take an m-dimensional vector and stack it n times.

def stack (x: Vector F m) (n: Nat): Matrix F m n :=
  fun (i, _) ↦ x i

-- Two ways to turn a vector into a matrix: either a column vector or a row vector.

def column_vector (x: Vector F n): Matrix F n 1 :=
  stack x 1

def row_vector (x: Vector F n): Matrix F 1 n :=
  transpose (column_vector x)

-- Given a matrix, take the i-th column or the j-th row.

def take_column (M: Matrix F m n) (i: Fin m): Vector F n :=
  fun j ↦ M (i, j)

def take_row (M: Matrix F m n) (j: Fin n): Vector F m :=
  take_column (transpose M) j



-- Given a vector, turn it into the corresponding diagonal matrix.

def diagonal {n: Nat} (d: Vector F n): Matrix F n n :=
  fun (i, j) ↦ if i = j then d i else 0

-- A diagonal matrix is symmetric.

theorem diagonal_transpose {n: Nat} (d: Vector F n): symmetric (diagonal d) := by
  simp [symmetric, Matrix]
  ext ij
  let (i, j) := ij
  simp [diagonal, transpose]
  by_cases i = j
  · simp_all
  · simp_all
    intro
    simp_all

-- The i-th column in a diagonal matrix is the i-th unit vector scaled by the i-th diagonal element.

theorem diagonal_take_column {n: Nat} (d: Vector F n) (i: Fin n): take_column (diagonal d) i = (d i) • (unit_vector F i) := by
  sorry

-- The identity matrix is a diagonal of ones.

def identity (F: Type) [Field F] (n: Nat): Matrix F n n :=
  diagonal (fun _ ↦ 1)

theorem identity_symmetric (n: Nat): symmetric (identity F n) := by
  simp [identity, diagonal_transpose]



-- Matrix multiplication, registered as an `HMul` instance so we can use * notation.

instance matmul (m n p: Nat): HMul (Matrix F m n) (Matrix F n p) (Matrix F m p) := {
  hMul := fun A B ↦ fun (i, k) ↦ ∑ j, A (i, j) * B (j, k)
}

theorem matmul_assoc {m n p q: Nat} (A: Matrix F m n) (B: Matrix F n p) (C: Matrix F p q): (A * B) * C = A * (B * C) := by
  sorry

theorem matmul_distrib_left {m n p q: Nat} (A: Matrix F m n) (B C: Matrix F n p): A * (B + C) = A * B + A * C := by
  sorry

theorem matmul_distrib_right {m n p q: Nat} (A B: Matrix F m n) (C: Matrix F n p): (A + B) * C = A * C + B * C := by
  sorry

-- A*B = (B^T * A^T)^T

theorem matmul_transpose {m n p: Nat} (A: Matrix F m n) (B: Matrix F n p): A * B = transpose ((transpose B) * (transpose A)) := by
  simp [Matrix]
  ext ik
  let (i, k) := ik
  simp [matmul, transpose, matmul]
  refine Fintype.sum_equiv ?_ _ _ fun j ↦ ?_
  · rfl
  · exact CommMonoid.mul_comm (A (i, j)) (B (j, k))

-- The identity matrix is the left/right identity

theorem matrix_multiply_identity_left {m n: Nat} (M: Matrix F m n): (identity F m) * M = M := by
  simp [Matrix]
  ext
  simp [matmul, identity, diagonal]

theorem matrix_multiply_identity_right {m n: Nat} (M: Matrix F m n): M * (identity F n) = M := by
  rw [matmul_transpose, identity_symmetric, matrix_multiply_identity_left, transpose_transpose]

-- The hadamard product, aka the pointwise product.

def hadamard_product {I: Type} (x y: I → F): I → F :=
  fun i ↦ x i * y i

-- The product of two diagonal matrices is the diagonal of the hadamard product of their diagonal vectors.

theorem diagonal_matmul (d1 d2: Vector F n): (diagonal d1) * (diagonal d2) = diagonal (hadamard_product d1 d2) := by
  sorry



-- Two matrices A, B are inverses if their product is the identity.
-- (A is the left inverse of B, and B the right inverse of A.)

def inverse (A: Matrix F m n) (B: Matrix F n m): Prop :=
  A * B = identity F m

-- The identity is its own inverse

theorem identity_inverse: inverse (identity F n) (identity F n) := by
  rw [inverse, matrix_multiply_identity_left]

-- If D = diag(d1, ..., dn) where d1, ..., dn are all nonzero,
-- then its inverse is diag(1/d1, ..., 1/dn).

theorem diagonal_inverse (d: Vector F n) (h: ∀ i, d i ≠ 0): inverse (diagonal d) (diagonal (fun i ↦ (d i)⁻¹)) := by
  rw [inverse, diagonal_matmul, identity]
  congr
  funext i
  rw [hadamard_product]
  exact CommGroupWithZero.mul_inv_cancel (d i) (h i)


-- If A, A' are inverses and c ≠ 0 then  c*A and (1/c) * A' are inverse.

theorem inverse_scalar {m n p: Nat} (A: Matrix F m n) (A': Matrix F n m) (h: inverse A A') (c: F) (h2: c ≠ 0): inverse (c • A) (c⁻¹ • A') := by
  simp_all [inverse]
  calc
    (c • A) * (c⁻¹ • A')
      = c • (A * (c⁻¹ • A')) := by sorry
    _ = c • (c⁻¹ • (A * A')) := by sorry
    _ = identity F m := by simp_all

-- If A, A' are inverses and B, B' are inverses then A * B and B' * A' are inverse.

theorem inverse_product {m n p: Nat} (A: Matrix F m n) (A': Matrix F n m) (B: Matrix F n p) (B': Matrix F p n) (h1: inverse A A') (h2: inverse B B'): inverse (A * B) (B' * A') := by
  simp_all [inverse]
  calc
    A * B * (B' * A')
      = A * (B * B') * A'       := by simp [matmul_assoc]
    _ = A * (identity F n) * A' := by rw [h2]
    _ = A * A'                  := by rw [matrix_multiply_identity_right]
    _ = identity F m            := by exact h1



-- Multiply a vector by a matrix on the right.

instance vecmulmat {m n: Nat}: HMul (Vector F m) (Matrix F m n) (Vector F n) := {
  hMul := fun x M ↦ take_column ((row_vector x) * M) 0
}

-- multiply a vector by a matrix on the left
instance matmulvec {m n: Nat}: HMul (Matrix F m n) (Vector F n) (Vector F m) := {
  hMul := fun M x ↦ x * transpose M
}

-- lets just focus on vecmulmat
theorem vecmulmat_right_identity {n: Nat} (x: Vector F n): x * (identity F n) = x := by
  simp [vecmulmat, matrix_multiply_identity_right]
  rfl

theorem vecmulmat_left_distrib {m n: Nat} (x: Vector F m) (A B: Matrix F m n): x * (A + B) = x * A + x * B := by
  simp [vecmulmat]
  rw [matmul_distrib_left]
  · rfl
  · assumption

theorem vecmulmat_smul_assoc {m n: Nat} (c: F) (x: Vector F m) (M: Matrix F m n): c • (x * M) = (c • x) * M := by
  sorry

theorem vecmulmat_smul_assoc' {m n: Nat} (c: F) (x: Vector F m) (M: Matrix F m n): c • (x * M) = x * (c • M) := by
  sorry

def inner_product {n: Nat} (x y: Vector F n): F :=
  ((row_vector x) * (column_vector y)) (0, 0)

def outer_product {n: Nat} (x y: Vector F n): Matrix F n n :=
  (column_vector x) * (row_vector y)

theorem vecmulmat_index {m n: Nat} (x: Vector F m) (M: Matrix F m n) (j: Fin n): (x * M) j = inner_product x (take_row M j) := by
  rfl



-- The linear map induced by a matrix.

def matrix_map {m n: Nat} (M: Matrix F m n): Vector F m → Vector F n :=
  fun x ↦ x * M

theorem vecmulmat_linear {m n: Nat} (M: Matrix F m n): linear_map F (matrix_map M) := by
  sorry

-- The matrix corresponding to a linear map.

def map_matrix {m n: Nat} (f: Vector F m → Vector F n): Matrix F m n :=
  fun (i, j) ↦ f (unit_vector F i) j

-- Prove this correspondence is a bijection.

theorem matrix_map_matrix {m n: Nat} (M: Matrix F m n): map_matrix (matrix_map M) = M := by
  sorry

theorem map_matrix_map {m n: Nat} (f: Vector F m → Vector F n): matrix_map (map_matrix f) = f := by
  sorry


theorem eigenpair_iff {n: Nat} (M: Matrix F n n) (x: Vector F n) (Λ: F): eigenpair F (matrix_map M) x Λ ↔ x * M = Λ • x := by
  rfl

-- (x, Λ) is an eigenpair for M iff. x * (M - Λ • I) = 0.

theorem eigenpair_iff' {n: Nat} (M: Matrix F n n) (x: Vector F n) (Λ: F): eigenpair F (matrix_map M) x Λ ↔ x * (M - Λ • (identity F n)) = 0 := by
  sorry

-- The diagonal matrix D = diag(d1, ..., dn) has eigenpairs (e_i, d_i).

theorem diagonal_eigenpair {n: Nat} (d: Vector F n) (i: Fin n): eigenpair F (matrix_map (diagonal d)) (unit_vector F i) (d i) :=
  sorry

-- If A has eigenpair (x, Λ) and B = P * A * P⁻¹ then B has eigenpair (P * x, Λ)

theorem eigenpair_conjugate {A B P P': Matrix F n n} {x: Vector F n} {Λ: F} (h1: eigenpair F (matrix_map A) x Λ) (h2: B = P' * A * P) (h3: inverse P P'): eigenpair F (matrix_map B) (x * P) Λ := by
  simp_all [eigenpair, matrix_map, inverse]
  calc
    x * P * (P' * A * P)
      = x * (P * P') * A * P := by sorry
    _ = x * (identity F n) * A * P := by rw [h3]
    _ = x * A * P := by simp [vecmulmat_right_identity]
    _ = Λ • x * P := by simp [h1]
    _ = Λ • (x * P) := by simp [vecmulmat_smul_assoc]

-- Corollary: If M = P * D * P⁻¹ and D = diag(d1, ..., dn) then M has eigenpairs (e_i * P, d_i)

theorem eigenpair_diagonalized (M P P': Matrix F n n) (d: Vector F n) (h1: M = P' * (diagonal d) * P) (h2: inverse P P') (i: Fin n): eigenpair F (matrix_map M) (unit_vector F i * P) (d i) := by
  exact eigenpair_conjugate (diagonal_eigenpair d i) h1 h2



end LinearAlgebra


-- "Long-time behavior of a class of biological models" by Weinberger (1982) https://doi.org/10.1137/0513028

import Mathlib.Data.Real.Basic
import Mathlib.Order.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Function.L2Space

-- first section is very general

-- theorems about ordering

open Function Matrix

def monotone {X Y: Type} [Preorder Y] (Q: (X → Y) → (X → Y)): Prop :=
  ∀ u v: X → Y, u ≤ v → (Q u) ≤ (Q v)

theorem comparison_principle {X Y: Type} [Preorder Y] {Q: (X → Y) → (X → Y)} {useq vseq: ℕ → X → Y}
  (h1: monotone Q)
  (h2: ∀ n: Nat, useq (n + 1) ≤ Q (useq n))
  (h3: ∀ n: Nat, Q (vseq n) ≤ vseq (n + 1))
  (h4: useq 0 ≤ vseq 0):
    useq ≤ vseq := by
  intro n
  induction n with
  | zero => exact h4
  | succ p h => {
    have h5 := h1 (useq p) (vseq p) h
    have h6 := le_trans (h2 p) h5
    exact le_trans h6 (h3 p)
  }

theorem prop_4_2 {X Y: Type} [Preorder Y] {Q: (X → Y) → (X → Y)} {u0: X → Y} (h1: monotone Q) (h2: u0 ≤ Q u0):
  ∀ n: Nat, Q^[n] u0 ≤ Q^[n+1] u0 := by
  have h3: ∀ n: Nat, Q^[n+1] u0 ≤ Q (Q^[n] u0) := by
    intro n
    rw [Function.iterate_succ']
    rfl
  have h4: ∀ n: Nat, Q (Q^[n+1] u0) ≤ Q^[n+2] u0 := by
    intro n
    have h4 := h3 (n + 1)
    rw [Function.iterate_succ'] at h4
    have h5: Q^[n + 2] = Q ∘ Q^[n+1] := by rw [Function.iterate_succ']
    rw [h5]
    exact h4
  exact comparison_principle h1 h3 h4 h2

-- theorems about translation and translation equivariance

def translate {X Y: Type} [Add X] (y: X) (u: X → Y): X → Y :=
  fun x => u (x + y)

def homogeneous {X Y: Type} [Add X] (Q: (X → Y) → (X → Y)): Prop :=
  ∀ u: X → Y, ∀ y: X, Q (translate y u) = translate y (Q u)

def is_const (f: X → Y): Prop :=
  ∃ y: Y, f = const X y

theorem const_is_const (X: Type) (y: Y): is_const (const X y) := by
  exists y

def const_iff_all_eq {X Y: Type} [Nonempty X] (f: X → Y): is_const f ↔ ∀ x1 x2: X, f x1 = f x2 := by
  apply Iff.intro
  intro h _ _
  obtain ⟨c, hc⟩ := h
  simp [hc]
  intro h
  let x := Classical.choice (by assumption)
  exists f x
  ext
  apply h

/-
theorem translate_const {X Y: Type} [AddCommGroup X] (x: X) (c: Y): translate (Function.const X c) x = Function.const X c := by
  rfl
-/

theorem translate_is_const {X Y: Type} [Add X] {u: X → Y} (h: is_const u): ∀ x: X, translate x u = u := by
  intro
  obtain ⟨c, hc⟩ := h
  rw [hc]
  rfl

theorem homogeneous_preserves_const {X: Type} [AddCommGroup X] {Q: (X → Y) → (X → Y)} {u: X → Y} (h1: homogeneous Q) (h2: is_const u): is_const (Q u) := by
  rw [const_iff_all_eq]
  intro x1 x2
  let dx := x1 - x2
  calc
    Q u x1 = Q u (x2 + dx)            := by rw [add_sub_cancel]
          _ = (translate dx (Q u)) x2 := by rfl
          _ = Q (translate dx u) x2   := by rw [h1]
          _ = Q u x2                  := by rw [translate_is_const h2]

-- if Q is homogeneous can define the little map q: R → R
theorem local_map_of_homogeneous {X: Type} [Nonempty X] [AddCommGroup X] {Q: (X → Y) → (X → Y)} (h: homogeneous Q): ∃ q: Y → Y, ∀ c: Y, Q (const X c) = const X (q c) := by
  let x := Classical.choice (by assumption)
  exists fun c => Q (const X c) x
  intro c
  obtain ⟨_, hc⟩ := homogeneous_preserves_const h (const_is_const X c)
  simp [hc]

def bounded_by {X: Type} (b: ℝ): Set (X → ℝ) := 
  fun u => ∀ x: X, 0 ≤ u x ∧ u x ≤ b

def preserves_bounded_by (Q: (X → ℝ) → (X → ℝ)) (b: ℝ): Prop :=
  ∀ u: X → ℝ, u ∈ bounded_by b → (Q u) ∈ bounded_by b


-- main theorems

-- theorem 6.1
-- let ξ be a unit vector and cstar(ξ) its speed in that direction
-- let S = {x ∈ ℝ^n | ∀ ξ ∈ S^(n-1), x ⬝ ξ ≤ cstar(ξ)} which is convex
-- suppose h1: S is bounded and nonempty
-- let S' be an open set containing S
-- let u0: ℝ^n → ℝ suppose h2: u0(x) = 0 outside a bounded set
-- assume h3: bounding principle (TODO)
-- then limsup_{n → ∞} max_{x ∉ n * S'} u_n(x) ≤ π0

#check max
-- the operator defined by equation 5.2

abbrev R (n: ℕ): Type := Fin n → ℝ

def zero_vec (n: ℕ): Fin n → ℝ := fun _ => 0

noncomputable def R_op {n: ℕ} (φ: ℝ → ℝ) (Q: (R n → ℝ) → R n → ℝ) (c: ℝ) (ξ: R n): (ℝ → ℝ) → ℝ → ℝ :=
  fun a s => max (φ s) (Q (fun x: R n => a (dotProduct x ξ) + s + c) (zero_vec n))

-- if R is the above operator then R a > a
-- these probably need additional hypotheses

theorem ineq_5_3 {n: ℕ} {φ: ℝ → ℝ} {Q: (R n → ℝ) → R n → ℝ} {c: ℝ} {ξ: R n} {a: ℝ}
  (h1: const (R n) a < Q (const (R n) a)):
  const ℝ a < R_op φ Q c ξ (const ℝ a) := by
  sorry

theorem R_op_monotone {n: ℕ} (φ: ℝ → ℝ) {Q: (R n → ℝ) → R n → ℝ} (c: ℝ) (ξ: R n)
  (h1: monotone Q):
  monotone (R_op φ Q c ξ) := by
  sorry

theorem φ_lt_R_φ {n: ℕ} (φ: ℝ → ℝ) {Q: (R n → ℝ) → R n → ℝ} (c: ℝ) (ξ: R n)
  (h1: monotone Q):
  φ < R_op φ Q c ξ φ := by
  sorry

-- now define the a-sequence
noncomputable def a_seq {n: ℕ} (φ: ℝ → ℝ) (Q: (R n → ℝ) → R n → ℝ) (c: ℝ) (ξ: R n): ℕ → ℝ → ℝ :=
  fun n => (R_op φ Q c ξ)^[n] φ

abbrev Nondecreasing (f: X → Y) [Preorder X] [Preorder Y] := ∀ x1 x2: X, x1 ≤ x2 → f x1 ≤ f x2

abbrev Nonincreasing (f: X → Y) [Preorder X] [Preorder Y] := ∀ x1 x2: X, x1 ≤ x2 → f x1 ≥ f x2

abbrev NondecreasingSeq (a: ℕ → X) [Preorder X] := ∀ n: ℕ, a n ≤ a (n + 1)

-- lemma 5.1 says that a_seq is nondecreasing in n, nonincreasing in s and c, and continuous in s, c, and ξ
theorem a_seq_nondecreasing_in_n {N: ℕ} (φ: ℝ → ℝ) (Q: (R N → ℝ) → R N → ℝ) (c: ℝ) (ξ: R N)
  (h1: monotone Q):
  ∀ s: ℝ, NondecreasingSeq fun n => a_seq φ Q c ξ n s := by
    let a: ℕ → ℝ → ℝ := fun m => a_seq φ Q c ξ m
    have h2 := R_op_monotone φ c ξ h1
    have hφ: a 0 = φ := rfl
    have h3: a 0 ≤ (R_op φ Q c ξ) (a 0) := by
      rw [hφ]
      exact le_of_lt (φ_lt_R_φ φ c ξ h1)
    have h4 := prop_4_2 h2 h3
    simp [a_seq]
    intro s n
    have h5 := h4 n
    rw [←hφ]
    rw [←hφ] at h5
    exact h5 s

theorem a_seq_nondecreasing_in_s {n: ℕ} (φ: ℝ → ℝ) (Q: (R n → ℝ) → R n → ℝ) (c: ℝ) (ξ: R n):
  ∀ n: ℕ, Nondecreasing (a_seq φ Q c ξ n) :=
    sorry

theorem a_seq_nondecreasing_in_c {n: ℕ} (φ: ℝ → ℝ) (Q: (R n → ℝ) → R n → ℝ) (ξ: R n):
  ∀ n: ℕ, ∀ s: ℝ, Nondecreasing fun c => a_seq φ Q c ξ n s :=
    sorry

-- TODO: restrict ξ to be unit vectors
def UnitVec (n: ℕ) :=
  {x: R n // ‖x‖ = 1}

def cstar (Q: (R n → ℝ) → R n → ℝ) (ξ: R n): ℝ :=
  sorry

theorem prop_5_3 {Q: (R n → ℝ) → R n → ℝ} {y: R n}:
  ∀ ξ: R n, cstar (translate y ∘ Q) ξ = cstar Q ξ + dotProduct y ξ :=
    sorry

theorem prop_5_4 {Q: (R n → ℝ) → R n → ℝ} {π0 δ b: ℝ}
  (h1: 0 ≤ δ ∧ δ ≤ π0)
  (h2: ∀ u: R n → ℝ, (∀ x: R n, ‖x‖ < b → u x ≤ δ) → Q u (zero_vec n) ≤ δ):
  ∀ ξ: R n, cstar Q ξ ≤ b :=
    sorry

abbrev Bound (S: Set X) [Norm X] (b: ℝ) := ∀ x ∈ S, ‖x‖ < b

abbrev Bounded (S: Set X) [Norm X] := ∃ b: ℝ, Bound S b

def LimsupSeq (x: ℕ → ℝ): EReal := sorry

theorem theorem_6_1 {Q: (R n → ℝ) → R n → ℝ} {u0: R n → ℝ} {π1: ℝ} {S': Set (R n)}
  (S := {x: R n | ∀ ξ: R n, dotProduct x ξ ≤ cstar Q ξ})
  (h1: Bounded S) -- S is bounded
  (h2: Nonempty S)
  (h3: S ⊆ S')
  (h4: IsOpen S')
  (h5: Bounded {x: R n | u0 x ≠ 0})
  (h6: u0 < const (R n) π1):
  LimsupSeq (fun m => sSup (Set.image (fun x => (Q^[n] u0) x) (Set.image (fun x => m*x) S')ᶜ)) ≤ π0 := by
  sorry

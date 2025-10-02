/-
Contraction mapping theorem aka the Banach fixed point theorem

Follows the proof given in Ch. 3 of Applied Analysis by Hunter and Nachtergaele
https://www.math.ucdavis.edu/~hunter/book/ch3.pdf

official mathlib proof is in https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/MetricSpace/Contracting.lean
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

structure MetricSpace (X: Type) where
  dist: X → X → Real
  nonneg: ∀ x y: X, dist x y ≥ 0
  eq_iff_dist_zero: ∀ x y: X, x = y ↔ dist x y = 0
  symm: ∀ x y: X, dist x y = dist y x
  tri: ∀ x y z: X, dist x z ≤ dist x y + dist y z

def continuous (M1: MetricSpace X1) (M2: MetricSpace X2) (f: X1 → X2): Prop :=
  ∀ x: X1, ∀ ε: Real, ε > 0 → ∃ δ: Real, δ > 0 ∧ ∀ y: X1, M1.dist x y < δ → M2.dist (f x) (f y) < ε

def converges (M: MetricSpace X) (a: Nat → X) (x: X): Prop :=
  ∀ ε: Real, ε > 0 → ∃ N: Nat, ∀ n: Nat, N ≤ n → M.dist (a n) x < ε

def cauchy (M: MetricSpace X) (a: Nat → X): Prop :=
  ∀ ε: Real, ε > 0 → ∃ N: Nat, ∀ m n: Nat, N ≤ m ∧ N ≤ n → M.dist (a m) (a n) < ε

def complete (M: MetricSpace X): Prop :=
  ∀ a: Nat → X, cauchy M a → ∃ x: X, converges M a x

theorem arbitrarily_close_eq (x: Real) (h: x ≥ 0): (∀ ε: Real, ε > 0 → x < ε) → x = 0 := by
  sorry

theorem limit_unique (h1: converges M a x1) (h2: converges M a x2): x1 = x2 := by
  -- we can show for every ε > 0 that dist x1 x2 < ε
  have x1_x2_arbitrarily_close: ∀ ε: Real, ε > 0 → M.dist x1 x2 < ε := by
    intro ε ε_pos
    have ε_div_2_pos: ε/2 > 0 := div_pos_iff.mpr (Or.inl ⟨ε_pos, two_pos⟩)
    obtain ⟨N1, conv_impl1⟩ := h1 (ε/2) ε_div_2_pos
    obtain ⟨N2, conv_impl2⟩ := h2 (ε/2) ε_div_2_pos
    let n := max N1 N2
    have an_near_x1 := conv_impl1 n (by apply le_max_left)
    have an_near_x2 := conv_impl2 n (by apply le_max_right)
    calc
      M.dist x1 x2 ≤ M.dist x1 (a n) + M.dist (a n) x2 := by apply M.tri
                 _ = M.dist (a n) x1 + M.dist (a n) x2 := by rw [M.symm]
                 _ < ε/2 + ε/2                         := by linarith [an_near_x1, an_near_x2]
                 _ = ε                                 := by simp
  have dist_x1_x2_zero := arbitrarily_close_eq (M.dist x1 x2) (M.nonneg x1 x2) x1_x2_arbitrarily_close
  exact (M.eq_iff_dist_zero x1 x2).mpr dist_x1_x2_zero

-- If a(0), a(1), a(2), ... converges to x and f is continuous then f(a(0)), f(a(1)), f(a(2)), ... converges to f(x)
theorem apply_continuous_function_to_convergent_sequence (h1: converges M1 a x) (h2: continuous M1 M2 f): converges M2 (f ∘ a) (f x) := by
  intro ε ε_pos
  obtain ⟨δ, ⟨δ_pos, ε_δ_impl⟩⟩ := h2 x ε ε_pos
  obtain ⟨N, a_convergence_impl⟩ := h1 δ δ_pos
  exists N
  intro n N_leq_n
  have ε_δ_impl_an := ε_δ_impl (a n)
  have dist_an_x_lt_δ := a_convergence_impl n N_leq_n
  rw [M1.symm] at dist_an_x_lt_δ
  have dist_fan_fx_lt_ε := ε_δ_impl_an dist_an_x_lt_δ
  rw [M2.symm] at dist_fan_fx_lt_ε
  exact dist_fan_fx_lt_ε

-- The t-th tail of a sequence a(0), a(1), a(2) ... is the sequence a(t), a(t+1), a(t+2), ...
def tail {X: Type} (a: Nat → X) (t: Nat): Nat → X :=
  fun n => a (n + t)

-- If a sequence converges to x then so does every tail
theorem tail_converge (h: converges M a x) (t: Nat): converges M (tail a t) x := by
  intro ε ε_pos
  obtain ⟨N, conv_impl⟩ := h ε ε_pos
  exists N - t
  intro n
  simp
  rw [tail]
  exact conv_impl (n + t)

-- Given a function f: X → X and a point x: X, the orbit is the sequence x, f(x), f(f(x))), ...
def orbit (f: X → X) (x: X) : Nat → X :=
  fun n =>
  match n with
  | Nat.zero => x
  | Nat.succ p => f ((orbit f x) p)

theorem orbit_tail (f: X → X) (x: X): f ∘ (orbit f x) = tail (orbit f x) 1 := by
  ext
  rw [tail, orbit]
  rfl

-- If an orbit of f converges, the limit is a fixed point of f
theorem orbit_converge_to_fixed_point (h1: continuous M M f) (h2: converges M (orbit f x) L): f L = L := by
  have h3 := apply_continuous_function_to_convergent_sequence h2 h1
  rw [orbit_tail] at h3
  have h4 := tail_converge h2 1
  exact limit_unique h3 h4

def contraction (M: MetricSpace X) (T: X → X): Prop :=
  ∃ c: Real, 0 ≤ c ∧ c < 1 ∧ ∀ x y: X, M.dist (T x) (T y) ≤ c * (M.dist x y)

-- https://math.stackexchange.com/a/1800125
theorem contraction_continuous (M: MetricSpace X) (T: X → X) (h: contraction M T): continuous M M T := by
  obtain ⟨c, ⟨c_nonneg, _, contr_ineq⟩⟩ := h
  intro x ε ε_pos
  by_cases c_case: c = 0
  exists ε
  apply And.intro
  exact ε_pos
  intro y _
  simp [c_case] at contr_ineq
  calc
    M.dist (T x) (T y) ≤ 0 := by apply contr_ineq
                     _ < ε := ε_pos
  have c_pos: c > 0 := lt_of_le_of_ne c_nonneg (ne_comm.mp c_case)
  exists ε/c
  apply And.intro
  exact div_pos_iff.mpr (Or.inl ⟨ε_pos, c_pos⟩)
  intro y x_y_within_eps_div_c
  calc
    M.dist (T x) (T y) ≤ c * M.dist x y := by apply contr_ineq
                     _ < c * (ε / c)    := by apply (mul_lt_mul_left c_pos).mpr x_y_within_eps_div_c
                     _ = ε              := by rw [mul_div_cancel₀ ε c_case]

theorem geom_series_bound (c: Real) (n: Nat): 0 ≤ c → c < 1 → (∑ i in Finset.range n, c^i) ≤ 1 / (1 - c) := by
  sorry

theorem pow_reverse {c: Real} {m n: Nat}: 0 ≤ c → c < 1 → m ≤ n → c^n ≤ c^m := by
  sorry

-- show orbit is cauchy. hard part!
theorem orbit_cauchy {M: MetricSpace X} (h1: contraction M T): cauchy M (orbit T x0) := by
  intro ε ε_pos
  obtain ⟨c, ⟨c_nonneg, c_lt_one, contr_ineq⟩⟩ := h1
  by_cases h2: c = 0
  simp [h2] at contr_ineq
  exists 1
  intro m n ⟨one_leq_m, one_leq_n⟩
  calc
    M.dist (orbit T x0 m) (orbit T x0 n) = M.dist (T (orbit T x0 (m - 1))) (T (orbit T x0 (n - 1))) := by sorry
                                       _ ≤ 0 := by apply contr_ineq
                                       _ < ε := ε_pos
  -- three important lemmas. would move them outside body but they depend on c
  have h3 (x y: X) (n: Nat): M.dist (orbit T x n) (orbit T y n) ≤ c^n * M.dist x y := by
    induction n with
    | zero => {
      repeat simp [orbit]
    }
    | succ p h_induction => {
      rw [orbit, orbit]
      calc
        M.dist (T (orbit T x p)) (T (orbit T y p)) ≤ c * M.dist (orbit T x p) (orbit T y p) := by apply contr_ineq
                                                 _ ≤ c * (c^p * M.dist x y)               := mul_le_mul_of_nonneg_left h_induction c_nonneg
                                                 _ = c^(p+1) * M.dist x y                   := by ring
    }
  have h4 (x: X) (n: Nat): M.dist x (orbit T x n) ≤ (∑ i in Finset.range n, c^i) * M.dist x (T x) := by
    induction n with
    | zero => {
      rw [orbit]
      simp [(M.eq_iff_dist_zero x x).mp]
    }
    | succ p h_induction => {
      rw [orbit]
      calc
        M.dist x (T (orbit T x p)) ≤ M.dist x (orbit T x p) + M.dist (orbit T x p) (T (orbit T x p))                       := by sorry
                                 _ ≤ (∑ i ∈ Finset.range p, c^i) * M.dist x (T x) + M.dist (orbit T x p) (orbit T (T x) p) := by sorry
                                 _ ≤ (∑ i ∈ Finset.range p, c^i) * M.dist x (T x) + c^p * M.dist x (T x)                   := by sorry -- rw [h_funfact1 x (T x) p]
                                 _ = ((∑ i ∈ Finset.range p, c^i) + c^p) * M.dist x (T x)                                  := by sorry
                                 _ = (∑ i ∈ Finset.range (p+1), c^i) * M.dist x (T x)                                      := by sorry                   
    }
  have h5 (x: X) (n: Nat): M.dist x (orbit T x n) ≤ M.dist x (T x) / (1 - c) := by
    sorry
  let N: Nat := sorry -- should be greater than log_c(2 * ε * (1-c) / (M.dist x0 (T x0)))
  have h6: c^N / (1 - c) * M.dist x0 (T x0) < ε := sorry
  exists N
  intro m n ⟨N_leq_m, N_leq_n⟩
  by_cases h7: m ≤ n
  let d := n - m
  have h8: n = d + m := sorry
  rw [h8]
  have c_pow_nonnneg: c^m ≥ 0 := sorry
  calc
    M.dist (orbit T x0 m) (orbit T x0 (d + m)) = M.dist (orbit T x0 m) (orbit T (orbit T x0 d) m) := by sorry
                                             _ ≤ c^m * M.dist x0 (orbit T x0 d)                        := by apply h3
                                             _ ≤ c^m * (∑ i in Finset.range d, c^i) * M.dist x0 (T x0) := sorry
                                             _ ≤ c^m / (1 - c) * M.dist x0 (T x0)                      := sorry
                                             _ ≤ c^N / (1 - c) * M.dist x0 (T x0)                      := sorry
                                             _ < ε                                                     := h6

  let d := m - n
  have h7: m = d + n := sorry
  rw [h7]
  calc
    M.dist (orbit T x0 (d + n)) (orbit T x0 n) ≤ c^n * M.dist (orbit T x0 d) x0                        := by sorry
                                             _ = c^n * M.dist x0 (orbit T x0 d)                        := by sorry
                                             _ ≤ c^n * (∑ i in Finset.range d, c^i) * M.dist x0 (T x0) := by sorry
                                             _ ≤ c^n / (1 - c) * M.dist x0 (T x0)                      := by sorry
                                             _ ≤ c^N / (1 - c) * M.dist x0 (T x0)                      := by sorry
                                             _ < ε                                                     := h6

theorem easy_lemma {a b: Real} (h1: a ≤ b * a) (h2: a ≥ 0) (h3: b < 1): a = 0 := by
  apply Classical.not_not.mp
  apply Not.intro
  intro a_neq_zero
  have a_gt_zero := lt_of_le_of_ne h2 (ne_comm.mp a_neq_zero)
  have a_div_a_leq_b := (div_le_iff a_gt_zero).mpr h1
  rw [div_self a_neq_zero] at a_div_a_leq_b
  have b_not_lt_one := not_lt.mpr a_div_a_leq_b
  contradiction

theorem contraction_mapping_theorem {M: MetricSpace X} (h0: Nonempty X) (h1: complete M) (h2: contraction M T): ∃! x: X, T x = x := by
  -- assume X is nonempty, pick an arbitrary point
  let x0: X := Classical.choice h0
  -- define a sequence
  let a: Nat → X := orbit T x0
  -- show it is cauchy
  have a_cauchy: cauchy M a := orbit_cauchy h2
  -- since the sequence is cauchy it has a limit
  obtain ⟨x, a_converges_to_x⟩ := h1 a a_cauchy
  exists x
  -- need to show x is indeed a fixed point
  have x_fixed_point := orbit_converge_to_fixed_point (contraction_continuous M T h2) a_converges_to_x
  apply And.intro
  exact x_fixed_point
  -- now show point is unique
  intro y
  simp
  intro y_fixed_point
  apply eq_comm.mp
  obtain ⟨c, ⟨c_geq_zero, c_lt_one, contraction_ineq⟩⟩ := h2
  have x_y_dist_leq_c_mul_x_y_dist := calc
    M.dist x y = M.dist (T x) (T y) := by rw [x_fixed_point, y_fixed_point]
               _ ≤ c * (M.dist x y) := by apply contraction_ineq
  have x_y_dist_zero: M.dist x y = 0 := easy_lemma x_y_dist_leq_c_mul_x_y_dist (M.nonneg x y) c_lt_one
  exact (M.eq_iff_dist_zero x y).mpr x_y_dist_zero

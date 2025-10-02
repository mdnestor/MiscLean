
import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas

variable {X: Type} 

structure MeasurableSpace (X: Type) where
  measurable: Set (Set X)
  univ: measurable Set.univ
  compl: ∀ A : Set X, measurable A → measurable A.compl
  countable_union: ∀ A: Nat → Set X, (∀ n, measurable (A n)) → measurable (Set.iUnion A)

theorem measurable_empty (M: MeasurableSpace X): M.measurable ∅ := by
  have: ∅ = (@Set.univ X).compl := by
    simp [Set.compl]
  rw [this]
  apply M.compl
  exact M.univ


def pad_pair {X: Type} (A B: Set X): Nat → Set X :=
  fun n => match n with
  | 0 => A
  | 1 => B
  | _ => ∅

theorem pad_pair_union {X: Type} (A B: Set X): Set.iUnion (pad_pair A B) = A ∪ B := by
  ext
  constructor
  . intro h
    simp at h
    obtain ⟨i, hi⟩ := h
    cases i with
    | zero => exact Set.mem_union_left B hi
    | succ i' => cases i' with
    | zero => exact Set.mem_union_right A hi
    | succ i'' => contradiction
  . intro h
    cases h with
    | inl =>
      simp
      exists 0
    | inr =>
      simp
      exists 1

theorem measurable_union {M: MeasurableSpace X} {A B: Set X} (h1: M.measurable A) (h2: M.measurable B): M.measurable (A ∪ B) := by
  rw [←pad_pair_union A B]
  apply M.countable_union
  intro n
  cases n with
  | zero => exact h1
  | succ n' =>
    cases n' with
    | zero => exact h2
    | succ _ => simp [pad_pair]; exact measurable_empty M

theorem measurable_countable_inter {M: MeasurableSpace X} {A: Nat → Set X} (h: ∀ n, M.measurable (A n)): M.measurable (Set.iInter A) := by
  have: Set.iInter A = (Set.iUnion (fun n => (A n).compl)).compl := by
    ext
    simp [Set.compl]
  rw [this]
  apply M.compl
  apply M.countable_union
  intro n
  apply M.compl
  exact h n

theorem measurable_inter {M: MeasurableSpace X} {A B: Set X} (h1: M.measurable A) (h2: M.measurable B): M.measurable (A ∩ B) := by
  have: A ∩ B = (A.compl ∪ B.compl).compl := by
    ext
    simp [Set.compl]
  rw [this]
  apply M.compl
  apply measurable_union
  . apply M.compl
    exact h1
  . apply M.compl
    exact h2

theorem set_mem_iff {A: Set X} {x: X}: A x ↔ x ∈ A := by
  exact Eq.to_iff rfl

structure MeasureSpace (X: Type) extends MeasurableSpace X where
  measure: measurable → ENNReal
  measure_zero: measure ⟨∅, sorry⟩ = 0
  measure_countable_disjoint_union (A: Nat → Set X) (h1: ∀ n: Nat, measurable (A n)) (h2: ∀ i j: Nat, i ≠ j → A i ∩ A j = ∅): measure ⟨Set.iUnion A, countable_union A h1⟩ = tsum (fun n => measure ⟨A n, h1 n⟩)

theorem measure_disjoint_union {M: MeasureSpace X} {A B: Set X} (h1: M.measurable A) (h2: M.measurable B) (h3: A ∩ B = ∅): M.measure ⟨A ∪ B, set_mem_iff.mp (measurable_union h1 h2)⟩ = M.measure ⟨A, h1⟩ + M.measure ⟨B, h2⟩ := by
  sorry

structure ProbabilitySpace (X: Type) extends MeasureSpace X where
  total: measure ⟨Set.univ, univ⟩ = 1

theorem probability_compl {M: ProbabilitySpace X} {A: Set X} (h: M.measurable A): M.measure ⟨A, h⟩ + M.measure ⟨A.compl, M.compl A h⟩ = 1 := by
  have: A ∩ A.compl = ∅ := by
    ext
    simp [Set.compl]
  rw [←measure_disjoint_union h (M.compl A h) this]
  have: A ∪ A.compl = Set.univ := by exact Set.compl_subset_iff_union.mp fun ⦃a⦄ a => a
  rw [←M.total]
  congr

theorem probability_leq_one {M: ProbabilitySpace X} {A: Set X} (h: M.measurable A): M.measure ⟨A, h⟩ ≤ 1 := by
  rw [←probability_compl h]
  simp

theorem probability_compl' (M: ProbabilitySpace X) {A: Set X} (h: M.measurable A): M.measure ⟨A.compl, M.compl A h⟩ = 1 - M.measure ⟨A, h⟩ := by
  rw [←probability_compl h]
  rw [add_comm]
  have: M.measure ⟨A, h⟩ ≠ ⊤ := by
    intro
    have := probability_leq_one h
    simp_all [top_le_iff, ENNReal.one_ne_top]
  rw [ENNReal.add_sub_cancel_right this]


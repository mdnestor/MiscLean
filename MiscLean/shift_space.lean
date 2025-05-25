
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Algebra.Group.Action.Defs

variable { T G A: Type*}

instance shift [Mul G]: SMul G (G → A) := {
  smul := fun g x => fun h => x (h * g)
}

instance [Monoid G]: MulAction G (G → A) := {
  one_smul := by
    intro x
    ext g
    calc
      ((1 : G) • x) g = x (g * 1) := by rfl
                    _ = x g       := by rw [mul_one]
  mul_smul := by
    intro a b x
    ext g
    calc
      ((a * b) • x) g = x (g * (a * b)) := by rfl
                     _ = x ((g * a) * b) := by rw [mul_assoc]
                     _ = (b • x) (g * a) := by rfl
                     _ = (a • (b • x)) g := by rfl
}

class ShiftSpace [Mul G] [TopologicalSpace A] (Λ: Set (G → A)): Prop where
  closed: IsClosed Λ
  shift_invariant: ∀ x ∈ Λ, ∀ g: G, g • x ∈ Λ

open ShiftSpace

theorem univ [Mul G] [TopologicalSpace A]: ShiftSpace (Set.univ: Set (G → A)) := {
  closed := isClosed_univ
  shift_invariant := fun _ x _ => x
}

theorem empty [Mul G] [TopologicalSpace A]: ShiftSpace (∅: Set (G → A)) := {
  closed := by
    rw [←Set.compl_univ]
    exact isClosed_compl_iff.mpr isOpen_univ
  shift_invariant := fun _ x _ => x
}

theorem ShiftSpace_sInter [Mul T] [TopologicalSpace A] {Λs: Set (Set (T → A))} (h: ∀ Λ ∈ Λs, ShiftSpace Λ): ShiftSpace (Set.sInter Λs) := {
  closed := by
    apply isClosed_sInter
    exact fun Λ hΛ => (h Λ hΛ).1
  shift_invariant := fun x hx g Λ hΛ => (h Λ hΛ).2 x (hx Λ hΛ) g
  }

-- finite union of shift spaces is a shift space
theorem ShiftSpace_sUnion [Mul T] [TopologicalSpace A] {Λs: Set (Set (T → A))} [Finite Λs] (h: ∀ Λ ∈ Λs, ShiftSpace Λ): ShiftSpace (Set.sUnion Λs) := {
  closed := by
    apply isOpen_compl_iff.mp
    rw [Set.compl_sUnion]
    apply Set.Finite.isOpen_sInter
    apply Set.Finite.image
    assumption
    intro _ ⟨V, hV⟩
    simp [←hV.right]
    exact (h V hV.left).closed
  shift_invariant := by
    intro x ⟨i, hi⟩ t
    exists i
    exact ⟨hi.1, (h i hi.left).shift_invariant x hi.2 t⟩
  }

def FinBlock (X Y: Type*) := Σ D: Finset X, D → Y

def from_forbidden [Mul G] (F: Set (FinBlock G A)): Set (G → A) :=
  {x | ∀ N: Finset G, ∀ g: G, ⟨N, Set.restrict N (g • x)⟩ ∉ F}

theorem from_forbidden_antitone [Mul G] (F F': Set (FinBlock G A)) (h: F ⊆ F'): from_forbidden F' ⊆ from_forbidden F := by
  exact fun a h1 N g h2 => h1 N g (h h2)
  
theorem from_forbidden_empty [Mul G]: from_forbidden (∅: Set (FinBlock G A)) = Set.univ := by
  exact Set.eq_univ_iff_forall.mpr fun x N g a => a

theorem from_forbidden_univ [Nonempty G] [Mul G]: from_forbidden (Set.univ: Set (FinBlock G A)) = ∅ := by
  simp [from_forbidden]

theorem forbidden_shift [Monoid G] [TopologicalSpace A] (F: Set (FinBlock G A)): ShiftSpace (from_forbidden F) := {
  closed := sorry
  shift_invariant := by
    intro _ h _ _ _
    rw [smul_smul]
    apply h
}

def patterns (Λ: Set (G → A)): Set (FinBlock G A) := 
  fun ⟨Ω, p⟩ => ∃ x ∈ Λ, Set.restrict Ω x = p

theorem shift_space_iff [Monoid G] [TopologicalSpace A] (Λ: Set (G → A)): ShiftSpace Λ ↔ ∃ F, Λ = from_forbidden F := by
  constructor
  . intro h
    exists fun ⟨Ω, p⟩ => ∀ x ∈ Λ, ∀ g: G, Ω.restrict (g • x) ≠ p
    ext x
    constructor
    . intro hx N g
      exact fun a => a x hx g rfl
    . intro hx
      simp_all [from_forbidden]
      sorry
  . intro ⟨F, hF⟩
    rw [hF]
    exact forbidden_shift F

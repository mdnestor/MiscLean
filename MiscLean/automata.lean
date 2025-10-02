
/- Ch. 1 of "Intro. to Theory of Computation" (3rd ed.) by Sipser -/

-- sets 
def subset (X: Type): Type :=
  X → Prop

def singleton {X: Type} (x0: X): subset X :=
  fun x => x = x0

-- automata

structure FinAutomaton (α: Type) where
  state: Type
  transition: state → α → state
  initial: state
  final: subset state

def run (M: FinAutomaton α) (string: List α): M.state :=
  match string with
  | [] => M.initial
  | head :: tail => M.transition (run M tail) head

def accept (M: FinAutomaton α) (string: List α): Prop :=
  let state := run M string
  M.final state

def reject (M: FinAutomaton α) (string: List α): Prop :=
  ¬(accept M string)

structure NondetFinAutomaton (α: Type) where
  state: Type
  transition: state → α → subset state
  initial: state
  final: subset state

def NFA.run (M: NondetFinAutomaton α) (string: List α): subset M.state :=
  match string with
  | [] => singleton M.initial
  | head :: tail => sorry

def NFA.accept (M: NondetFinAutomaton α) (string: List α): Prop :=
  ∃ s: M.state, (NFA.run M string) s ∧ M.final s

def NFA.reject (M: NondetFinAutomaton α) (string: List α): Prop :=
  Not (NFA.accept M string)

def NFA.language_of (M: NondetFinAutomaton α): subset (List α) :=
  fun string => NFA.accept M string

-- convert DDA to NFA and back
def DFA.toNFA (M: FinAutomaton α): NondetFinAutomaton α := {
  state := M.state
  transition := fun s a => singleton (M.transition s a)
  initial := M.initial
  final := M.final
}

def NFA.toDFA (M: NondetFinAutomaton α): FinAutomaton α := {
  state := subset M.state
  transition := fun S a => fun s1 => ∃ s0: M.state, S s0 ∧ (M.transition s0 a) s1
  initial := singleton M.initial
  final := singleton M.final
}

-- languages

def Language (α: Type): Type := subset (List α)

def language_of (M: FinAutomaton α): Language α :=
  fun string => accept M string

def regular (L: Language α): Prop :=
  ∃ M: FinAutomaton α, language_of M = L

theorem equivalence (M: NondetFinAutomaton α): ∃ M': FinAutomaton α, NFA.language_of M = language_of M' := by
  sorry

theorem corollary (L: Language α): regular L ↔ ∃ M: NondetFinAutomaton α, NFA.language_of M = L := by
  sorry

-- helpers
def all_left: List (Sum α0 α1) → Prop
  | [] => True
  | (Sum.inl _) :: tail => all_left tail
  | (Sum.inr _) :: _ => False

def all_right: List (Sum α0 α1) → Prop
  | [] => True
  | (Sum.inl _) :: tail => all_right tail
  | (Sum.inr _) :: _ => False

def convert_left: List (Sum α0 α1) → List α0
  | [] => []
  | (Sum.inl head) :: tail => head :: convert_left tail
  | (Sum.inr _) :: tail => convert_left tail

def convert_right: List (Sum α0 α1) → List α1
  | [] => []
  | (Sum.inl _) :: tail => convert_right tail
  | (Sum.inr head) :: tail => head :: convert_right tail

/- union, concatenation, and star of languages -/
def union (L0: Language α0) (L1: Language α1): Language (Sum α0 α1) :=
  fun string => (all_left string ∧ L0 (convert_left string)) ∨ (all_right string ∧ L1 (convert_right string))

def concat (L0: Language α0) (L1: Language α1): Language (Sum α0 α1) :=
  fun string => ∃ x y: List (Sum α0 α1), (string = List.append x y) ∧ (all_left x) ∧ (all_right y) ∧ L0 (convert_left x) ∧ L1 (convert_right y)

def collapse (L: List (List α)): List α :=
  match L with
  | [] => []
  | head :: tail => List.append (collapse tail) head

def star (L: Language α): Language (List α) :=
  fun string => L (collapse string)

def star2 (L: Language α): Language α :=
  fun string => ∃ Ls: List (List α), (collapse Ls = string) ∧ (∀ x ∈ Ls, L x)

theorem union_of_regular_is_regular (L0: Language α0) (L1: Language α1): regular L0 ∧ regular L1 -> regular (union L0 L1) := by
  intro ⟨L0_regular, L1_regular⟩
  -- let M1 and M2 be the corresponding automata
  obtain ⟨M0, h0⟩ := L0_regular
  obtain ⟨M1, h1⟩ := L1_regular 
  -- now construct an automaton to recognize the union
  let M : FinAutomaton (Sum α0 α1) := {
    state := M0.state × M1.state
    transition := fun (s0, s1) => fun a => match a with
    | Sum.inl a => (M0.transition s0 a, s1)
    | Sum.inr a => (s0, M1.transition s1 a)
    initial := (M0.initial, M1.initial)
    final := fun (s0, s1) => (M0.final s0) ∨ (M1.final s1)
  }
  exists M
  apply funext
  intro string
  rw [language_of, union]
  -- ?? seems to be a problem here
  sorry

theorem concat_of_regular_is_regular (L0: Language α0) (L1: Language α1): (regular L0) ∧ (regular L1) -> regular (concat L0 L1) := by
  sorry

theorem star_of_regular_is_regular (L: Language α): regular L -> regular (star L) := by
  sorry

/- todo: regular expressions and pumping lemma -/

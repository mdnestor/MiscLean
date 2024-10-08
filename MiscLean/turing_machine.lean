structure TuringMachine where /- generalizes to tapes besides ℤ 💅 -/
  tape: Type
  symbol: Type
  state: Type
  shift: Type
  translate: tape × shift → tape
  update: state × symbol → state × symbol × shift

structure DiscreteDynamicalSystem where
  state: Type
  update: state → state

def F (M: TuringMachine) (h: DecidableEq M.tape): DiscreteDynamicalSystem := {
  state := (M.tape → M.symbol) × M.state × M.tape
  update := fun (u, s, x) => by
    have (y1, y2, y3) := M.update (s, (u x))
    exact (
      fun x0 => if x = x0 then y2 else (u x0),
      y1,
      M.translate (x, y3)
    )
}

/-
some theorem to cap it off?
that there is a turing machine U
such that for any other given turing machine M
you can encode into an input of U
and simulate it in U
-/

structure IOMachine where
  machine: TuringMachine
  h: DecidableEq machine.tape
  input: Type
  output: Type
  encode: input → (F machine h).state
  decode: (F machine h).state → output

def run (S: DiscreteDynamicalSystem) (x0: S.state): Nat → S.state :=
  fun n => match n with
  | Nat.zero => x0
  | Nat.succ n_previous => S.update ((run S x0) n_previous)

def reaches (S: DiscreteDynamicalSystem) (x0 x1: S.state): Prop :=
  ∃ n: Nat, (run S x0) n = x1

def halts_on_input (M: IOMachine) (h: DecidableEq M.machine.tape) (s0: M.machine.state) (i: M.input): Prop :=
  ∃ n: Nat, ((run (F M.machine h) (M.encode i)) n).2.1 = s0

def halts (M: IOMachine) (h: DecidableEq M.machine.tape) (s_halt: M.machine.state): Prop :=
  ∀ i: M.input, halts_on_input M h s_halt i

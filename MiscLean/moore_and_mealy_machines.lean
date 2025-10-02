structure MealyMachine where
  state: Type
  input: Type
  output: Type
  update: state × input -> state × output

structure MooreMachine where
  state: Type
  input: Type
  output: Type
  update: state × input -> state
  read: state -> output
  
def convert (M: MooreMachine): MealyMachine := {
  state := M.state,
  input := M.input,
  output := M.output,
  update := fun (x, y) => (M.update (x, y), M.read (M.update (x, y))),
}

import Complexity.TuringMachine

def succ_tm : TM 1 (Fin 4) Char :=
  {
    transition := fun state symbols =>
      match state with
      -- we still need to add one (initially or carry)
      | 0 => match symbols 0 with
        | ' ' => (2, fun _ => ' ', some '1', fun _ => .stay)
        | '0' => (1, fun _ => ' ', some '1', fun _ => .right)
        | '1' => (0, fun _ => ' ', some '0', fun _ => .right)
        | _ => (0, fun _ => ' ', none, fun _ => .right) -- should not happen
      -- nothing to add, only copy input to output
      | 1 => match symbols 0 with
        | ' ' => (2, fun _ => ' ', none, fun _ => .stay)
        | '0' => (1, fun _ => ' ', some '0', fun _ => .right)
        | '1' => (1, fun _ => ' ', some '1', fun _ => .right)
        | _ => (1, fun _ => ' ', none, fun _ => .right) -- should not happen
      -- finished
      | st => (st, fun _ => ' ', none, fun _ => .stay)
    startState := 0
    acceptState := 2
    rejectState := 3
  }

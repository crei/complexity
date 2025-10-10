import Complexity.TuringMachine
import Complexity.Dyadic

import Mathlib

-- A Turing machine that computes the successor of a
-- reversely encoded dyadic number
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

-- TODO we also need a lemma that models the principle of addition that is
-- used by the machine.

-- lemma copies_in_state_one {σ : Configuration 1 (Fin 4) Char}
--   (hstate : σ.state = 1) :
--   let inputTape := σ.tapes 0
--   let remainingInput := inputTape.head :: inputTape.right
--   let (finalConf, output) := succ_tm.run_for_steps σ (remainingInput.length + 1)
--   finalConf.state = succ_tm.acceptState ∧ output = remainingInput := by
--   intros inputTape remainingInput
--   simp [remainingInput]
--   induction inputTape.right generalizing σ with
--   | nil =>
--     simp [TM.run_for_steps, succ_tm, hstate, TM.step]

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
        | '1' => (1, fun _ => ' ', some '2', fun _ => .right)
        | '2' => (0, fun _ => ' ', some '1', fun _ => .right)
        | _ => (0, fun _ => ' ', none, fun _ => .right) -- should not happen
      -- nothing to add, only copy input to output
      | 1 => match symbols 0 with
        | ' ' => (2, fun _ => ' ', none, fun _ => .stay)
        | '1' => (1, fun _ => ' ', some '1', fun _ => .right)
        | '2' => (1, fun _ => ' ', some '2', fun _ => .right)
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

-- lemma copies_in_state_one_of_dyadic
--   {σ : Configuration 1 (Fin 4) Char}
--   (hstate : σ.state = 1)
--   (hd : ∀ c ∈ ((σ.tapes 0).head :: (σ.tapes 0).right), c = '1' ∨ c = '2') :
--   let inputTape := σ.tapes 0
--   let remainingInput := inputTape.head :: inputTape.right
--   let (finalConf, output) := succ_tm.run_for_steps σ (remainingInput.length + 1)
--   finalConf.state = succ_tm.acceptState ∧ output = remainingInput := by
--   intro inputTape remainingInput
--   have hhead : inputTape.head = '0' ∨ inputTape.head = '1' := by
--     simp [hd, inputTape, hd]

--     simp [List.mem_cons, hd]
--   -- We induct on the structure of the "right" list, keeping σ generalized.
--   induction inputTape.right generalizing σ with
--   | nil =>
--     -- Unfold the run (n+1) convention in your `TM.run_for_steps`
--     -- and the one-step behavior of succ_tm at state 1.
--     -- The `simp` below picks the correct branch using `hstate` and `hhead`.
--     rcases hhead with h0 | h1
--     · simp [remainingInput, TM.run_for_steps, succ_tm, hstate, TM.step, h0]
--     · simp [remainingInput, TM.run_for_steps, succ_tm, hstate, TM.step, h1]
--   | cons c cs ih =>
--     -- Inductive case: right = c :: cs
--     -- We know the head and c are 0/1 by hd; we split on head and use simp.
--     have hhead : inputTape.head = '0' ∨ inputTape.head = '1' := by
--       exact hd inputTape.head (by simp)
--     rcases hhead with h0 | h1
--     · -- head = '0': one step emits '0' and moves right; then apply IH
--       -- After that first copy step, we remain in state 1; the remainingInput shrinks to c::cs.
--       -- Your `run_for_steps` does the n steps first, then one step; we adjust lengths accordingly.
--       simp [remainingInput, TM.run_for_steps, succ_tm, hstate, TM.step, h0]
--       -- Now we must apply the IH to the updated configuration after that (n) prefix.
--       -- To justify dyadic well-formedness for the tail, use hd on c and cs.
--       -- The `simp` goal reduces exactly to IH’s statement; we discharge the hypothesis as follows:
--       refine ih ?hstate' ?hd'
--       · -- state stays 1 in the copy branch
--         simp [succ_tm, TM.step, hstate, h0]
--       · -- All remaining symbols (c :: cs) are still 0/1
--         intro d hdmem
--         have : d ∈ (inputTape.head :: c :: cs) := by simpa [List.mem_cons] using Or.inr hdmem
--         exact hd d (by simpa)
--     · -- head = '1': symmetric to the '0' case
--       simp [remainingInput, TM.run_for_steps, succ_tm, hstate, TM.step, h1]
--       refine ih ?hstate' ?hd'
--       · simp [succ_tm, TM.step, hstate, h1]
--       · intro d hdmem
--         have : d ∈ (inputTape.head :: c :: cs) := by simpa [List.mem_cons] using Or.inr hdmem
--         exact hd d (by simpa)


lemma copies_in_state_one_of_dyadic
  {σ : Configuration 1 (Fin 4) Char}
  (hstate : σ.state = 1)
  (hd : ∀ c ∈ ((σ.tapes 0).head :: (σ.tapes 0).right), c = '0' ∨ c = '1') :
  let inputTape := σ.tapes 0
  let remainingInput := inputTape.head :: inputTape.right
  let (finalConf, output) := succ_tm.run_for_steps σ (remainingInput.length + 1)
  finalConf.state = succ_tm.acceptState ∧ output = remainingInput := by
  intro inputTape remainingInput
  revert σ
  induction (σ.tapes 0).right with
  | nil =>
    intro σ
    rcases hd _ (by simp) with h0 | h1
    all_goals simp [remainingInput, TM.run_for_steps, succ_tm, TM.step, hstate, *]
  | cons c cs ih =>
    intro σ
    rcases hd _ (by simp) with h0 | h1
    have hd' : ∀ d ∈ (c :: cs), d = '0' ∨ d = '1' := by intro d hdmem; exact hd d (by simp [hdmem])
    all_goals (
      simp [remainingInput, TM.run_for_steps, succ_tm, TM.step, hstate, *]
      exact ih _ (by simp [succ_tm, TM.step, hstate, *]) hd'
    )

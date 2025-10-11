import Mathlib
import Complexity.TuringMachine

/-!
# Output Redirection

This file defines a simple transformation: taking a TM and creating a new TM
that writes its output to a designated tape instead of the output stream.

This is a building block for composition.
-/

open TM

namespace OutputRedirect

/-- Redirect output to a new tape.
    Given a TM with k work tapes, creates a TM with k+1 work tapes where
    the (k+1)-th tape accumulates what would have been the output. -/
def redirect_output {k : Nat} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Q]
    (tm : TM k Q Γ) : TM (k + 1) Q Γ where
  transition σ symbols_read :=
    -- Read the first k+1 symbols (input + k work tapes, ignoring the output tape)
    let tm_symbols : Fin (k + 1) → Γ := fun i => symbols_read (Fin.castSucc i)
    let (q', writes, output, moves) := tm.transition σ tm_symbols
    -- Extend writes to k+1 tapes
    let extended_writes : Fin (k + 1) → Γ := fun i =>
      if h : i.val < k then
        writes ⟨i.val, h⟩
      else
        -- Write output to the (k+1)-th work tape
        match output with
        | some c => c
        | none => default
    -- Extend moves to k+2 tapes (input + k+1 work tapes)
    let extended_moves : Fin (k + 1 + 1) → Movement := fun i =>
      if h : i.val < k + 1 then
        moves ⟨i.val, h⟩
      else
        -- Move the output tape right if we wrote something
        match output with
        | some _ => Movement.right
        | none => Movement.stay
    (q', extended_writes, none, extended_moves)
  startState := tm.startState
  acceptState := tm.acceptState
  rejectState := tm.rejectState

/-- The index of the output tape in the redirected machine -/
def output_tape_idx (k : Nat) : Fin (k + 1 + 1) :=
  ⟨k + 1, by omega⟩

/-- A single step of the redirected machine matches the original -/
lemma redirect_output_step {k : Nat} {Q Γ : Type*}
    [Inhabited Γ] [DecidableEq Q]
    (tm : TM k Q Γ)
    (conf_orig : Configuration k Q Γ)
    (conf_redir : Configuration (k + 1) Q Γ)
    (h_state : conf_redir.state = conf_orig.state)
    (h_tapes : ∀ i : Fin (k + 1), conf_redir.tapes (Fin.castSucc i) = conf_orig.tapes i) :
    let tm' := redirect_output tm
    let (conf_orig', out_orig) := tm.step conf_orig
    let (conf_redir', out_redir) := tm'.step conf_redir
    conf_redir'.state = conf_orig'.state ∧
    (∀ i : Fin (k + 1), conf_redir'.tapes (Fin.castSucc i) = conf_orig'.tapes i) ∧
    out_redir = none := by
  intro tm'
  simp only [TM.step]
  by_cases h_accept : ((conf_orig.state = tm'.acceptState) ∨ (conf_orig.state = tm'.rejectState))
  · simp [h_accept]; sorry
  · sorry

/-- The redirected machine preserves the original machine's behavior,
    except output goes to a tape instead. -/
theorem redirect_output_correct {k : Nat} {Q Γ : Type*}
    [Inhabited Γ] [DecidableEq Q]
    (tm : TM k Q Γ) (input : List Γ) (t : Nat) :
    let (conf_orig, output_orig) := tm.run_on_input_for_steps input t
    let tm' := redirect_output tm
    let (conf_redir, output_redir) := tm'.run_on_input_for_steps input t
    -- States match
    conf_redir.state = conf_orig.state ∧
    -- No output in redirected version
    output_redir = [] ∧
    -- Output tape contains the original output
    let output_tape := conf_redir.tapes (output_tape_idx k)
    (output_tape.head :: output_tape.right) = output_orig ++ [default] := by
  -- This should be proven by induction on t, using redirect_output_step
  sorry

end OutputRedirect

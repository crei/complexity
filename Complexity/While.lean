import Complexity.TuringMachine
import Complexity.Dyadic
import Complexity.TapeLemmas
import Complexity.AbstractTape

import Mathlib

inductive WhileState (Q : Type*) where
  | main (q : Fin 2)
  | sub_routine (q : Q)
  deriving DecidableEq

--- Repeatedly run a sub routine as long as a condition on the symbol
--- at the first head is true.
def Routine.while {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Q]
  (tm : TM k.succ Q Γ) (condition : Γ → Bool) :
  TM k.succ (WhileState Q) Γ :=
  let σ := fun state symbols =>
    match state with
    | .main 0 => if condition (symbols 0) then
        (.sub_routine tm.startState, (symbols · , none))
      else
        (.main 1, (symbols ·, none))
    | .sub_routine s => if s = tm.stopState then
        (.main 0, (symbols ·, none))
      else
        let ⟨s, op⟩ := tm.transition s symbols
        (.sub_routine s, op)
    | s => (s, (symbols ·, none))
  TM.mk σ (.main 0) (.main 1)

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
def Routines.while {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Q]
  (condition : Γ → Bool) (tm : TM k.succ Q Γ) :
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

lemma Routines.while.inert_after_stop {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Q]
  (tm : TM k.succ Q Γ) (condition : Γ → Bool) :
  (Routines.while condition tm).inert_after_stop := by
  intro conf h_is_stopped
  ext <;> simp_all [Transition.step, performTapeOps, Routines.while]

theorem Routines.while.semantics {k : ℕ} {Q Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  (condition : Γ → Bool)
  (tm : TM k.succ Q Γ)
  (tapes : ℕ → Fin k.succ → Turing.Tape Γ)
  (h_transform : ∀ i, tm.transforms (tapes i) (tapes i.succ))
  (h_stops : ∃ m, ¬condition (tapes m 0).head) :
  (Routines.while condition tm).transforms (tapes 0) (tapes (Nat.find h_stops)) := by
  sorry

import Complexity.AbstractTape
import Complexity.TuringMachine
import Complexity.TapeLemmas
import Complexity.Routines
import Complexity.MoveUntil
import Complexity.TMComposition
import Complexity.WithTapes

import Mathlib

def pop_char : TM 1 (Fin 2) SChar :=
  let σ := fun _ _ => (1, (fun _ => (.blank, .some .right)))
  TM.mk σ 0 1

--- This is a 1-tape Turing machine that removes the left-most word
--- from the tape.
def pop := (Routines.while (· ≠ .sep) pop_char).seq pop_char

@[simp]
theorem pop.eval {w : List Char} {ws₁ ws₂ : List (List Char)} :
  pop.eval (list_to_tape ∘ [w :: ws₁].get) =
    .some (list_to_tape ∘ [ws₁].get) := by
  let semantics := fun tapes => (tapes 0).
  let tapes : ℕ → Fin 1 → Turing.Tape SChar :=
    (fun i j => Turing.Tape.mk₁ ((list_to_string (w :: ws₁)).drop i))
  have h_tapes₀ : tapes 0 = (list_to_tape ∘ [w :: ws₁].get) := by
    sorry
  have h_inner : ∀ i, pop_char.eval (tapes i) = tapes i.succ := by
    sorry
  let x := Routines.while.eval (condition := (· ≠ .sep)) (tm := pop_char) tapes h_inner
  simp at x
  rw [← h_tapes₀]
  simp [pop, x]


  sorry

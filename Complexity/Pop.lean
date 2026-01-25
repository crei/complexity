import Complexity.AbstractTape
import Complexity.TuringMachine
import Complexity.TapeLemmas
import Complexity.Routines
import Complexity.MoveUntil
import Complexity.TMComposition
import Complexity.WithTapes

import Mathlib

def pop_char : TM 1 (Fin 2) SChar :=
  let σ := fun state symbols => match state with
    | 0 => (1, (fun _ => (.blank, .some .right)))
    | 1 => (1, (symbols ·, .none))
  TM.mk σ 0 1

lemma pop_char.inert_after_stop :
  pop_char.inert_after_stop := by
  intro conf h_is_stopped
  ext <;> simp_all [Transition.step, performTapeOps, pop_char]

@[simp]
lemma pop_char.eval (tape : Turing.Tape SChar) :
  pop_char.eval (fun _ => tape) = .some (fun _ => (tape.write .blank).move .right) := by
  apply TM.eval_of_transforms
  exact TM.transforms_of_inert pop_char _ _ pop_char.inert_after_stop ⟨1, rfl⟩

--- This is a 1-tape Turing machine that removes the left-most word
--- from the tape.
def pop := (Routines.while (· ≠ .sep) pop_char).seq pop_char

@[simp]
theorem pop.eval {w : List Char} {ws₁ ws₂ : List (List Char)} :
  pop.eval (list_to_tape ∘ [w :: ws₁].get) =
    .some (list_to_tape ∘ [ws₁].get) := by
  let tapes : ℕ → Fin 1 → Turing.Tape SChar :=
    (fun i j => Turing.Tape.mk₁ ((list_to_string (w :: ws₁)).drop i))
  have h_tapes₀ : tapes 0 = (list_to_tape ∘ [w :: ws₁].get) := by
    funext i; simp [tapes, list_to_tape]
  have h_inner : ∀ i, pop_char.eval (tapes i) = tapes i.succ := by
    intro i
    simp [tapes]


    simp [pop_char, TM.eval, TM.configurations, Transition.step, tapes]
    sorry
  let x := Routines.while.eval (condition := (· ≠ .sep)) (tm := pop_char) tapes h_inner
  simp at x
  rw [← h_tapes₀]
  simp [pop, x]


  sorry

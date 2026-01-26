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
lemma pop_char.eval (tapes : Fin 1 → Turing.Tape SChar) :
  pop_char.eval tapes = .some (fun _ => ((tapes 0).write .blank).move .right) := by
  apply TM.eval_of_transforms
  exact TM.transforms_of_inert pop_char _ _ pop_char.inert_after_stop ⟨1, sorry⟩

--- This is a 1-tape Turing machine that removes the left-most word
--- from the tape.
def pop := (Routines.while (· ≠ .sep) pop_char).seq pop_char

@[simp]
theorem pop.eval {w : List Char} {ws₁ : List (List Char)} :
  pop.eval (list_to_tape ∘ [w :: ws₁].get) =
    .some (list_to_tape ∘ [ws₁].get) := by
  have h_blank : SChar.blank = default := by rfl
  let tapes : ℕ → Fin 1 → Turing.Tape SChar :=
    (fun i j => Turing.Tape.mk₁ ((list_to_string (w :: ws₁)).drop i))
  have h_tapes₀ : tapes 0 = (list_to_tape ∘ [w :: ws₁].get) := by
    funext i; simp [tapes, list_to_tape]
  have h_inner : ∀ i, ((TM.eval pop_char (tapes i)) = Part.some (tapes i.succ)) := by
    simp [tapes, pop_char.eval, h_blank]
  have h_terminate : PartENat.find (fun i => (tapes i 0).head = SChar.sep) =
      Part.some w.length := by
    rw [Part.eq_some_iff]
    use ⟨w.length, by simp [tapes]⟩
    simp only [Fin.isValue, PartENat.find_get]
    rw [Nat.find_eq_iff]
    constructor
    · simp [tapes]
    · intro n h_n_lt
      simp only [Turing.Tape.mk₁, Turing.Tape.mk₂, list_to_string_cons, Fin.isValue,
        Turing.Tape.mk'_head, Turing.ListBlank.head_mk, tapes]
      rw [List.drop_eq_getElem_cons (by simp; omega)]
      simp [h_n_lt, List.coe_schar_getElem_neq_sep]
  have h_move_blank : (fun x ↦ Turing.Tape.move .right (.write .blank (tapes w.length 0))) =
      list_to_tape ∘ [ws₁].get := by
    funext i; simp [h_blank, tapes, list_to_tape]
  rw [← h_tapes₀]
  let h_eval := Routines.while.eval' (condition := (· ≠ .sep)) (tm := pop_char) tapes h_inner
  simp at h_eval
  simpa [pop, h_eval, h_terminate, pop_char.eval] using h_move_blank

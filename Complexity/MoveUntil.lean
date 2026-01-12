import Complexity.TuringMachine
import Complexity.Dyadic
import Complexity.TapeLemmas
import Complexity.AbstractTape
import Complexity.While

import Mathlib

--- A 1-tape Turing machine that moves its head in a given direction
--- once and then halts.
def Routines.move {Γ} [Inhabited Γ]
  (dir : Turing.Dir) :
  TM 1 (Fin 2) Γ :=
  let σ := fun state symbols =>
    match state with
    | 0 => (1, (symbols ·, some dir))
    | 1 => (1, (symbols ·, none))
  TM.mk σ 0 1

lemma Routines.move.inert_after_stop {Γ} [Inhabited Γ]
  (dir : Turing.Dir) :
  (Routines.move (Γ := Γ) dir).inert_after_stop := by
  intro conf h_is_stopped
  ext <;> simp_all [Transition.step, performTapeOps, Routines.move]

lemma Routines.move.semantics {Γ} [Inhabited Γ] [DecidableEq Γ]
  (tape : Turing.Tape Γ)
  (dir : Turing.Dir) :
  (Routines.move dir).transforms (fun _ => tape) (fun _ => Turing.Tape.move dir tape) := by
  let tm := Routines.move (Γ := Γ) dir
  exact TM.transforms_of_inert tm _ _ (move.inert_after_stop dir) ⟨1, rfl⟩

--- A 1-tape Turing machine that moves its head
--- in a given direction until a condition is met.
def move_until {Γ} [Inhabited Γ]
  (dir : Turing.Dir) (stop_condition : Γ → Bool) :=
  Routines.while (¬stop_condition ·) (Routines.move dir)

theorem move_until.right_semantics {Γ} [Inhabited Γ] [DecidableEq Γ]
  (tape : Turing.Tape Γ)
  (stop_condition : Γ → Bool)
  (h_stop : ∃ n : ℕ, stop_condition (tape.nth n)) :
  (move_until .right stop_condition).transforms
    (fun _ => tape)
    (fun _ => tape.move_int (Nat.find h_stop)) := by
  let h_while := Routines.while.semantics
    (¬stop_condition ·)
    (Routines.move .right)
    (fun n => fun i => tape.move_int n)
    (by
      intro i
      have : tape.move_int (↑i + 1) = (tape.move_int ↑i).move .right := by
        simp [← move_int_one]
      simpa [this] using Routines.move.semantics (tape.move_int i) .right
    )
    (by simp [h_stop, Turing.Tape.move_int])
  simpa [move_until, Turing.Tape.move_int] using h_while

theorem move_until.left_semantics {Γ} [Inhabited Γ] [DecidableEq Γ]
  (tape : Turing.Tape Γ)
  (stop_condition : Γ → Bool)
  (h_stop : ∃ n : ℕ, stop_condition (tape.nth (-n))) :
  (move_until .left stop_condition).transforms
    (fun _ => tape)
    (fun _ => tape.move_int (-(Nat.find h_stop))) := by
  let h_while := Routines.while.semantics
    (¬stop_condition ·)
    (Routines.move .left)
    (fun n => fun _ => tape.move_int (-n))
    (by
      intro i
      simp
      have : tape.move_int (-1 + -i) = (tape.move_int (-i)).move .left := by
        simp [← move_int_neg_one, Int.add_comm]
      simpa [this] using Routines.move.semantics (tape.move_int (-i)) .left
    )
    (by simp [h_stop])
  simp at h_while
  simpa [move_until, Turing.Tape.move_int] using h_while

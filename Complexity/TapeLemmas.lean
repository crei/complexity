import Complexity.TuringMachine
import Mathlib.Computability.Tape

@[simp]
theorem Tape.write_mk'_list {Γ} [Inhabited Γ] (a b : Γ) (L : Turing.ListBlank Γ) (R : List Γ) :
    (Turing.Tape.mk' L (Turing.ListBlank.mk (a :: R))).write b =
      Turing.Tape.mk' L (Turing.ListBlank.mk (b :: R)) := by
  rw [← Turing.ListBlank.cons_mk]
  simp only [Turing.Tape.write_mk']
  simp only [Turing.ListBlank.cons_mk]

@[simp]
theorem Tape.write_mk'empty {Γ} [Inhabited Γ] (b : Γ) (L : Turing.ListBlank Γ) :
    (Turing.Tape.mk' L (Turing.ListBlank.mk [])).write b =
      Turing.Tape.mk' L (Turing.ListBlank.mk [b]) := by
  rfl


@[simp]
theorem Tape.move_left_right_iter {Γ} [Inhabited Γ] (T : Turing.Tape Γ) (n : ℕ) :
    (Turing.Tape.move .left)^[n] ((Turing.Tape.move .right)^[n] T) = T := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ, Function.comp_apply]
    rw [Function.Commute.iterate_self (Turing.Tape.move Turing.Dir.left)]
    simp [ih]

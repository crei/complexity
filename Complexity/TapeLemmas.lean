import Complexity.TuringMachine
import Mathlib.Computability.Tape

@[simp]
theorem Tape.write_mk'_list {Γ} [Inhabited Γ] (a b : Γ) (L : Turing.ListBlank Γ) (R : List Γ) :
    (Turing.Tape.mk' L (Turing.ListBlank.mk (a :: R))).write b =
      Turing.Tape.mk' L (Turing.ListBlank.mk (b :: R)) := by
  rw [← Turing.ListBlank.cons_mk]
  simp

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

@[simp]
lemma Tape.nth_of_empty {Γ} [Inhabited Γ] (i : ℤ) :
    (Turing.Tape.mk₁ []).nth i = (default : Γ) :=
  match i with
  | 0 => by simp; rfl
  | (_ + 1 : ℕ) => by simp; rfl
  | Int.negSucc k => by unfold Turing.Tape.nth; simp; rfl

@[simp]
lemma Tape.mk₂_nth {Γ} [Inhabited Γ] (i : ℤ)
  (A B : List Γ) :
  (Turing.Tape.mk₂ A B).nth i =
    if i < 0 then A.getD (-i - 1).toNat default else B.getD i.toNat default :=
  match i with
  | 0 => by
      unfold Turing.Tape.mk₂
      match B with
      | [] => simp_all
      | x :: xs => simp_all
  | (n + 1 : ℕ) => by
      unfold Turing.Tape.mk₂ Turing.Tape.nth
      have h : ¬((n : Int) + 1 < 0) := by linarith
      simp only [Turing.Tape.mk'_right, Turing.ListBlank.tail_mk, Turing.ListBlank.nth_mk,
        Nat.cast_add, Nat.cast_one, h, ↓reduceIte, Int.toNat_natCast_add_one,
        List.getD_eq_getElem?_getD]
      match B with
      | [] => rfl
      | x :: xs => simp only [List.getElem?_cons_succ]; rfl
  | Int.negSucc k => by unfold Turing.Tape.nth; simp; rfl

lemma Tape.mk₂_nth' {Γ} [Inhabited Γ] (i : ℤ)
  (A B : List Γ) :
  (Turing.Tape.mk₂ A B).nth i = match i with
    | Int.ofNat n => B.getD n default
    | Int.negSucc n => A.getD n default :=
  match i with
  | 0 => by
      unfold Turing.Tape.mk₂
      match B with
      | [] => simp_all
      | x :: xs => simp_all
  | (n + 1 : ℕ) => by
      unfold Turing.Tape.mk₂ Turing.Tape.nth
      simp only [Turing.Tape.mk'_right, Turing.ListBlank.tail_mk, Turing.ListBlank.nth_mk,
        List.getD_eq_getElem?_getD]
      match B with
      | [] => rfl
      | x :: xs => simp only [List.getElem?_cons_succ]; rfl
  | Int.negSucc k => by unfold Turing.Tape.nth; simp; rfl

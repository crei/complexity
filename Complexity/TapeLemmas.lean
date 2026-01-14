import Complexity.TuringMachine
import Mathlib.Computability.Tape

@[simp]
theorem Tape.write_mk'_list {Γ} [Inhabited Γ] (a b : Γ) (L : Turing.ListBlank Γ) (R : List Γ) :
    (Turing.Tape.mk' L (Turing.ListBlank.mk (a :: R))).write b =
      Turing.Tape.mk' L (Turing.ListBlank.mk (b :: R)) := by
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

@[simp]
lemma Tape.default_nth {Γ} [Inhabited Γ] (i : ℤ) :
  (default : Turing.Tape Γ).nth i = default := by
  match i with
  | 0 => rfl
  | (n + 1 : ℕ) => rfl
  | Int.negSucc k => rfl

@[simp]
lemma Tape.mk₁_cons_head {Γ} [Inhabited Γ] (c : Γ) (ws : List Γ) :
  (Turing.Tape.mk₁ (c :: ws)).head = c := by
  rfl

@[simp]
lemma Tape.mk₁_nil_head {Γ} [Inhabited Γ] :
  (Turing.Tape.mk₁ []).head = (default : Γ) := by
  rfl

@[simp]
lemma Tape.write_left_mk₁ {Γ} [Inhabited Γ]
  (c : Γ) (ws : List Γ) :
  Turing.Tape.write c (Turing.Tape.move Turing.Dir.left (Turing.Tape.mk₁ ws)) =
    Turing.Tape.mk₁ (c :: ws) := by
  simp [Turing.Tape.mk₁, Turing.Tape.mk₂]

@[simp]
lemma Tape.mk₁_default {Γ} [Inhabited Γ] :
  (Turing.Tape.mk₁ [(default : Γ)]) = Turing.Tape.mk₁ [] := by rfl

@[simp]
lemma Tape.write_mk₁_nil {Γ} [Inhabited Γ] (c : Γ) :
  Turing.Tape.write c (Turing.Tape.mk₁ []) = Turing.Tape.mk₁ [c] := by rfl

@[simp]
lemma Tape.move_right_append {Γ} [Inhabited Γ] (A B C : List Γ) :
  (Turing.Tape.move .right)^[B.length] (Turing.Tape.mk₂ A (B ++ C)) =
     Turing.Tape.mk₂ (B.reverse ++ A) C := by
  induction B generalizing A with
  | nil => rfl
  | cons b B ih =>
    calc (Turing.Tape.move Turing.Dir.right)^[(b :: B).length] (Turing.Tape.mk₂ A (b :: B ++ C))
        = (Turing.Tape.move Turing.Dir.right)^[B.length] (Turing.Tape.mk₂ (b :: A) (B ++ C)) := by
          simp [Turing.Tape.mk₂]
      _ = Turing.Tape.mk₂ (B.reverse ++ (b :: A)) C := by rw [ih]
      _ = Turing.Tape.mk₂ ((b :: B).reverse ++ A) C := by simp

theorem Tape.left₀_nth {Γ} [Inhabited Γ] (tape : Turing.Tape Γ) (n : ℕ) :
  tape.left₀.nth n = tape.nth (-n) := by
  cases n with
  | zero => simp [Turing.Tape.nth, Turing.Tape.left₀]
  | succ n =>
    simp only [Turing.Tape.nth, Turing.Tape.left₀, Turing.ListBlank.nth_succ,
      Turing.ListBlank.tail_cons]
    rfl

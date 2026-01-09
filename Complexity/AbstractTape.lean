import Mathlib
import Complexity.TuringMachine
import Complexity.TapeLemmas

--- Defines operations on Turing machine tapes involving movements by integer amounts,
--- writing at specific integer positions, lemmas about these operations
--- and an extensionality lemma that states that tapes are equal if their
--- `nth` functions are equal.

def Turing.Tape.move_int {Γ} [Inhabited Γ] (tape : Turing.Tape Γ) (n : ℤ) : Turing.Tape Γ :=
  match n with
  | .ofNat n => (Turing.Tape.move .right)^[n] tape
  | .negSucc n => (Turing.Tape.move .left)^[n + 1] tape

lemma move_int_nonneg {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (n : ℕ) :
  tape.move_int (Int.ofNat n) = (Turing.Tape.move .right)^[n] tape := by
  rfl

lemma move_right_iter_eq_move_int {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (n : ℕ) :
  (Turing.Tape.move .right)^[n] tape = tape.move_int (Int.ofNat n) := by
  rfl

-- lemma move_left_iter_eq_move_int {Γ} [Inhabited Γ]
--   (tape : Turing.Tape Γ) (n : ℕ) :
--   (Turing.Tape.move .left)^[n] tape = tape.move_int (Int.negSucc (n - 1)) := by
--   cases n with
--   | zero => simp; rfl
--   | succ n => rfl

@[simp]
lemma move_int_zero {Γ} [Inhabited Γ] (tape : Turing.Tape Γ) :
  tape.move_int 0 = tape := by
  rfl

@[simp]
lemma move_int_one {Γ} [Inhabited Γ] (tape : Turing.Tape Γ) :
  tape.move_int 1 = tape.move .right := by
  rfl

@[simp]
lemma move_int_neg_one {Γ} [Inhabited Γ] (tape : Turing.Tape Γ) :
  tape.move_int (-1) = tape.move .left := by
  rfl

@[simp]
lemma move_int_nth {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (p n : ℤ) :
  (tape.move_int n).nth p = tape.nth (p + n) := by
  unfold Turing.Tape.move_int
  match n with
  | .ofNat n =>
    dsimp
    induction n generalizing tape with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply, ih, Turing.Tape.move_right_nth]
      simp [Int.add_assoc]
  | .negSucc n =>
    simp only []
    induction n generalizing tape with
    | zero => simp [Int.sub_eq_add_neg]
    | succ n ih =>
      rw [Function.iterate_succ_apply, ih, Turing.Tape.move_left_nth]
      congr 1
      omega

@[simp]
lemma move_int_head {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (n : ℤ) :
  (tape.move_int n).head = tape.nth n := by
  rw [← Turing.Tape.nth_zero, move_int_nth, zero_add]

@[ext]
lemma tape_eq_of_nth {Γ} [Inhabited Γ]
  (tape₁ tape₂ : Turing.Tape Γ)
  (h_nth_equal : ∀ p : ℤ, tape₁.nth p = tape₂.nth p) :
  tape₁ = tape₂ := by
  have h_head : tape₁.head = tape₂.head := by refine h_nth_equal 0
  have h_right : tape₁.right = tape₂.right := by
    ext p
    unfold Turing.Tape.nth at h_nth_equal
    simpa using h_nth_equal ((p + 1) : ℕ)
  have h_left : tape₁.left = tape₂.left := by
    ext p
    unfold Turing.Tape.nth at h_nth_equal
    simpa using h_nth_equal (Int.negSucc p)
  match tape₁, tape₂ with | ⟨h₁, r₁, l₁⟩, ⟨h₂, r₂, l₂⟩ => congr

@[simp]
lemma move_int_move_int {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (m n : ℤ) :
  (tape.move_int m).move_int n = tape.move_int (m + n) := by
  ext p
  simp [move_int_nth]
  congr 1
  omega

def Turing.Tape.write_at {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (pos : ℤ) (symbol : Γ) : Turing.Tape Γ :=
  ((tape.move_int pos).write symbol).move_int (-pos)

lemma write_eq_write_at {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (symbol : Γ) :
  tape.write symbol = tape.write_at 0 symbol := by
  rfl

lemma write_at_move_int {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (pos shift : ℤ) (symbol : Γ) :
  (tape.write_at pos symbol).move_int shift =
    (tape.move_int shift).write_at (pos - shift) symbol := by
  unfold Turing.Tape.write_at
  simp [Int.sub_eq_add_neg, Int.add_comm]

lemma move_int_write_at {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (pos shift : ℤ) (symbol : Γ) :
  (tape.move_int shift).write_at pos symbol =
    (tape.write_at (pos + shift) symbol).move_int shift := by
  unfold Turing.Tape.write_at
  simp [Int.add_comm]

@[simp]
lemma write_at_nth {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (n : ℤ) :
  (tape.write_at n (tape.nth n)) = tape := by
  ext p
  simp only [Turing.Tape.write_at, move_int_nth, Turing.Tape.write_nth,
             neg_add_cancel_right, ite_eq_right_iff]
  intro h_eq
  have : p = n := by omega
  rw [this]

lemma Turing.Tape.write_at_tape_nth {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (p₁ p₂ : ℤ) (symbol : Γ) :
  (tape.write_at p₁ symbol).nth p₂ = if p₁ = p₂ then symbol else tape.nth p₂ := by
  unfold Turing.Tape.write_at
  simp only [move_int_nth, write_nth, neg_add_cancel_right]
  by_cases h : p₁ = p₂ <;> simp only [h, add_neg_cancel, ↓reduceIte, ite_eq_right_iff]; omega

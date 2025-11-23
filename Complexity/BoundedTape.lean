import Mathlib

import Complexity.TuringMachine
import Complexity.TapeLemmas
import Complexity.AbstractTape


--- All tapes are infinite in both directions, but they only ever contain
--- a finite number of non-blank symbols.
--- We define a bounded tape as one which is blank outside a given interval
--- [min, min + length).
--- The important point here is that we have specific bounds on the location
--- of the non-blank symbols.
--- This file concludes with an equivalence between bounded tapes and functions
--- from Fin length to Γ, which allows us to show that the type of bounded tapes
--- is finite when Γ is finite and compute its cardinality.

def bounded_tape {Γ} [Inhabited Γ]
  (t : Turing.Tape Γ) (min : ℤ) (length : ℕ) :=
  ∀ n : ℤ, (n < min ∨ n ≥ min + length) → t.nth n = default

def BoundedTape (Γ) [Inhabited Γ] (min : ℤ) (length : ℕ) :=
  {tape : (Turing.Tape Γ) // bounded_tape tape min length }

instance {Γ} [Inhabited Γ] (min : ℤ) (length : ℕ) :
  Nonempty (BoundedTape Γ min length) :=
  ⟨
    Turing.Tape.mk₁ (Γ := Γ) [],
    by intro n h_outside; simp
  ⟩

lemma bounded_tape_weaken_length {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (min : ℤ) (length₁ length₂ : ℕ)
  (h_bounded : bounded_tape tape min length₁)
  (h_le : length₁ ≤ length₂) :
  bounded_tape tape min length₂ := by
  intro n h_outside
  apply h_bounded n
  omega

lemma bounded_tape_weaken_min {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (min₁ min₂ : ℤ) (length : ℕ)
  (h_bounded : bounded_tape tape min₁ length)
  (h_le : min₂ ≤ min₁) :
  bounded_tape tape min₂ (length + (min₁ - min₂).toNat) := by
  intro n h_outside
  apply h_bounded n
  cases h_outside with
  | inl h => left; omega
  | inr h => right; omega

lemma bounded_tape_shift_bounded {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (min₁ min₂ : ℤ) (length : ℕ)
  (h_bounded : bounded_tape tape min₁ length) :
  bounded_tape (tape.move_int (min₁ - min₂)) min₂ length := by
  intro n h_outside
  rw [move_int_nth]
  apply h_bounded (n + (min₁ - min₂))
  omega

def bounded_tape_shift {Γ} [Inhabited Γ] (length : ℕ) (min₁ min₂ : ℤ)
  (tape : BoundedTape Γ min₁ length) : BoundedTape Γ min₂ length :=
  ⟨
    tape.val.move_int (min₁ - min₂),
    bounded_tape_shift_bounded tape.val min₁ min₂ length tape.property
  ⟩

lemma bounded_tape_shift_inverse {Γ} [Inhabited Γ] (length : ℕ) (min₁ min₂ : ℤ) :
  (bounded_tape_shift length min₁ min₂).LeftInverse
    (bounded_tape_shift (Γ := Γ) length min₂ min₁) := by
  intro ⟨tape, h_bounded⟩
  unfold bounded_tape_shift
  simp

lemma bounded_tape_shift_bijective {Γ} [Inhabited Γ] (length : ℕ) (min₁ min₂ : ℤ) :
  (bounded_tape_shift (Γ := Γ) length min₁ min₂).Bijective := by
  refine Function.bijective_iff_has_inverse.mpr ?_
  exact ⟨
    bounded_tape_shift (Γ := Γ) length min₂ min₁,
    bounded_tape_shift_inverse length min₂ min₁,
    bounded_tape_shift_inverse length min₁ min₂,
  ⟩

@[simp]
lemma bounded_tape_zero_left_default {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (length : ℕ)
  (h_bounded : bounded_tape tape 0 length) (i : ℕ) :
  tape.left.nth i = default := by
  have h' : tape.nth (Int.negSucc i) = default :=
    h_bounded (Int.negSucc i) (Or.inl (Int.negSucc_lt_zero i))
  simpa [Turing.Tape.nth] using h'

def bounded_tape_to_fun (Γ) [Inhabited Γ] (length : ℕ)
  (tape : BoundedTape Γ 0 length) : Fin length → Γ :=
  fun i => tape.val.nth i.val

def fun_to_bounded_tape (Γ) [Inhabited Γ] (length : ℕ)
  (f : Fin length → Γ) : BoundedTape Γ 0 length :=
  let tape := Turing.Tape.mk₁ (List.ofFn f)
  let h_bounded : bounded_tape tape 0 length := by
    unfold tape Turing.Tape.mk₁
    intro n h_outside
    cases h_outside with
    | inl h_lt => simp [h_lt]
    | inr h_ge =>
      have h_ge' : ¬(n.toNat < length) := by omega
      simp [h_ge']
  ⟨tape, h_bounded⟩

lemma left_inverse {Γ} [Inhabited Γ] {length : ℕ} :
  (fun_to_bounded_tape Γ length).LeftInverse (bounded_tape_to_fun Γ length) := by
  intro ⟨tape, h_tape_bounded⟩
  unfold bounded_tape_to_fun fun_to_bounded_tape bounded_tape
  apply Subtype.ext
  ext p
  specialize h_tape_bounded p
  unfold Turing.Tape.mk₁
  simp
  by_cases h : p < 0
  · simp [h, h_tape_bounded]
  · rw [max_eq_left (by linarith)]
    by_cases h' : p.toNat < length
    · simp [h, h']
    · simpa [h, h'] using (h_tape_bounded (by omega)).symm

lemma right_inverse {Γ} [Inhabited Γ] {length : ℕ} :
  (fun_to_bounded_tape Γ length).RightInverse (bounded_tape_to_fun Γ length) := by
  intro f
  unfold bounded_tape_to_fun fun_to_bounded_tape Turing.Tape.mk₁ Turing.Tape.mk₂
  simp only [Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk]
  unfold List.getI List.getD
  simp [List.getElem_ofFn]

lemma bounded_tape_to_fun_bijective (Γ) [Inhabited Γ] (length : ℕ) :
  (bounded_tape_to_fun Γ length).Bijective :=
  Function.bijective_iff_has_inverse.mpr
    ⟨fun_to_bounded_tape Γ length, left_inverse, right_inverse⟩

lemma fun_to_bounded_tape_bijective (Γ) [Inhabited Γ] (length : ℕ) :
  (fun_to_bounded_tape Γ length).Bijective :=
  Function.bijective_iff_has_inverse.mpr
    ⟨bounded_tape_to_fun Γ length, right_inverse, left_inverse⟩

instance {Γ} [Inhabited Γ] [Fintype Γ] (length : ℕ) :
  Fintype (BoundedTape Γ 0 length) :=
  Fintype.ofBijective
    (fun_to_bounded_tape Γ length)
    (fun_to_bounded_tape_bijective Γ length)

lemma fun_to_bounded_tape_shifted_bijective (Γ) [Inhabited Γ] (min : ℤ) (length : ℕ) :
  ((bounded_tape_shift length 0 min) ∘ (fun_to_bounded_tape Γ length)).Bijective := by
  refine Function.Bijective.comp ?_ ?_
  · exact bounded_tape_shift_bijective length 0 min
  · exact fun_to_bounded_tape_bijective Γ length

noncomputable instance {Γ} [Inhabited Γ] [Fintype Γ] (min : ℤ) (length : ℕ) :
  Fintype (BoundedTape Γ min length) :=
  Fintype.ofBijective
    ((bounded_tape_shift length 0 min) ∘ (fun_to_bounded_tape Γ length))
    (fun_to_bounded_tape_shifted_bijective Γ min length)

@[simp]
theorem bounded_tape_card' {Γ} [Inhabited Γ] [Fintype Γ] (length : ℕ) :
  Fintype.card (BoundedTape Γ 0 length) = Fintype.card Γ ^ length := by
  rw [Fintype.card_of_bijective (bounded_tape_to_fun_bijective Γ length)]
  simp

@[simp]
theorem bounded_tape_card {Γ} [Inhabited Γ] [Fintype Γ] (min : ℤ) (length : ℕ) :
  Fintype.card (BoundedTape Γ min length) = Fintype.card Γ ^ length := by
  rw [← Fintype.card_of_bijective (fun_to_bounded_tape_shifted_bijective Γ min length)]
  simp

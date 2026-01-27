import Complexity.TuringMachine
import Complexity.Dyadic
import Complexity.TapeLemmas
import Complexity.AbstractTape
import Complexity.While
import Complexity.Routines
import Complexity.TMComposition

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
  {tape : Turing.Tape Γ} {dir : Turing.Dir} :
  (Routines.move dir).transforms (fun _ => tape) (fun _ => Turing.Tape.move dir tape) := by
  let tm := Routines.move (Γ := Γ) dir
  exact TM.transforms_of_inert tm _ _ (move.inert_after_stop dir) ⟨1, rfl⟩

@[simp]
lemma Routines.move.eval {Γ} [Inhabited Γ] [DecidableEq Γ]
  (tape : Turing.Tape Γ)
  (dir : Turing.Dir) :
  (Routines.move dir).eval (fun _ => tape) =
    .some (fun _ => Turing.Tape.move dir tape) :=
  TM.eval_of_transforms Routines.move.semantics

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
      simpa [this] using Routines.move.semantics
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
      simpa [this] using Routines.move.semantics
    )
    (by simp [h_stop])
  simp at h_while
  simpa [move_until, Turing.Tape.move_int] using h_while

theorem move_until.right_till_separator {Γ} [Inhabited Γ] [DecidableEq Γ]
  (l r₁ r₂ : List Γ)
  (sep : Γ)
  (h_sep : ∀ i, r₁.get i ≠ sep) :
  (move_until .right (fun c => c = sep)).transforms
    (fun _ => Turing.Tape.mk₂ l (r₁ ++ (sep :: r₂)))
    (fun _ => (Turing.Tape.mk₂ l (r₁ ++ (sep :: r₂))).move_int r₁.length) := by
  let tape := Turing.Tape.mk₂ l (r₁ ++ (sep :: r₂))
  have h_stop : ∃ n : ℕ, (fun c => decide (c = sep)) (tape.nth n) := by
    use r₁.length
    simp [tape]
  convert move_until.right_semantics tape (fun c => c = sep) h_stop
  rw [(Nat.find_eq_iff h_stop (m := r₁.length)).mpr]
  constructor
  · simp [tape]
  · intro n h_nlt
    have : tape.nth n = List.get r₁ ⟨n, (by omega)⟩ := by
      simp [tape]
      have : ¬((n : ℤ) < 0) := by omega
      simp [this, List.getElem?_append, h_nlt]
    rw [this]
    simpa using h_sep ⟨n, (by omega)⟩


theorem move_until.left_till_blank {Γ} [Inhabited Γ] [DecidableEq Γ]
  (l : List Γ)
  (n : ℕ)
  (h_nlt : n < l.length)
  (h_non_blank : ∀ i : ℕ, (h_le : i ≤ n) → l[i] ≠ default) :
  (move_until .left (fun c => c = default)).transforms
    (fun _ => (Turing.Tape.move .right)^[n] (Turing.Tape.mk₁ l))
    (fun _ => (Turing.Tape.mk₁ l).move .left) := by
  let tape := Turing.Tape.mk₁ l
  let condition := (fun c : Γ ↦ decide (c = default))
  have h_stop : ∃ i : ℕ, condition (((Turing.Tape.move .right)^[n] tape).nth (-i)) := by
    use n + 1
    simp [condition, move_right_iter_eq_move_int, tape, Turing.Tape.mk₁]
  convert move_until.left_semantics
    ((Turing.Tape.move .right)^[n] (Turing.Tape.mk₁ l))
    (fun c => c = default)
    h_stop
  have h_stop_eq : Nat.find h_stop = n + 1 := by
    apply (Nat.find_eq_iff h_stop (m := n + 1)).mpr
    simp only [tape, move_right_iter_eq_move_int, move_int_nth, Turing.Tape.mk₁, condition]
    constructor
    · simp
    · intro n' h_n'lt
      have h_n'_le_n: n' ≤ n := by omega
      have h_neg_n'_add_n: (-(n': ℤ) + (n : ℤ)).toNat = n - n' := by omega
      have h_n_sub_n'_lt_length : n - n' < l.length := by omega
      simp_all
  rw [h_stop_eq]
  simp [move_right_iter_eq_move_int, Turing.Tape.mk₁, ←move_int_neg_one]

@[simp]
lemma move_until.right_till_separator_list
  {w : List Char} {ws : List (List Char)} :
  (move_until .right (fun c => c = .sep)).eval
    (fun _ => list_to_tape (w :: ws)) =
    .some (fun _ => Turing.Tape.mk₂ w.coe_schar.reverse (.sep :: (list_to_string ws))) := by
  apply TM.eval_of_transforms
  convert move_until.right_till_separator [] w.coe_schar (list_to_string ws) .sep
    (List.coe_schar_get_neq_sep w)
  · simp [list_to_tape, Turing.Tape.mk₁]
  · have h_len: ↑w.length = Int.ofNat w.coe_schar.length := by simp
    rw [List.coe_schar_length]
    simp only [h_len, move_int_nonneg, Tape.move_right_append, List.append_nil]

def Routines.move_to_start :=
  (move_until .left (fun c => c = SChar.blank)).seq (Routines.move .right)

theorem Routines.move_to_start_eval
  {c : SChar} {l r : List SChar}
  (h_c_non_blank : c ≠ .blank)
  (h_l_non_blank : .blank ∉ l) :
  Routines.move_to_start.eval (fun _ => Turing.Tape.mk₂ l (c :: r)) =
    Part.some (fun _ => Turing.Tape.mk₂ [] (l.reverse ++ (c :: r))) := by
  have h_blank_default : default = SChar.blank := rfl
  apply TM.eval_of_transforms
  apply TM.seq.semantics
      (tapes₁ := (fun _ => (Turing.Tape.mk₁ (l.reverse ++ (c :: r))).move .left))
  · convert move_until.left_till_blank
      (l.reverse ++ (c :: r))
      l.length
      (by aesop)
      ?_
    · simp [Turing.Tape.mk₁]
    · intro i h_i
      have : (l.reverse ++ c :: r) = (c :: l).reverse ++ r := by simp
      simp only [this]
      rw [List.getElem_append_left (by grind)]
      rw [h_blank_default]
      by_cases h : i < l.reverse.length
      · simp [List.getElem_append_left h]; grind
      · grind
  · convert Routines.move.semantics (dir := .right) (Γ := SChar)
    simp [Turing.Tape.mk₁]

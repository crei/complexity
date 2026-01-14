import Complexity.TuringMachine
import Complexity.TapeLemmas
import Complexity.Dyadic
import Complexity.Routines
import Complexity.MoveUntil
import Complexity.TMComposition
import Complexity.Dyadic

import Mathlib

def dya (n : ℕ) : List Char :=
  (dyadic_encoding n).map (fun x => if x then '2' else '1')

--- The "core" part of the successor function:
--- If the head is on the separator, increments the dyadic number
--- left of it and stops as soon as it is done, i.e. does not
--- move to the left end of the word.
def successor_core : TM 1 (Fin 2) SChar :=
  let σ := fun state symbols =>
    match state with
    | 0 => match symbols 0 with
      | .sep => (0, fun _ => (.sep, some .left))
      | .blank => (1, fun _ => ('1', none))
      | '1' => (1, fun _ => ('2', none))
      | '2' => (0, fun _ => ('1', some .left))
      | _ => (0, (symbols ·, none))
    | 1 => (1, (symbols ·, none))
  TM.mk σ 0 1

lemma successor_core.inert_after_stop :
  successor_core.inert_after_stop := by
  intro conf h_is_stopped
  ext <;> simp_all [Transition.step, performTapeOps, successor_core]

lemma successor_core.step_start_empty (ws : List SChar) :
  successor_core.transition.step
    ⟨0, fun _ => Turing.Tape.mk₂ [] (.sep :: ws)⟩ =
    ⟨0, fun _ => Turing.Tape.mk₂ [] (.blank :: .sep :: ws)⟩ := by
  simp [successor_core, Transition.step, Turing.Tape.mk₂, default]

lemma successor_core.step_start (c : SChar) (ws₁ ws₂ : List SChar) :
  successor_core.transition.step
    ⟨0, fun _ => Turing.Tape.mk₂ (c :: ws₁) (.sep :: ws₂)⟩ =
    ⟨0, fun _ => Turing.Tape.mk₂ ws₁ (c :: .sep :: ws₂)⟩ := by
  simp [successor_core, Transition.step, Turing.Tape.mk₂]

lemma successor_core.step_odd (n : ℕ) (ws : List SChar) :
  successor_core.transition.step
    ⟨successor_core.startState, fun _ => Turing.Tape.move Turing.Dir.left
      (Turing.Tape.mk₂ (dya (2 * n + 1)).coe_schar.reverse ws)⟩ =
    ⟨successor_core.stopState, fun _ => Turing.Tape.move Turing.Dir.left
      (Turing.Tape.mk₂ (dya (2 * n + 2)).coe_schar.reverse ws)⟩ := by
  simp [successor_core, Transition.step, Turing.Tape.mk₂, dya, dyadic_encoding_prop_one,
        dyadic_encoding_prop_two, performTapeOps, List.coe_schar]

lemma successor_core.step_even (n : ℕ) (ws : List SChar) :
  successor_core.transition.step
    ⟨successor_core.startState, fun _ => .move .left
      (.mk₂ (dya (2 * n + 2)).coe_schar.reverse ws)⟩ =
    ⟨successor_core.startState, fun _ => .move .left (.move .left
      (.mk₂ (dya (2 * n + 1)).coe_schar.reverse ws))⟩ := by
  simp [successor_core, Transition.step, Turing.Tape.mk₂, performTapeOps,
        dya, List.coe_schar, dyadic_encoding_prop_two, dyadic_encoding_prop_one]

lemma dya_odd_tape (n : ℕ) (ws : List SChar) :
  Turing.Tape.move .left (.mk₂ (dya (2 * n + 1)).coe_schar.reverse ws) =
    Turing.Tape.mk₂ (dya n).coe_schar.reverse ('1' :: ws) := by
  simp [dya, dyadic_encoding_prop_one, Turing.Tape.mk₂, Turing.Tape.move_left_mk', List.coe_schar]

lemma dya_odd_iter (n : ℕ) :
    dya (2 * n + 2 + 1) = dya (n + 1) ++ ['1'] := by
  have : 2 * n + 2 + 1 = 2 * (n + 1) + 1 := by ring
  rw [this]
  simp [dya, dyadic_encoding_prop_one]

lemma move_left_mk₂_move_right {Γ} [Inhabited Γ] (A B : List Γ) :
  Turing.Tape.move_int (.mk₂ A.reverse B) (-1) =
     Turing.Tape.move_int (.mk₂ [] (A ++ B)) ((A.length : ℤ) - 1) := by
  calc Turing.Tape.move_int (.mk₂ A.reverse B) (-1)
      = Turing.Tape.move_int ((.move .right)^[A.length] (.mk₂ [] (A ++ B))) (-1) := by
        simp [Tape.move_right_append]
    _ = .move_int (.mk₂ [] (A ++ B)) ((A.length : ℤ) - 1) := by
      rw [move_right_iter_eq_move_int]
      rw [move_int_move_int]
      congr

lemma successor_core.transforms_tape (n : Nat) (ws : List SChar) :
  ∃ shift < (dya n.succ).length, ∃ t, successor_core.configurations
    (fun _ => Turing.Tape.move .left (Turing.Tape.mk₂ (dya n).coe_schar.reverse ws)) t =
    ⟨successor_core.stopState, (fun _ => (Turing.Tape.move .right)^[shift]
         (Turing.Tape.mk₁ ((dya n.succ).coe_schar ++ ws)))⟩  := by
  revert ws
  refine dyadic_induction_on n ?_ ?_ ?_
  · intro ws
    use 0
    constructor
    · simp [dya, dyadic_encoding]
    · use 1
      simp [dya, dyadic_encoding, successor_core, Turing.Tape.mk₂, TM.configurations,
            Transition.step, Turing.Tape.mk₁, performTapeOps, List.coe_schar]
  · intro n ih ws
    use (dya (2 * n + 1).succ).coe_schar.length - 1
    constructor
    · simp [dya, dyadic_encoding_prop_two]
    · use 1
      unfold TM.configurations
      simp only [Function.iterate_one, successor_core.step_odd, Turing.Tape.mk₁]
      rw [move_right_iter_eq_move_int, ← move_int_neg_one, move_left_mk₂_move_right]
      simp [dya, dyadic_encoding_prop_two]
  · intro n ih ws
    obtain ⟨shift, h_shift, t, ih⟩ := ih (( '1' :: ws))
    use shift
    constructor
    · calc shift
          < (dya n.succ).length := h_shift
        _ ≤ (dya (2 * n + 2).succ).length := by simp [dya_odd_iter]
    · use t + 1
      unfold TM.configurations
      simp only [Function.iterate_succ_apply]
      rw [successor_core.step_even, dya_odd_tape, ← TM.configurations, ih]
      have : (dya (2 * n + 2 + 1)).coe_schar ++ ws =
          (dya (n + 1)).coe_schar ++ (↑'1' :: ws) := by simp [dya_odd_iter, List.coe_schar]
      simp [this]


lemma successor_core.semantics (n : Nat) (ws : List SChar) :
  ∃ shift < (dya n.succ).length,
  successor_core.transforms
    (fun _ => Turing.Tape.move .left (Turing.Tape.mk₂ (dya n).coe_schar.reverse ws))
    (fun _ => (Turing.Tape.move .right)^[shift]
         (Turing.Tape.mk₁ ((dya n.succ).coe_schar ++ ws))) := by
  obtain ⟨shift, h_shift, t, h_transforms⟩ := successor_core.transforms_tape n ws
  use shift, h_shift
  exact TM.transforms_of_inert successor_core _ _
    successor_core.inert_after_stop ⟨t, h_transforms⟩

def is_separator : SChar -> Bool
  | .sep => true
  | _ => false

def is_blank : SChar -> Bool
  | .blank => true
  | _ => false

--- Successor Turing machine:
--- 1-tape Turing machine that increments the first word on the first
--- tape interpreted as a dyadic number.
def successor :=
  ((((move_until .right is_separator).seq
  (Routines.move .left)).seq
  successor_core).seq
  (move_until .left is_blank)).seq
  (Routines.move .right)

lemma successor.semantics' (n : Nat) (ws : List SChar) :
  successor.transforms
    (fun _ => Turing.Tape.mk₁ ((dya n).coe_schar ++ (.sep :: ws)))
    (fun _ => Turing.Tape.mk₁ ((dya n.succ).coe_schar ++ (.sep :: ws))) := by
  let tape₀ := fun _ : Fin 1 => Turing.Tape.mk₁ ((dya n).coe_schar ++ (.sep :: ws))
  let tape₁ := fun _ : Fin 1 => Turing.Tape.mk₂ (dya n).coe_schar.reverse (.sep :: ws)
  let tape₂ := fun i : Fin 1 => Turing.Tape.move .left (tape₁ i)
  let tape₃ (shift : ℕ) := fun _ : Fin 1 => (Turing.Tape.move .right)^[shift]
         (Turing.Tape.mk₁ ((dya n.succ).coe_schar ++ (.sep :: ws)))
  let tape₄ := fun _ : Fin 1 => (Turing.Tape.mk₁
                         ((dya n.succ).coe_schar ++ (.sep :: ws))).move .left
  let tape₅ := fun _ : Fin 1 => Turing.Tape.mk₁ ((dya n.succ).coe_schar ++ (.sep :: ws))
  have h_dya_length_nonneg : ¬(((dya n).length : ℤ) < 0) := by simp
  have h_tr₁ : (move_until .right is_separator).transforms tape₀ tape₁ := by
    convert move_until.right_till_separator [] (dya n).coe_schar ws .sep ?_
    · simp [is_separator]; split <;> simp_all
    · rw [←Int.ofNat_eq_natCast, ←move_right_iter_eq_move_int, Tape.move_right_append]
      simp [tape₁]
    · exact List.coe_schar_get_neq_sep _
  have h_tr₂ : (Routines.move .left).transforms tape₁ tape₂ := by
    exact Routines.move.semantics (tape₁ 0) .left
  have h_tr₃ : ∃ shift < (dya n.succ).length, successor_core.transforms tape₂ (tape₃ shift) := by
    exact successor_core.semantics n (.sep :: ws)
  have h_tr₄ : ∀ shift < (dya n.succ).length, (move_until .left is_blank).transforms
      (tape₃ shift) tape₄ := by
    intro shift h_shift
    convert move_until.left_till_blank ((dya n.succ).coe_schar ++ (.sep :: ws)) shift ?_ ?_
    · simp [is_blank, default]; split <;> simp_all
    · simp only [List.length_append, List.coe_schar_length, List.length_cons]; omega
    · intro i h_ilt
      have h_coe_i_lt : (i : ℕ) < (dya n.succ).length := by omega
      have : ((dya n.succ).coe_schar ++ SChar.sep :: ws).get ⟨(i : ℕ), by omega⟩ =
          (dya n.succ).get ⟨(i : ℕ), (by omega)⟩ := by simp [List.coe_schar, h_coe_i_lt]
      rw [this]
      simp
  have h_tr₅ : (Routines.move .right).transforms tape₄ tape₅ := by
    simpa [tape₅, tape₄] using Routines.move.semantics (tape₄ 0) .right
  unfold successor
  obtain ⟨shift, h_shift, h_tr₃⟩ := h_tr₃
  let h₁ := TM.seq.semantics h_tr₁ h_tr₂
  let h₂ := TM.seq.semantics h₁ h_tr₃
  let h₃ := TM.seq.semantics h₂ (h_tr₄ shift h_shift)
  exact TM.seq.semantics h₃ h_tr₅


-- theorem successor.semantics (n : Nat) (ws : List (List Char)) :
--   successor.transforms_list
--     (fun _ => (dya n) :: ws)
--     (fun _ => (dya n.succ) :: ws) := by
--   let tape₀ := list_to_tape ((dya n) :: ws)
--   let tape₁ := Turing.Tape.mk₁
--   have h1 (ws : List SChar) : (move_until .right is_separator).transforms
--     (fun _ => Turing.Tape.mk₁ ((dya n).coe_schar ++ (.sep :: ws)))
--     (fun _ => Turing.Tape.move_int
--       (Turing.Tape.mk₁ ((dya n).coe_schar ++ ['sep'] ++ ws.concat)) (dya n).length) := by
--     apply move_until.right_semantics
--     · simp [is_separator, dya]
--     · use (dya n).length
--       simp [dya]
--   let tm := successor



--   sorry

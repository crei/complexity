import Complexity.TuringMachine
import Complexity.Dyadic
import Complexity.TapeLemmas
import Complexity.AbstractTape
import Complexity.While
import Complexity.Routines
import Complexity.WithTapes
import Complexity.TMComposition
import Complexity.MoveUntil

import Mathlib

--- Core of the equality routine: The head of the third tape is on an
--- empty cell, left of a separator cell. The two first heads check equality.
--- If the two heads both read separators, the third head writes "1".
--- If they read two other equal symbols, both move right, and we continue.
--- If they read two different symbols, the third head moves right.
def eq_core : TM 3 (Fin 2) SChar :=
  let σ := fun state symbols =>
    match state, (symbols 0), (symbols 1) with
    | 0, .sep, .sep => (1, [(SChar.sep, none), (.sep, .none), ('1', .none)].get)
    | 0, a, b => if a = b then
          (0, [(a, .some .right), (a, .some .right), (.blank, none)].get)
        else
          (1, [(a, .none), (b, .none), (.blank, .some .right)].get)
    | 1, _, _ => (1, (symbols ·, none))
  TM.mk σ 0 1

lemma eq_core.is_inert_after_stop : eq_core.inert_after_stop := by
  intro conf h_is_stopped
  ext <;> simp_all [Transition.step, performTapeOps, eq_core]

lemma eq_core_step_separators (l₁ l₂ r₁ r₂ r₃ : List SChar) :
  eq_core.transition.step
    ⟨eq_core.startState, [.mk₂ l₁ (.sep :: r₁), .mk₂ l₂ (.sep :: r₂), .mk₂ [] (.blank :: r₃)].get⟩ =
    ⟨eq_core.stopState, [.mk₂ l₁ (.sep :: r₁), .mk₂ l₂ (.sep :: r₂), .mk₂ [] ('1' :: r₃)].get⟩ := by
  ext1
  · simp [eq_core, Transition.step, Turing.Tape.mk₂, performTapeOps]
  · dsimp
    funext i
    match i with
    | 0 | 1 | 2 => simp [eq_core, Transition.step, Turing.Tape.mk₂, performTapeOps]

lemma eq_core_step_equal (a : SChar) (h_neq : a ≠ .sep) (l₁ l₂ r₁ r₂ r₃ : List SChar) :
  eq_core.transition.step
    ⟨eq_core.startState, [.mk₂ l₁ (a :: r₁), .mk₂ l₂ (a :: r₂), .mk₂ [] (.blank :: r₃)].get⟩ =
    ⟨eq_core.startState, [.mk₂ (a :: l₁) r₁, .mk₂ (a :: l₂) r₂, .mk₂ [] (.blank :: r₃)].get⟩ := by
  ext1
  · simp [h_neq, eq_core, Transition.step, Turing.Tape.mk₂, performTapeOps]
  · dsimp
    funext i
    match i with
    | 0 | 1 | 2 =>
      simp [h_neq, eq_core, Transition.step, Turing.Tape.mk₂, performTapeOps]

lemma eq_core_step_non_equal
  (a b : SChar) (h_neq₁ : a ≠ b) (h_neq₂ : a ≠ .sep) (h_neq₃ : b ≠ .sep)
  (l₁ l₂ r₁ r₂ r₃ : List SChar) :
  eq_core.transition.step
    ⟨eq_core.startState, [.mk₂ l₁ (a :: r₁), .mk₂ l₂ (b :: r₂), .mk₂ [] (.blank :: r₃)].get⟩ =
    ⟨eq_core.stopState, [.mk₂ l₁ (a :: r₁), .mk₂ l₂ (b :: r₂), .mk₂ [] r₃].get⟩ := by
  have h_blank_default : SChar.blank = default := rfl
  ext1
  · simp [h_neq₁, h_neq₂, h_neq₃, eq_core, Transition.step, Turing.Tape.mk₂, performTapeOps]
  · dsimp
    funext i
    match i with
    | 0 | 1 | 2 =>
      simp [h_blank_default, h_neq₁, h_neq₂, h_neq₃, eq_core,
            Transition.step, Turing.Tape.mk₂, performTapeOps]

lemma eq_core_steps_equal
  (l r r₁ r₂ r₃ : List SChar) (h_r_non_sep : .sep ∉ r) :
  eq_core.transition.step^[r.length]
    ⟨eq_core.startState, [.mk₂ l (r ++ r₁), .mk₂ l (r ++ r₂), .mk₂ [] (.blank :: r₃)].get⟩ =
    ⟨eq_core.startState, [
      .mk₂ (r.reverse ++ l) r₁,
      .mk₂ (r.reverse ++ l) r₂,
      .mk₂ [] (.blank :: r₃)].get⟩ := by
  induction r generalizing l with
  | nil => rfl
  | cons c r ih =>
    simp only [List.length_cons, List.cons_append, Function.iterate_succ, Function.comp_apply]
    rw [eq_core_step_equal c (by aesop) l l (r ++ r₁) (r ++ r₂) r₃]
    rw [ih (c :: l) (by aesop)]
    simp only [Configuration.mk.injEq, true_and]
    funext
    simp

lemma eq_core_eval_different
  (a b : SChar) (h_neq₁ : a ≠ b) (h_neq₂ : a ≠ .sep) (h_neq₃ : b ≠ .sep)
  (l r r₁ r₂ r₃ : List SChar) (h_r_non_sep : .sep ∉ r) :
  eq_core.eval [.mk₂ l (r ++ (a :: r₁)), .mk₂ l (r ++ (b :: r₂)), .mk₂ [] (.blank :: r₃)].get =
    Part.some [
      .mk₂ (r.reverse ++ l) (a :: r₁),
      .mk₂ (r.reverse ++ l) (b :: r₂),
      .mk₂ [] r₃].get := by
  have h_start_state : eq_core.startState = 0 := rfl
  apply TM.eval_of_transforms
  apply TM.transforms_of_inert _ _ _ eq_core.is_inert_after_stop
  use r.length.succ
  simp only [TM.configurations, Function.iterate_succ_apply']
  rw [eq_core_steps_equal l r (a :: r₁) (b :: r₂) r₃ h_r_non_sep]
  rw [eq_core_step_non_equal a b h_neq₁ h_neq₂ h_neq₃ (r.reverse ++ l) (r.reverse ++ l) r₁ r₂ r₃]

lemma eq_core_eval_same
  (l r r₁ r₂ r₃ : List SChar) (h_r_non_sep : .sep ∉ r) :
  eq_core.eval [.mk₂ l (r ++ .sep :: r₁), .mk₂ l (r ++ .sep :: r₂), .mk₂ [] (.blank :: r₃)].get =
    Part.some [
      .mk₂ (r.reverse ++ l) (.sep :: r₁),
      .mk₂ (r.reverse ++ l) (.sep :: r₂),
      .mk₂ [] ('1' :: r₃)].get := by
  have h_start_state : eq_core.startState = 0 := rfl
  apply TM.eval_of_transforms
  apply TM.transforms_of_inert _ _ _ eq_core.is_inert_after_stop
  use r.length.succ
  simp only [TM.configurations, Function.iterate_succ_apply']
  rw [eq_core_steps_equal l r (.sep :: r₁) (.sep :: r₂) r₃ h_r_non_sep]
  rw [eq_core_step_separators (r.reverse ++ l) (r.reverse ++ l) r₁ r₂ r₃]

--- A 3-tape Turing machine that pushes the new word "1"
--- to the third tape if the first words on the first tape are the same
--- and otherwise pushes the empty word to the third tape.

-- push empty word on the third tape
-- move left on the third tape
-- run core
-- run "move_to_start" on first tape
-- run "move_to_start" on second tape
def Routines.eq :=
  (((((cons_empty.seq (Routines.move .left)).with_tapes #v[2]) : TM 3 _ _).seq
    eq_core).seq
  (Routines.move_to_start.with_tapes #v[0])).seq
  (Routines.move_to_start.with_tapes #v[1])

@[simp]
theorem Routines.eq_eval (w₁ w₂ : List Char) (ws₁ ws₂ ws₃ : List (List Char)) :
  Routines.eq.eval (list_to_tape ∘ [w₁ :: ws₁, w₂ :: ws₂, ws₃].get) =
    Part.some (if h: w₁ = w₂ then
      list_to_tape ∘ [w₁ :: ws₁, w₂ :: ws₂, ['1'] :: ws₃].get
    else
      list_to_tape ∘ [w₁ :: ws₁, w₂ :: ws₂, [] :: ws₃].get) := by
  have h_blank_is_default: SChar.blank = default := rfl
  have h_part1 : (((cons_empty.seq (Routines.move .left)).with_tapes #v[2]) : TM 3 _ _).eval
      (list_to_tape ∘ [w₁ :: ws₁, w₂ :: ws₂, ws₃].get) =
      Part.some ([
        list_to_tape (w₁ :: ws₁),
        list_to_tape (w₂ :: ws₂),
        .mk₂ [] (.blank :: list_to_string ([] :: ws₃))].get) := by
    -- TODO create a therem that moves the `.get i` into the `Part.some`?
    simp only [Fin.isValue, TM.with_tapes.eval_1, Nat.succ_eq_add_one, Nat.reduceAdd,
      Function.comp_apply, List.get_eq_getElem, List.length_cons, List.length_nil,
      Fin.coe_ofNat_eq_mod, Nat.mod_succ, List.getElem_cons_succ, List.getElem_cons_zero,
      TM.seq.eval, cons_empty_eval, Part.bind_some, move.eval, Part.map_some, Part.some_inj]
    funext i
    match i with
    | 0 | 1 | 2 =>
      simp [Turing.Tape.mk₁, h_blank_is_default, list_to_tape, Turing.Tape.mk₂]

  by_cases h : w₁ = w₂
  · simp [h]; sorry
  · simp [h]; sorry

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
  (a b : SChar) (h_neq₁ : a ≠ b) (l₁ l₂ r₁ r₂ r₃ : List SChar) :
  eq_core.transition.step
    ⟨eq_core.startState, [.mk₂ l₁ (a :: r₁), .mk₂ l₂ (b :: r₂), .mk₂ [] (.blank :: r₃)].get⟩ =
    ⟨eq_core.stopState, [.mk₂ l₁ (a :: r₁), .mk₂ l₂ (b :: r₂), .mk₂ [] r₃].get⟩ := by
  have h_blank_default : SChar.blank = default := rfl
  have h_neq_seq : ¬(a = .sep ∧ b = .sep) := by grind
  ext1
  · simp_all [eq_core, Transition.step, Turing.Tape.mk₂, performTapeOps]
  · dsimp
    funext i
    match i with
    | 0 | 1 | 2 =>
      simp_all [eq_core, Transition.step, Turing.Tape.mk₂, performTapeOps]

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

lemma eq_core_eval_same_words (w : List Char) (ws₁ ws₂ ws₃ : List (List Char)) :
  eq_core.eval [
      list_to_tape (w :: ws₁),
      list_to_tape (w :: ws₂),
      .mk₂ [] (.blank :: list_to_string ([] :: ws₃))].get =
    Part.some [
      .mk₂ (w.coe_schar.reverse) (.sep :: list_to_string ws₁),
      .mk₂ (w.coe_schar.reverse) (.sep :: list_to_string ws₂),
      list_to_tape (['1'] :: ws₃)
    ].get := by
  rw [list_to_tape_cons, list_to_tape_cons, Turing.Tape.mk₁, Turing.Tape.mk₁]
  rw [eq_core_eval_same [] w.coe_schar
    (list_to_string ws₁)
    (list_to_string ws₂)
    (list_to_string ([] :: ws₃))
    (by exact List.not_sep_getElem_coe_schar)]
  simp only [Part.some_inj]
  rw [List.append_nil, list_to_tape]
  rw [Turing.Tape.mk₁]
  have : list_to_string (['1'] :: ws₃) = .ofChar '1' :: list_to_string ([] :: ws₃) := by
    simp [list_to_string, List.coe_schar]
  rw [this]

lemma eq_core_eval_different
  (a b : SChar) (h_neq₁ : a ≠ b)
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
  rw [eq_core_step_non_equal a b h_neq₁ (r.reverse ++ l) (r.reverse ++ l) r₁ r₂ r₃]

-- Helper: Find where two different Char lists first differ when encoded as SChar
-- This gives us the common prefix and first differing characters
lemma List.coe_schar_differ_at (w₁ w₂ : List Char) (h_neq : w₁ ≠ w₂) :
  ∃ (common rest1 rest2 : List SChar), ∃ (a b : SChar),
    (∀ c ∈ common, c ≠ .sep) ∧
    (a ≠ b) ∧
    w₁.coe_schar ++ [SChar.sep] = common ++ a :: rest1 ∧
    w₂.coe_schar ++ [SChar.sep] = common ++ b :: rest2 := by
  wlog h_length: w₁.length ≤ w₂.length
  · -- Symmetric case: if w₂.length ≤ w₁.length, swap them
    have h_w2_le : w₂.length ≤ w₁.length := Nat.le_of_not_le h_length
    obtain ⟨common, rest2, rest1, b, a, h_no_sep, h_ba_neq, h_w2, h_w1⟩ :=
      this w₂ w₁ (Ne.symm h_neq) h_w2_le
    use common, rest1, rest2, a, b
    exact ⟨h_no_sep, Ne.symm h_ba_neq, h_w1, h_w2⟩
  induction w₁ generalizing w₂ with
  | nil =>
    cases w₂ with
    | nil => simp at h_neq
    | cons c w₂' =>
      use [], [], w₂'.coe_schar ++ [.sep], .sep, .ofChar c
      simp [List.coe_schar]
  | cons c w₁ ih =>
    cases w₂ with
    | nil =>
      -- contradiction with h_length: (c :: w₁).length ≤ [].length is false
      simp at h_length
    | cons d w₂' =>
      by_cases h_char_eq : c = d
      · -- Characters equal, use induction on tails
        subst h_char_eq
        obtain ⟨common, rest1, rest2, a, b, h_no_sep, h_ab_neq, h_w1', h_w2'⟩ :=
          ih w₂' (by simpa using h_neq) (by simp at h_length; omega)
        use .ofChar c :: common, rest1, rest2, a, b
        simp only [List.coe_schar, List.map_cons, List.cons_append]
        constructor
        · -- Show ∀ x ∈ .ofChar c :: common, x ≠ .sep
          intro x h_mem
          cases h_mem with
          | head => simp
          | tail _ h => exact h_no_sep x h
        · constructor
          · exact h_ab_neq
          · constructor
            · simpa [List.coe_schar] using h_w1'
            · simpa [List.coe_schar] using h_w2'
      · -- Characters differ: common is empty
        use [], w₁.coe_schar ++ [.sep], w₂'.coe_schar ++ [.sep], .ofChar c, .ofChar d
        simp [List.coe_schar, h_char_eq]

lemma eq_core_eval_different_words (w₁ w₂ : List Char) (ws₁ ws₂ ws₃ : List (List Char))
    (h_neq : w₁ ≠ w₂) :
  ∃ n ≤ min w₁.length w₂.length,
  eq_core.eval [
      list_to_tape (w₁ :: ws₁),
      list_to_tape (w₂ :: ws₂),
      .mk₂ [] (.blank :: list_to_string ([] :: ws₃))].get =
    Part.some [
      (.move .right)^[n] (list_to_tape (w₁ :: ws₁)),
      (.move .right)^[n] (list_to_tape (w₂ :: ws₂)),
      list_to_tape ([] :: ws₃)
    ].get := by
  -- Convert to tape representation
  rw [list_to_tape_cons, list_to_tape_cons, Turing.Tape.mk₁, Turing.Tape.mk₁]
  -- Get the decomposition of where the words differ
  obtain ⟨common, rest1, rest2, a, b, h_common_no_sep, h_ab_neq, h_w1, h_w2⟩ :=
    List.coe_schar_differ_at w₁ w₂ h_neq
  -- Use the length of the common prefix
  use common.length
  constructor
  · have h1 : common.length ≤ w₁.length := by
      have : (w₁.coe_schar ++ [SChar.sep]).length = (common ++ a :: rest1).length :=
        congrArg List.length h_w1
      simp at this
      have : w₁.coe_schar.length = w₁.length := List.coe_schar_length w₁
      omega
    have h2 : common.length ≤ w₂.length := by
      have : (w₂.coe_schar ++ [SChar.sep]).length = (common ++ b :: rest2).length :=
        congrArg List.length h_w2
      simp at this
      have : w₂.coe_schar.length = w₂.length := List.coe_schar_length w₂
      omega
    omega
  -- Now we need to show the evaluation gives the correct result
  -- Rewrite using the decompositions
  have h_w1_eq : w₁.coe_schar ++ SChar.sep :: list_to_string ws₁ =
                  common ++ a :: (rest1 ++ list_to_string ws₁) := by
    calc w₁.coe_schar ++ SChar.sep :: list_to_string ws₁
        = w₁.coe_schar ++ [SChar.sep] ++ list_to_string ws₁ := by simp
      _ = common ++ a :: (rest1 ++ list_to_string ws₁) := by simp [h_w1]
  have h_w2_eq : w₂.coe_schar ++ SChar.sep :: list_to_string ws₂ =
                  common ++ b :: (rest2 ++ list_to_string ws₂) := by
    calc w₂.coe_schar ++ SChar.sep :: list_to_string ws₂
        = w₂.coe_schar ++ [SChar.sep] ++ list_to_string ws₂ := by simp
      _ = common ++ b :: (rest2 ++ list_to_string ws₂) := by simp [h_w2]
  rw [h_w1_eq, h_w2_eq]
  rw [Tape.move_right_append, Tape.move_right_append]
  have h_common_no_sep' : .sep ∉ common := by
    intro h_mem
    exact h_common_no_sep .sep h_mem rfl
  convert eq_core_eval_different a b h_ab_neq
    [] common
    (rest1 ++ list_to_string ws₁)
    (rest2 ++ list_to_string ws₂)
    (list_to_string ([] :: ws₃))
    h_common_no_sep' using 2


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
    apply TM.eval_tapes_ext
    intro i
    match i with
    | 0 | 1 | 2 =>
      simp only [TM.with_tapes.eval_1, Function.comp_apply, TM.seq.eval, cons_empty_eval]
      simp [Turing.Tape.mk₁, h_blank_is_default, list_to_tape, Turing.Tape.mk₂]

  by_cases h : w₁ = w₂
  · subst h
    have h_part2 := eq_core_eval_same_words w₁ ws₁ ws₂ ws₃
    apply TM.eval_tapes_ext
    intro i
    match i with | 0 | 1 | 2 => simp [eq, h_part1, h_part2]; sorry
  · have h_part2 := eq_core_eval_different_words w₁ w₂ ws₁ ws₂ ws₃ h
    simp [h]; sorry

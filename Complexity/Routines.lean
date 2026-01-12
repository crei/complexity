import Mathlib

import Complexity.TuringMachine
import Complexity.TapeLemmas

--- Routines are Turing Machines that can be composed to build more complex
--- algorithms. They fulfill the following invariants:
--- At the start and at the end of each routine, all tapes contain words
--- suffixed (separated) by special separation symbols.
--- The words themselves do not contain the blank symbol.
--- All tape heads are at the leftmost non-blank symbol (or at an arbitrary
--- position if the tape is empty).
--- The tapes are interpreted as a stack of words that grows to the left.
--- Each routine operates on a certain set of tapes and adds, modifies or
--- removes words from the top of the stack. The tape heads only move within
--- the changed words (or at most to the separator or blank delimiting them).
--- A routine can use auxiliary tapes but they need to be restored to their
--- initial contents before halting.

section Routines

--- A character type that allows a distinct separator and blank symbol.
inductive SChar where
  | blank
  | ofChar (c : Char)
  | sep
  deriving DecidableEq

instance : Inhabited SChar where
  default := SChar.blank

instance : Coe Char SChar where
  coe c := .ofChar c

--- Character-by-character coercion from List Char to List SChar.
--- If we use the built-in coercion, Lean uses filter_map instead of map.
def List.coe_schar (x : List Char) : List SChar :=
  x.map (fun c => SChar.ofChar c)

@[simp]
lemma List.coe_schar_length (x : List Char) :
  x.coe_schar.length = x.length := by simp [List.coe_schar]

lemma List.coe_schar_get_neq_sep (x : List Char) (n : Fin x.coe_schar.length) :
  x.coe_schar.get n ≠ .sep := by
  simp [List.coe_schar]

def list_to_string (ls : List (List Char)) : List SChar :=
  (ls.map (fun w : List Char => w.coe_schar ++ [SChar.sep])).flatten

lemma list_to_string_empty :
  list_to_string [] = [] := by
  rfl

lemma list_to_string_cons (w : List Char) (ws : List (List Char)) :
  list_to_string (w :: ws) = (w.coe_schar : List SChar) ++ (SChar.sep :: list_to_string ws) := by
  simp [list_to_string]

lemma list_to_string_nonempty {w : List Char} {ws : List (List Char)} :
  list_to_string (w :: ws) ≠ [] := by
  simp [list_to_string]

@[simp]
lemma list_to_string_nil_cons_head (ws : List (List Char)) :
  (list_to_string ([] :: ws)).head list_to_string_nonempty = SChar.sep := by
  simp [list_to_string, List.coe_schar]

@[simp]
lemma list_to_string_nil_cons_tail (ws : List (List Char)) :
  (list_to_string ([] :: ws)).tail = list_to_string ws := by
  simp [list_to_string, List.coe_schar]

@[simp]
lemma list_to_string_head_nonempty
  (c : Char)
  (w : List Char)
  (ws : List (List Char)) :
  (list_to_string ((c :: w) :: ws)).head list_to_string_nonempty = ↑c := by
  simp [list_to_string, List.coe_schar]

@[simp]
lemma list_to_string_headI_nonempty
  (c : Char)
  (w : List Char)
  (ws : List (List Char)) :
  (list_to_string ((c :: w) :: ws)).headI = ↑c := by
  simp [list_to_string, List.coe_schar]

@[simp]
lemma list_to_string_tail_nonempty
  (c : Char)
  (w : List Char)
  (ws : List (List Char)) :
  (list_to_string ((c :: w) :: ws)).tail = (list_to_string (w :: ws)) := by
  simp [list_to_string, List.coe_schar]

def list_to_tape (ls : List (List Char)) : Turing.Tape SChar :=
  Turing.Tape.mk₁ (list_to_string ls)

lemma list_to_tape_nil :
  list_to_tape [] = Turing.Tape.mk₁ [] := by
  rfl

lemma list_to_tape_cons (w : List Char) (ws : List (List Char)) :
  list_to_tape (w :: ws) =
    Turing.Tape.mk₁ ((w.coe_schar) ++ (SChar.sep :: list_to_string ws)) := by
  simp [list_to_tape, list_to_string, List.coe_schar]

@[simp]
lemma list_to_tape_nil_head :
  (list_to_tape []).head = SChar.blank := by
  rfl

@[simp]
lemma list_to_tape_nil_cons_head (l : List (List Char)) :
  (list_to_tape ([] :: l)).head = SChar.sep := by rfl

@[simp]
lemma list_to_tape_head_nonempty
  (c : Char)
  (w : List Char)
  (l : List (List Char)) :
  (list_to_tape ((c :: w) :: l)).head = c := by
  simp [list_to_tape_cons, Turing.Tape.mk₁, Turing.Tape.mk₂]
  rfl

def lists_to_configuration {k : ℕ} {Q : Type*} (lists : Fin k → List (List Char)) (state : Q) :
  Configuration k Q SChar :=
  {
    state := state,
    tapes := fun i => list_to_tape (lists i)
  }

def TM.transforms_list {k : ℕ} {Q : Type*}
  (tm : TM k Q SChar)
  (initial : Fin k → (List (List Char)))
  (final : Fin k → (List (List Char))) : Prop :=
  let configs := fun t => tm.transition.step^[t] (lists_to_configuration initial tm.startState)
  ∃ t, configs t = lists_to_configuration final tm.stopState ∧
    ∀ t' < t, (configs t').state ≠ tm.stopState

lemma transforms_of_inert {k : ℕ} {Q : Type*}
  (tm : TM k Q SChar)
  (initial : Fin k → (List (List Char)))
  (final : Fin k → (List (List Char)))
  (h_inert_after_stop : tm.inert_after_stop)
  (h_stops_with_final : ∃ t, tm.configurations (list_to_tape ∘ initial) t =
    lists_to_configuration final tm.stopState) :
  tm.transforms_list initial final :=
  TM.transforms_of_inert tm (list_to_tape ∘ initial) (list_to_tape ∘ final)
    h_inert_after_stop h_stops_with_final

--- Prepend a new empty word to the first tape.
def cons_empty :
  TM 1 (Fin 3) SChar :=
  let σ := fun state symbols =>
    match state, (symbols 0) with
    | 0, .blank => (1, (symbols ·, none))
    | 0, _ => (1, (symbols ·, some .left))
    | 1, _ => (2, fun _ => (.sep, none))
    | _, _ => (state, (symbols ·, none))
  TM.mk σ 0 2

lemma cons_empty_inert_after_stop
  (conf : Configuration 1 (Fin 3) SChar)
  (h_is_stopped : conf.state = 2) :
  cons_empty.transition.step conf = conf := by
  unfold Transition.step cons_empty
  ext <;> simp_all

lemma cons_empty_two_steps (ws : List (List Char)) :
  cons_empty.transition.step^[2] (lists_to_configuration (fun _ => ws) 0) =
    lists_to_configuration (fun _ => [] :: ws) 2 := by
  cases ws with
  | nil => simp [lists_to_configuration, list_to_tape_nil, list_to_tape_cons, cons_empty,
                Transition.step, list_to_string, List.coe_schar]
  | cons w ws =>
    cases w <;> simp [lists_to_configuration, list_to_tape_cons, cons_empty,
                      Transition.step, list_to_string_cons, List.coe_schar]

theorem cons_empty_semantics (ws : List (List Char)) :
  cons_empty.transforms_list (fun _ => ws) (fun _ => [] :: ws) := by
  exact transforms_of_inert cons_empty _ _
    cons_empty_inert_after_stop
    ⟨2, cons_empty_two_steps ws⟩

--- Prepend a character to the first word of the first tape.
def cons_char (c : Char) :
  TM 1 (Fin 3) SChar :=
  let σ := fun state symbols =>
    match state, (symbols 0) with
    | 0, _ => (1, (symbols ·, some .left))
    | 1, _ => (2, fun _ => (↑c, none))
    | _, _ => (state, (symbols ·, none))
  TM.mk σ 0 2

lemma cons_char_inert_after_stop
  (c : Char)
  (conf : Configuration 1 (Fin 3) SChar)
  (h_is_stopped : conf.state = 2) :
  (cons_char c).transition.step conf = conf := by
  unfold Transition.step cons_char
  ext <;> simp_all

lemma cons_char_two_steps (c : Char) (w : List Char) (ws : List (List Char)) :
  (cons_char c).transition.step^[2] (lists_to_configuration (fun _ => w :: ws) 0) =
    lists_to_configuration (fun _ => (c :: w) :: ws) 2 := by
  cases w <;> simp [lists_to_configuration, list_to_tape_cons, cons_char, Transition.step] <;> rfl

theorem cons_char_semantics (c : Char) (w : List Char) (ws : List (List Char)) :
  (cons_char c).transforms_list (fun _ => w :: ws) (fun _ => ((c :: w) :: ws)) := by
  exact transforms_of_inert (cons_char c) _ _
    (cons_char_inert_after_stop c)
    ⟨2, cons_char_two_steps c w ws⟩


end Routines

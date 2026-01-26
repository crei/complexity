import Complexity.TuringMachine
import Complexity.Dyadic
import Complexity.TapeLemmas
import Complexity.AbstractTape
import Complexity.While
import Complexity.Routines

import Mathlib

-- state 0:
-- if both separator, move to state 2
-- as long as equal, move both right and keep in state 0
-- if different, move to state 3
-- if

--- A 3-tape Turing machine that pushes the new word "1"
--- to the third tape if the first words on the first tape are the same
--- and otherwise pushes the empty word to the third tape.

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
  eq_core.transforms
    [.mk₂ l₁ (.sep :: r₁), .mk₂ l₂ (.sep :: r₂), .mk₁ (.blank :: r₃)].get
    [.mk₂ l₁ (.sep :: r₁), .mk₂ l₂ (.sep :: r₂), .mk₁ ('1' :: r₃)].get := by
  apply TM.transforms_of_inert eq_core _ _ eq_core.is_inert_after_stop ?_
  use 1
  ext1
  · simp [eq_core, TM.configurations, Transition.step, Turing.Tape.mk₁,
          Turing.Tape.mk₂, performTapeOps]
  · dsimp
    funext i
    match i with
    | 0 | 1 | 2 => simp [eq_core, TM.configurations, Transition.step, Turing.Tape.mk₁,
                         Turing.Tape.mk₂, performTapeOps]

lemma eq_core_step_equal (a : SChar) (h_neq : a ≠ .sep) (l₁ l₂ r₁ r₂ r₃ : List SChar) :
  eq_core.transition.step
    ⟨0, [.mk₂ l₁ (a :: r₁), .mk₂ l₂ (a :: r₂), .mk₁ (.blank :: r₃)].get⟩ =
    ⟨0, [.mk₂ (a :: l₁) r₁, .mk₂ (a :: l₂) r₂, .mk₁ (.blank :: r₃)].get⟩ := by
  ext1
  · simp [h_neq, eq_core, Transition.step, Turing.Tape.mk₁, Turing.Tape.mk₂, performTapeOps]
  · dsimp
    funext i
    match i with
    | 0 | 1 | 2 =>
      simp [h_neq, eq_core, Transition.step, Turing.Tape.mk₁, Turing.Tape.mk₂, performTapeOps]

lemma eq_core_step_non_equal
  (a b : SChar) (h_neq₁ : a ≠ b) (h_neq₂ : a ≠ .sep) (h_neq₃ : b ≠ .sep)
  (l₁ l₂ r₁ r₂ r₃ : List SChar) :
  eq_core.transition.step
    ⟨0, [.mk₂ l₁ (a :: r₁), .mk₂ l₂ (b :: r₂), .mk₁ (.blank :: r₃)].get⟩ =
    ⟨1, [.mk₂ l₁ (a :: r₁), .mk₂ l₂ (b :: r₂), .mk₁ r₃].get⟩ := by
  have h_blank_default : SChar.blank = default := rfl
  ext1
  · simp [h_neq₁, h_neq₂, h_neq₃, eq_core, Transition.step, Turing.Tape.mk₁,
          Turing.Tape.mk₂, performTapeOps]
  · dsimp
    funext i
    match i with
    | 0 | 1 | 2 =>
      simp [h_blank_default, h_neq₁, h_neq₂, h_neq₃, eq_core,
            Transition.step, Turing.Tape.mk₁, Turing.Tape.mk₂, performTapeOps]


-- def Routines.eq_core : TM 3 (Fin 2) SChar :=
--   let σ := fun state symbols =>
--     match state, (symbols 0), (symbols 1) with
--     | 0, .sep, .sep => (1, (symbols ·, some dir))
--     | 1, a, b => (1, (symbols ·, none))
--   TM.mk σ 0 1

-- lemma Routines.move.inert_after_stop {Γ} [Inhabited Γ]
--   (dir : Turing.Dir) :
--   (Routines.move (Γ := Γ) dir).inert_after_stop := by
--   intro conf h_is_stopped
--   ext <;> simp_all [Transition.step, performTapeOps, Routines.move]

-- lemma Routines.move.semantics {Γ} [Inhabited Γ] [DecidableEq Γ]
--   {tape : Turing.Tape Γ} {dir : Turing.Dir} :
--   (Routines.move dir).transforms (fun _ => tape) (fun _ => Turing.Tape.move dir tape) := by
--   let tm := Routines.move (Γ := Γ) dir
--   exact TM.transforms_of_inert tm _ _ (move.inert_after_stop dir) ⟨1, rfl⟩

-- @[simp]
-- lemma Routines.move.eval {Γ} [Inhabited Γ] [DecidableEq Γ]
--   (tape : Turing.Tape Γ)
--   (dir : Turing.Dir) :
--   (Routines.move dir).eval (fun _ => tape) =
--     .some (fun _ => Turing.Tape.move dir tape) :=
--   TM.eval_of_transforms Routines.move.semantics

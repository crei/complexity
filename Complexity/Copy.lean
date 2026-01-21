import Complexity.AbstractTape
import Complexity.TuringMachine
import Complexity.TapeLemmas
import Complexity.Routines
import Complexity.MoveUntil
import Complexity.TMComposition
import Complexity.WithTapes

import Mathlib

def copy_core : TM 2 (Fin 2) SChar :=
  let σ := fun state symbols =>
    match state with
    | 0 => match symbols 0 with
      | .blank => (1, fun _ => (.blank, some .right))
      | c => (0, fun _ => (c, some .left))
    | 1 => (1, (symbols ·, none))
  TM.mk σ 0 1

lemma copy_core.step (c : SChar) (h_c_neq : c ≠ .blank) (l ws₁ ws₂ : List SChar) :
  copy_core.transition.step
    ⟨0, [Turing.Tape.mk₂ l (c :: ws₁), (Turing.Tape.mk₁ ws₂).move .left].get⟩ =
    ⟨0, [(Turing.Tape.mk₂ l (c :: ws₁)).move .left,
         (Turing.Tape.mk₁ (c :: ws₂)).move .left].get⟩ := by
  ext1
  · simp [Transition.step, copy_core, Turing.Tape.mk₂]
  · funext t
    refine Fin.cases ?_ ?_ t <;> simp [Transition.step, copy_core, Turing.Tape.mk₂, performTapeOps]

lemma copy_core.last_step (l ws₁ ws₂ : List SChar) :
  copy_core.transition.step
    ⟨0, [Turing.Tape.mk₂ l (.blank :: ws₁), (Turing.Tape.mk₁ ws₂).move .left].get⟩ =
    ⟨1, [(Turing.Tape.mk₂ l (.blank :: ws₁)).move .right, Turing.Tape.mk₁ ws₂].get⟩ := by
  have h_blank_default : SChar.blank = default := rfl
  ext1
  · simp [Transition.step, copy_core, Turing.Tape.mk₂]
  · funext t
    refine Fin.cases ?_ ?_ t <;>
    simp [Transition.step, copy_core, Turing.Tape.mk₁, Turing.Tape.mk₂,
          performTapeOps, h_blank_default]

lemma copy_core.configurations (l ws₁ ws₂ : List SChar) (h_neq_blank : ∀ i, l.get i ≠ .blank) :
  copy_core.configurations
    [(Turing.Tape.mk₂ l ws₁).move .left, (Turing.Tape.mk₁ ws₂).move .left].get l.length.succ =
    ⟨1, [Turing.Tape.mk₁ (l.reverse ++ ws₁), Turing.Tape.mk₁ (l.reverse ++ ws₂)].get⟩ := by
  have h_blank_default : SChar.blank = default := rfl
  induction l generalizing ws₁ ws₂ with
  | nil =>
    unfold TM.configurations
    dsimp
    convert copy_core.last_step [] ws₁ ws₂ <;>
    simp [Turing.Tape.mk₂, Turing.Tape.mk₁, h_blank_default]
  | cons c l ih =>
    have h_c_non_blank : c ≠ SChar.blank := by
      simpa using (h_neq_blank ⟨0, by simp⟩)
    unfold TM.configurations
    simp only [List.length_cons, Nat.succ_eq_add_one, Fin.isValue]
    rw [Function.iterate_succ_apply]
    have h_start_is_zero : copy_core.startState = 0 := rfl
    let h_step := copy_core.step c h_c_non_blank l ws₁ ws₂
    rw [Tape.move_left_cons, h_start_is_zero, h_step]
    have h_l_neq_blank : ∀ i, l.get i ≠ .blank := by
      intro i; exact h_neq_blank i.succ
    specialize ih (c :: ws₁) (c :: ws₂) h_l_neq_blank
    unfold TM.configurations at ih
    rw [← h_start_is_zero, ih]
    grind

lemma copy_core.inert_after_stop : copy_core.inert_after_stop := by
  intro conf h_is_stopped
  ext <;> simp_all [Transition.step, performTapeOps, copy_core]

lemma copy_core.semantics (l ws₁ ws₂ : List SChar) (h_neq_blank : ∀ i, l.get i ≠ .blank) :
  copy_core.transforms
    [Turing.Tape.mk₂ l (.sep :: ws₁), (Turing.Tape.mk₁ ws₂).move .left].get
    [Turing.Tape.mk₁ (l.reverse ++ (.sep :: ws₁)),
     Turing.Tape.mk₁ (l.reverse ++ (.sep :: ws₂))].get := by
  refine TM.transforms_of_inert copy_core _ _ copy_core.inert_after_stop ?_
  use l.length.succ.succ
  have : Turing.Tape.mk₂ l (.sep :: ws₁) = (Turing.Tape.mk₂ (.sep :: l) ws₁).move .left := by simp
  rw [this]
  have : l.length.succ.succ = (.sep ::l).length.succ := by simp
  rw [this]
  have h_not_blank : ∀ i : Fin l.length.succ, (SChar.sep :: l)[i] ≠ SChar.blank := by
    intro i
    refine Fin.induction ?_ ?_ i
    · simp
    · intro i ih; simpa using (h_neq_blank i)
  rw [copy_core.configurations (.sep :: l) ws₁ ws₂ h_not_blank]
  simp [copy_core]
  grind

--- This is a 2-tape Turing machine that copies the first word from the first tape
--- to the second tape.
def copy :=
  ((((move_until .right (fun c => (c = SChar.sep))).extend (by omega)).seq
  ((Routines.move .left).with_tapes #v[(1 : Fin 2)] (h_le := by omega))).seq
  copy_core)

theorem copy.semantics (w : List Char) (ws₁ ws₂ : List (List Char)) :
  copy.transforms_list [w :: ws₁, ws₂].get [w :: ws₁, w :: ws₂].get := by
  let tm₁ : TM 2 _ _  := ((move_until .right (fun c => (c = SChar.sep))).extend (by omega))
  let tm₂ : TM 2 _ SChar := ((Routines.move .left).with_tapes #v[(1 : Fin 2)] (h_le := by omega))
  have h_copy_eq : copy = (tm₁.seq tm₂).seq copy_core := rfl
  have h_part1 : tm₁.transforms
        (list_to_tape ∘ [w :: ws₁, ws₂].get)
        [Turing.Tape.mk₂ w.coe_schar.reverse (.sep :: (list_to_string ws₁)),
         list_to_tape ws₂].get := by
    sorry
  have h_part2 : tm₂.transforms
        [Turing.Tape.mk₂ w.coe_schar.reverse (.sep :: (list_to_string ws₁)),
         list_to_tape ws₂].get
        [Turing.Tape.mk₂ w.coe_schar.reverse (.sep :: (list_to_string ws₁)),
         (list_to_tape ws₂).move .left].get := by
    sorry
  have h_core : copy_core.transforms
        [Turing.Tape.mk₂ w.coe_schar.reverse (.sep :: (list_to_string ws₁)),
         (list_to_tape ws₂).move .left].get
        (list_to_tape ∘ [w :: ws₁, w :: ws₂].get) := by
    sorry

  exact TM.seq.semantics (TM.seq.semantics h_part1 h_part2) h_core

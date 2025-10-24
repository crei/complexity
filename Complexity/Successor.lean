import Complexity.TuringMachine
import Complexity.Dyadic

import Mathlib

inductive OneTwo where
  | one
  | two

def succ_transition : Transition 1 (Fin 2) (Option OneTwo) :=
  fun state symbols =>
    match state with
    | 0 => match symbols 0 with
      | none => (1, fun _ => (some .one, none))
      | some .one => (1, fun _ => (some .two, none))
      | some .two => (0, fun _ => (some .one, some .right))
    | 1 => (1, (symbols ·, none))

theorem stop_state_inert (tapes : Fin 1 → Turing.Tape (Option OneTwo)) (n : ℕ) :
  succ_transition.n_steps ⟨1, tapes⟩ n = ⟨1, tapes⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold Transition.n_steps
    simp [succ_transition, Transition.step, ih]

-- A Turing machine that computes the successor of a
-- reversely encoded dyadic number
def succ_tm : TM 1 (Fin 2) (Option OneTwo) := {
  transition := succ_transition
  startState := 0
  stopState := 1
}

def rev_dya (n : ℕ) : List OneTwo :=
  (dyadic_encoding_reverse n).map (fun x => if x then .two else .one)

@[simp]
lemma rev_dya_zero : rev_dya 0 = [] := by
  simp [rev_dya, dyadic_encoding_reverse]

@[simp]
lemma rev_dya_odd (n : ℕ) : rev_dya (2 * n + 1) = .one :: rev_dya (n) := by
  simp [rev_dya, dyadic_encoding_reverse_prop_one]

@[simp]
lemma rev_dya_even (n : ℕ) : rev_dya (2 * n + 2) = .two :: rev_dya (n) := by
  simp [rev_dya, dyadic_encoding_reverse_prop_two]


lemma succ_step_odd (n : ℕ) (pref : List BlankChar) :
  succ_transition.step (⟨0, (fun _ => Turing.Tape.mk₂ pref (rev_dya (2 * n + 1)))⟩) =
    ⟨1, (fun _ => Turing.Tape.mk₂ pref (rev_dya (2 * n + 2)))⟩ := by
  rw [rev_dya_odd]
  simp [succ_transition, Transition.step, Turing.Tape.mk₂]

lemma succ_step_even' (n : ℕ) (pref : List BlankChar) :
  let σ' := succ_transition.step (⟨0, (fun _ => Turing.Tape.mk₂ pref (rev_dya (2 * n + 2)))⟩)
  σ'.state = 0 ∧ (σ'.tapes 0).move .left = Turing.Tape.mk₂ pref ('1' :: rev_dya n) := by
  rw [rev_dya_even]
  simp [succ_transition, Transition.step, Turing.Tape.mk₂, performTapeOps]

lemma succ_step_even (n : ℕ) (pref : List BlankChar) :
  succ_transition.step (⟨0, (fun _ => Turing.Tape.mk₂ pref (rev_dya (2 * n + 2)))⟩) =
    ⟨0, fun _ => (Turing.Tape.mk₂ pref ('1' :: rev_dya n)).move .right⟩ := by
  rw [rev_dya_even]
  simp [succ_transition, Transition.step, Turing.Tape.mk₂, performTapeOps]

theorem succ_semantics (n : ℕ) (pref : List BlankChar) :
  ∃ shift : ℕ,
  succ_transition.n_steps (⟨0, (fun _ => Turing.Tape.mk₂ pref (rev_dya n))⟩) ((n + 2).log2 + 1) =
  ⟨1, fun _ => (Turing.Tape.move .right)^[shift] (Turing.Tape.mk₂ pref (rev_dya (n + 1)))⟩ := by
  revert pref
  refine dyadic_induction_on n ?_ ?_ ?_
  · intro pref
    use 0;
    simp [Transition.n_steps, Transition.step, succ_transition, Turing.Tape.mk₂, default]
    simp [rev_dya, dyadic_encoding_reverse]
  · intro n ih pref
    use 0
    rw [← n_steps_first, succ_step_odd]
    simp [stop_state_inert]
  · intro n ih pref
    rw [← n_steps_first, succ_step_even]
    simp [Turing.Tape.mk₂]
    rw [← Turing.Tape.mk₂]
    obtain ⟨shift, ih⟩ := ih ('1' :: pref)
    use shift + 1
    rw [Nat.log2_def]
    simp_all
    unfold Turing.Tape.mk₂
    have hn : 2 * n + 2 + 1 = 2 * (n + 1) + 1 := by ring
    rw [hn]
    simp [rev_dya_odd]

theorem succ_in_linear_time (n : ℕ) : succ_tm.runs_in_time
    (rev_dya n)
    (rev_dya n.succ)
    ((n + 2).log2 + 1) := by
  obtain ⟨shift, hstep⟩ := succ_semantics n []
  rw [Turing.Tape.mk₂] at hstep
  simp [TM.runs_in_time, TM.runs_in_exact_time, TM.initial_configuration]
  use (n + 2).log2 + 1
  simp [succ_tm, Turing.Tape.mk₁, Turing.Tape.mk₂, hstep]
  use shift, .left;
  simp

-- theorem succ_in_dtime_id: dtime_nat id Nat.succ := by

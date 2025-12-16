import Complexity.TuringMachine
import Complexity.Dyadic
import Complexity.TapeLemmas
import Complexity.Classes

import Mathlib

inductive OneTwo where
  | one
  | two
  deriving DecidableEq, Fintype

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

@[simp]
lemma succ_transition.inert
  (c : Configuration 1 (Fin 2) (Option OneTwo))
  (h_is_stopped : c.state = 1) :
  succ_transition.step c = c := by
  unfold Transition.step; ext <;> simp [succ_transition, h_is_stopped]

def rev_dya (n : ℕ) : List OneTwo :=
  (dyadic_encoding_reverse n).map (fun x => if x then .two else .one)

def rev_dya_option (n : ℕ) : List (Option OneTwo) :=
  (rev_dya n).map some

@[simp]
lemma rev_dya_zero : rev_dya_option 0 = [] := by
  simp [rev_dya_option, rev_dya, dyadic_encoding_reverse]

@[simp]
lemma rev_dya_odd (n : ℕ) : rev_dya (2 * n + 1) = .one :: rev_dya (n) := by
  simp [rev_dya, dyadic_encoding_reverse_prop_one]

@[simp]
lemma rev_dya_option_odd (n : ℕ) :
    rev_dya_option (2 * n + 1) = (some .one) :: rev_dya_option (n) := by
  simp [rev_dya_option]

@[simp]
lemma rev_dya_even (n : ℕ) : rev_dya (2 * n + 2) = .two :: rev_dya (n) := by
  simp [rev_dya, dyadic_encoding_reverse_prop_two]

@[simp]
lemma rev_dya_option_even (n : ℕ) :
    rev_dya_option (2 * n + 2) = (some .two) :: rev_dya_option (n) := by
  simp [rev_dya_option]

theorem rev_dya_bijective : Function.Bijective rev_dya := by
  exact Function.Bijective.comp
    (Function.Bijective.list_map (by decide)) dyadic_encoding_reverse_bijective

theorem rev_dya_length (n : ℕ) : (rev_dya n).length = (n + 1).log2 := by
  simp [rev_dya, dyadic_reverse_length]

lemma succ_step_odd (n : ℕ) (pref : List (Option OneTwo)) :
  succ_transition.step (⟨0, (fun _ => Turing.Tape.mk₂ pref (rev_dya_option (2 * n + 1)))⟩) =
    ⟨1, (fun _ => Turing.Tape.mk₂ pref (rev_dya_option (2 * n + 2)))⟩ := by
  simp [succ_transition, Transition.step, Turing.Tape.mk₂]

lemma succ_step_even' (n : ℕ) (pref : List (Option OneTwo)) :
  let σ' := succ_transition.step (⟨0, (fun _ => Turing.Tape.mk₂ pref (rev_dya_option (2 * n + 2)))⟩)
  σ'.state = 0 ∧
  (σ'.tapes 0).move .left = Turing.Tape.mk₂ pref ((some .one) :: rev_dya_option n) := by
  simp [succ_transition, Transition.step, Turing.Tape.mk₂, performTapeOps]

lemma succ_step_even (n : ℕ) (pref : List (Option OneTwo)) :
  succ_transition.step (⟨0, (fun _ => Turing.Tape.mk₂ pref (rev_dya_option (2 * n + 2)))⟩) =
    ⟨0, fun _ => (Turing.Tape.mk₂ pref ((some .one) :: rev_dya_option n)).move .right⟩ := by
  simp [succ_transition, Transition.step, Turing.Tape.mk₂, performTapeOps]

theorem succ_semantics (n : ℕ) (pref : List (Option OneTwo)) :
  ∃ shift : ℕ,
  succ_transition.n_steps (⟨
    0, (fun _ => Turing.Tape.mk₂ pref (rev_dya_option n))
  ⟩) ((n + 2).log2 + 1) =
  ⟨1, fun _ =>
    (Turing.Tape.move .right)^[shift] (Turing.Tape.mk₂ pref (rev_dya_option (n + 1)))⟩ := by
  revert pref
  refine dyadic_induction_on n ?_ ?_ ?_
  · intro pref
    use 0;
    simp [Transition.n_steps, Transition.step, succ_transition, Turing.Tape.mk₂, default]
    simp [rev_dya_option, rev_dya, dyadic_encoding_reverse]
  · intro n ih pref
    use 0
    rw [← n_steps_first, succ_step_odd]
    simp [stop_state_inert]
  · intro n ih pref
    rw [← n_steps_first, succ_step_even]
    simp only [Fin.isValue, Turing.Tape.mk₂, Turing.Tape.move_right_mk', Turing.ListBlank.head_mk,
      List.headI_cons, Turing.ListBlank.cons_mk, Turing.ListBlank.tail_mk, List.tail_cons]
    rw [← Turing.Tape.mk₂]
    obtain ⟨shift, ih⟩ := ih ((some .one):: pref)
    use shift + 1
    rw [Nat.log2_def]
    have hn : 2 * n + 2 + 1 = 2 * (n + 1) + 1 := by ring
    simp_all [Turing.Tape.mk₂]

theorem succ_in_linear_time_via_rev_dya (n : ℕ) : succ_tm.runs_in_time
    (rev_dya n)
    (rev_dya n.succ)
    ((n + 2).log2 + 1) := by
  obtain ⟨shift, hstep⟩ := succ_semantics n []
  rw [Turing.Tape.mk₂, rev_dya_option] at hstep
  apply TM.runs_in_time_of_inert succ_tm _ _ _
    (by intro c h_state; simpa using succ_transition.inert c h_state)
  simp only [TM.stops_and_outputs, Nat.reduceAdd, TM.configurations_on_input,
    TM.initial_configuration, Fin.val_eq_zero, ↓reduceIte, Fin.zero_eta, Fin.isValue,
    Nat.succ_eq_add_one]
  simp only [succ_tm, Fin.isValue, Turing.Tape.mk₁, Turing.Tape.mk₂, hstep, and_true]
  use shift, .left;
  simp [rev_dya_option]

theorem dya_succ_in_linear_time :
    succ_tm.computes_in_o_time (rev_dya ∘ Nat.succ ∘ (Function.invFun rev_dya)) ⟨id⟩ := by
  use ⟨fun n => 2 * n + 2⟩
  have h_bound : ⟨fun n => 2 * n + 2⟩ ≼ ⟨id⟩ := by use 2; intro n; simp
  simp only [h_bound, true_and]
  intro input
  let n := rev_dya.invFun input
  have hn : rev_dya n = input := by
    exact Function.rightInverse_invFun rev_dya_bijective.2 input
  rw [← hn]
  simp only [Function.comp_apply, Function.leftInverse_invFun rev_dya_bijective.1 n,
    Nat.succ_eq_add_one]
  have h_len : ((n + 2).log2 + 1) ≤ (2 * (rev_dya n).length + 2) := by
    simp only [rev_dya_length, add_le_add_iff_right]
    calc (n + 2).log2
        _ ≤ (2 * n + 2).log2 := by
          simpa [Nat.log2_eq_log_two] using (Nat.log_monotone (by linarith))
        _ = (2 * (n + 1)).log2 := by ring_nf
        _ = (n + 1).log2 + 1 := by simp [Nat.log2_two_mul]
        _ ≤ 2 * (n + 1).log2 + 1 := by linarith
  exact succ_tm.runs_in_time_monotone (rev_dya n) (rev_dya n.succ) h_len
    (succ_in_linear_time_via_rev_dya n)

-- Main theorem: successor is computable in linear time
theorem succ_in_linear_time : dtime_nat id Nat.succ := by
  use OneTwo, rev_dya
  constructor
  · exact rev_dya_bijective
  · use 0, Fin 2, succ_tm
    exact ⟨Finite.of_fintype OneTwo, Finite.of_fintype (Fin 2), dya_succ_in_linear_time⟩

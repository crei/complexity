import Complexity.TuringMachine
import Complexity.Dyadic

import Mathlib

def succ_transition : Transition 1 (Fin 2) BlankChar :=
  fun state symbols =>
    match state with
    | 0 => match symbols 0 with
      | ' ' => (1, fun _ => ('1', none))
      | '1' => (1, fun _ => ('2', none))
      | '2' => (0, fun _ => ('1', some .right))
      | c => (0, fun _ => (c, some .right)) -- should not happen
    | 1 => (1, (symbols ·, none))

theorem stop_state_inert (tapes : Fin 1 → Turing.Tape BlankChar) (n : ℕ) :
  succ_transition.n_steps ⟨1, tapes⟩ n = ⟨1, tapes⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold Transition.n_steps
    simp [succ_transition, Transition.step, ih]

-- A Turing machine that computes the successor of a
-- reversely encoded dyadic number
def succ_tm : TM 1 (Fin 2) BlankChar := {
  transition := succ_transition
  startState := 0
  stopState := 1
}

def rev_dya (n : ℕ) : List BlankChar :=
  (dyadic_encoding_reverse n).map (fun x => if x then '2' else '1')

@[simp]
lemma rev_dya_zero : rev_dya 0 = [] := by
  simp [rev_dya, dyadic_encoding_reverse]

@[simp]
lemma rev_dya_odd (n : ℕ) : rev_dya (2 * n + 1) = '1' :: rev_dya (n) := by
  simp [rev_dya, dyadic_encoding_reverse_prop_one]

@[simp]
lemma rev_dya_even (n : ℕ) : rev_dya (2 * n + 2) = '2' :: rev_dya (n) := by
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

theorem succ_semantics' (n : ℕ) (pref : List BlankChar) :
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


theorem listblank_cons_default_to_empty {Γ} [Inhabited Γ] :
  (Turing.ListBlank.mk [default] : Turing.ListBlank Γ) = Turing.ListBlank.mk [] := by
  have h2 : Turing.BlankRel ([default] : List Γ) [] := by
    unfold Turing.BlankRel; right; use 1; simp
  apply Quotient.sound
  exact h2

theorem listblank_all_blank_is_empty {Γ} [Inhabited Γ]
  (list : List Γ)
  (all_empty : ∀ i, list.getI i = default) :
  Turing.ListBlank.mk list = Turing.ListBlank.mk [] := by
  apply Turing.ListBlank.ext
  simp [all_empty]

theorem listblank_is_empty_all_blank {Γ} [Inhabited Γ]
  (list : Turing.ListBlank Γ)
  (is_empty : list = Turing.ListBlank.mk []) :
  ∀ i, list.nth i = default := by
  intro i
  subst is_empty
  simp_all only [List.getI_nil, Turing.ListBlank.nth_mk]

lemma cons_is_empty {Γ} [Inhabited Γ]
  (c : Γ)
  (list : Turing.ListBlank Γ)
  (is_empty : Turing.ListBlank.cons c list = Turing.ListBlank.mk []) :
  c = default := by
  simpa using listblank_is_empty_all_blank (Turing.ListBlank.cons c list ) is_empty 0

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

-- A Turing machine that computes the successor of a
-- reversely encoded dyadic number
def succ_tm : TM 1 (Fin 2) BlankChar := {
  transition := succ_transition
  startState := 0
  stopState := 1
}

def rev_dya (n : ℕ) : List BlankChar :=
  (dyadic_encoding_reverse n).map (fun x => if x then '2' else '1')


lemma rev_dya_odd (n : ℕ) : rev_dya (2 * n + 1) = '1' :: rev_dya (n) := by
  simp [rev_dya, dyadic_encoding_reverse_prop_one]

lemma rev_dya_even (n : ℕ) : rev_dya (2 * n + 2) = '2' :: rev_dya (n) := by
  simp [rev_dya, dyadic_encoding_reverse_prop_two]


lemma succ_step (n : ℕ)
  (pref : List BlankChar) :
  let σ' := succ_transition.step (⟨ 0, (fun _ => Turing.Tape.mk₂ pref (rev_dya (2 * n + 1)))⟩)
  σ'.state = 1 ∧ σ'.tapes 0 = Turing.Tape.mk₂ pref (rev_dya (2 * n + 2)) := by
  rw [rev_dya_odd]
  simp [succ_transition, Transition.step, Turing.Tape.mk₂]
  rw [← Turing.ListBlank.cons_mk]
  simp only [Turing.Tape.write_mk']
  simp [rev_dya_even]

-- What we want to prove is:
-- For any n : ℕ, if TM starts with the tape containing the
-- reverse dyadic encoding of n,
-- then whet in reaches state 1, it will have the reverse dyadic encoding of n + 1 on the tape.


-- theorem succ_semantics (n : ℕ) :
--   succ_tm.runs_in_time (rev_dya n) (rev_dya (n + 1)) (rev_dya n).length.succ := sorry


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

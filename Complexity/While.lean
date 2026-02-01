import Complexity.TuringMachine
import Complexity.Dyadic
import Complexity.TapeLemmas
import Complexity.AbstractTape

import Mathlib

inductive WhileState (Q : Type*) where
  | main (q : Fin 2)
  | sub_routine (q : Q)
  deriving DecidableEq

--- Repeatedly run a sub routine as long as a condition on the symbol
--- at the first head is true.
def Routines.while {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Q]
  (condition : Γ → Bool) (tm : TM k.succ Q Γ) :
  TM k.succ (WhileState Q) Γ :=
  let σ := fun state symbols =>
    match state with
    | .main 0 => if condition (symbols 0) then
        (.sub_routine tm.startState, (symbols · , none))
      else
        (.main 1, (symbols ·, none))
    | .sub_routine s => if s = tm.stopState then
        (.main 0, (symbols ·, none))
      else
        let ⟨s, op⟩ := tm.transition s symbols
        (.sub_routine s, op)
    | s => (s, (symbols ·, none))
  TM.mk σ (.main 0) (.main 1)

lemma Routines.while.inert_after_stop {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Q]
  (tm : TM k.succ Q Γ) (condition : Γ → Bool) :
  (Routines.while condition tm).inert_after_stop := by
  intro conf h_is_stopped
  ext <;> simp_all [Transition.step, performTapeOps, Routines.while]

-- Helper lemma: while machine in subroutine state mirrors tm's execution
lemma Routines.while.subroutine_runs_tm {k : ℕ} {Q Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  (condition : Γ → Bool)
  (tm : TM k.succ Q Γ)
  (tapes₀ tapes₁ : Fin k.succ → Turing.Tape Γ)
  (t : ℕ)
  (h_transform : tm.transforms_in_exact_time tapes₀ tapes₁ t) :
  (Routines.while condition tm).transition.step^[t] ⟨.sub_routine tm.startState, tapes₀⟩ =
    ⟨.sub_routine tm.stopState, tapes₁⟩ := by
  have h_mirror : ∀ i ≤ t,
    (Routines.while condition tm).transition.step^[i] ⟨.sub_routine tm.startState, tapes₀⟩ =
      ⟨.sub_routine (tm.configurations tapes₀ i).state, (tm.configurations tapes₀ i).tapes⟩ := by
    intro i h_i_le
    induction i with
    | zero => simp [TM.configurations]
    | succ i ih =>
      have h_i_lt : i < t := Nat.lt_of_succ_le h_i_le
      specialize ih (Nat.le_of_lt h_i_lt)
      rw [Function.iterate_succ_apply', ih]
      simp only [Transition.step, Routines.while]
      have h_not_stopped : (tm.configurations tapes₀ i).state ≠ tm.stopState :=
        h_transform.2 i h_i_lt
      simp only [TM.configurations] at h_not_stopped ⊢
      split
      · contradiction
      · simp only [Function.iterate_succ_apply', Configuration.mk.injEq,
          WhileState.sub_routine.injEq]
        exact ⟨ rfl, rfl ⟩
  rw [h_mirror t (Nat.le_refl t), h_transform.1]

lemma Routines.while.single_iter {k : ℕ} {Q Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  (condition : Γ → Bool)
  (tm : TM k.succ Q Γ)
  (tapes₀ tapes₁ : Fin k.succ → Turing.Tape Γ)
  (t : ℕ)
  (h_transform : tm.transforms_in_exact_time tapes₀ tapes₁ t)
  (h_not_stops : condition (tapes₀ 0).head) :
  (Routines.while condition tm).configurations (tapes₀) (t + 2) = ⟨.main 0, tapes₁⟩ := by
  let tm_while := Routines.while condition tm
  have h_step1 : tm_while.transition.step ⟨tm_while.startState, tapes₀⟩ =
      ⟨.sub_routine tm.startState, tapes₀⟩ := by
    simp [Transition.step, Routines.while, tm_while, performTapeOps, h_not_stops]
  have h_subroutine := Routines.while.subroutine_runs_tm condition tm tapes₀ tapes₁ t h_transform
  have h_step_t_plus_1 : tm_while.configurations tapes₀ (t + 1) =
      ⟨.sub_routine tm.stopState, tapes₁⟩ := by
    unfold TM.configurations
    rw [Function.iterate_succ_apply, h_step1, h_subroutine]
  unfold TM.configurations
  rw [Function.iterate_succ_apply']
  unfold TM.configurations at h_step_t_plus_1
  rw [h_step_t_plus_1]
  simp [Transition.step, Routines.while, performTapeOps]

lemma Routines.while.exit {k : ℕ} {Q Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  (condition : Γ → Bool)
  (tm : TM k.succ Q Γ)
  (tapes : Fin k.succ → Turing.Tape Γ)
  (h_exits : ¬condition (tapes 0).head) :
  (Routines.while condition tm).configurations tapes 1 = ⟨.main 1, tapes⟩ := by
  simp [Routines.while, TM.configurations, Transition.step, performTapeOps, h_exits]

--- Given a sequence of tape states between iterations of the while loop,
--- and given that the subroutine tm correctly transforms each tape state to the next,
--- then the while machine transforms the initial tape state to the final tape state.
theorem Routines.while.semantics {k : ℕ} {Q Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  (condition : Γ → Bool)
  (tm : TM k.succ Q Γ)
  (tapes : ℕ → Fin k.succ → Turing.Tape Γ)
  (h_transform : ∀ i, tm.transforms (tapes i) (tapes i.succ))
  (h_stops : ∃ m, ¬condition (tapes m 0).head) :
  (Routines.while condition tm).transforms (tapes 0) (tapes (Nat.find h_stops)) := by
  let tm_while := Routines.while condition tm
  apply TM.transforms_of_inert tm_while _ _ (Routines.while.inert_after_stop _ _)
  let iter_count := Nat.find h_stops
  have h_no_stop : ∀ i < iter_count, condition (tapes i 0).head := by
    intro i hi; simpa using Nat.find_min h_stops hi
  -- for each iteration, there is a step count from the start to reach the start state again.
  have h_iter_time : ∀ i ≤ iter_count, ∃ t : ℕ,
      tm_while.configurations (tapes 0) t = ⟨.main 0, tapes i⟩ := by
    intro i hi
    induction i with
    | zero => exact ⟨0, rfl⟩
    | succ i ih =>
      obtain ⟨ t, ht ⟩ := ih ( Nat.le_of_succ_le hi );
      have h_time : ∃ t', (tm_while.configurations (tapes i) t' = ⟨.main 0, tapes (i + 1)⟩) := by
        obtain ⟨ t', ht' ⟩ := h_transform i
        use t' + 2
        simpa using Routines.while.single_iter condition tm
          (tapes i) (tapes (i + 1)) t' ht' (h_no_stop i (Nat.lt_of_succ_le hi))
      obtain ⟨ t', ht' ⟩ := h_time
      use t' + t
      unfold TM.configurations at ht ht' ⊢
      have h_startState : .main 0 = tm_while.startState := rfl
      simp [Function.iterate_add, ht', ht, h_startState]
  obtain ⟨ t, ht ⟩ := h_iter_time iter_count le_rfl
  use t + 1
  convert Routines.while.exit condition tm (tapes iter_count) (Nat.find_spec h_stops) using 1
  convert congr_arg (tm_while.transition.step) ht using 1
  exact Function.iterate_succ_apply' _ _ _

-- Semantics of Routines.while in terms of `eval.`.
-- Note that this only works for Turing machines that always halt
-- on the sequence of iterated inputs.
@[simp]
theorem Routines.while.eval' {k : ℕ} {Q Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  {condition : Γ → Bool} {tm : TM k.succ Q Γ}
  (tapes_seq : ℕ → (Fin k.succ → (Turing.Tape Γ)))
  (h_inner : ∀ i, tm.eval (tapes_seq i) = .some (tapes_seq i.succ)) :
  (Routines.while condition tm).eval (tapes_seq 0) =
    (PartENat.find
      fun i => ¬condition (((tapes_seq i) 0).head)
    ).map tapes_seq := by
  by_cases h_halts: ∃ i, ¬condition ((tapes_seq i) 0).head
  · convert TM.eval_of_transforms (Routines.while.semantics condition tm tapes_seq
      (by intro i; exact TM.transforms_of_eval (h_inner i))
      (by convert h_halts))
    rw [Part.eq_some_iff]
    obtain ⟨i, h_halts⟩ := h_halts
    use ⟨i, by simp [h_halts]⟩
    simp
  · have h_no_halts : (PartENat.find fun i => ¬condition (tapes_seq i 0).head) = Part.none := by
      sorry
    sorry
    -- rw [h_no_halts]
    -- simp
    -- rw [Part.eq_none_iff']
    -- simp [TM.eval, PartENat.find]
    -- by_contra h_does_halt
    -- simp at h_does_halt
    -- obtain ⟨t, h_does_halt⟩ := h_does_halt
    -- simp at h_halts
    -- sorry

theorem Routines.while.eval {k : ℕ} {Q Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  {condition : Γ → Bool} {tm : TM k.succ Q Γ}
  (semantics : (Fin k.succ → (Turing.Tape Γ)) → (Fin k.succ → (Turing.Tape Γ)))
  (h_inner : ∀ tapes, tm.eval tapes = .some (semantics tapes))
  (tapes : Fin k.succ → Turing.Tape Γ) :
  (Routines.while condition tm).eval tapes =
    (PartENat.find
      fun i => ¬condition (((semantics^[i] tapes) 0).head)
    ).map (semantics^[·] tapes) := by
  sorry

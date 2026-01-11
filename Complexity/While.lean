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
      have h_not_stopped : (tm.configurations tapes₀ i).state ≠ tm.stopState := h_transform.2 i h_i_lt
      simp only [TM.configurations] at h_not_stopped ⊢
      split
      · contradiction
      ·
        simp +decide [ *, Function.iterate_succ_apply' ];
        exact ⟨ rfl, rfl ⟩ -- This should be rfl but needs additional unfolding
  rw [h_mirror t (Nat.le_refl t), h_transform.1]

lemma Routines.while.single_iter {k : ℕ} {Q Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  (condition : Γ → Bool)
  (tm : TM k.succ Q Γ)
  (tapes₀ tapes₁ : Fin k.succ → Turing.Tape Γ)
  (t : ℕ)
  (h_transform : tm.transforms_in_exact_time tapes₀ tapes₁ t)
  (h_not_stops : condition (tapes₀ 0).head) :
  (Routines.while condition tm).configurations (tapes₀) (t + 2) =
    ⟨.main 0, tapes₁⟩ := by
  -- Step 1: Enter the subroutine
  have h_step1 : (Routines.while condition tm).transition.step^[1] ⟨(Routines.while condition tm).startState, tapes₀⟩ =
    ⟨.sub_routine tm.startState, tapes₀⟩ := by
    simp only [Function.iterate_one, Transition.step, Routines.while]
    simp [performTapeOps, h_not_stops]
  -- Use the helper lemma to run the subroutine for t steps
  have h_subroutine := Routines.while.subroutine_runs_tm condition tm tapes₀ tapes₁ t h_transform
  -- Combine: 1 step to enter + t steps to run = step t+1 is at stopState
  have h_step_t_plus_1 : (Routines.while condition tm).configurations tapes₀ (t + 1) =
    ⟨.sub_routine tm.stopState, tapes₁⟩ := by
    show (Routines.while condition tm).transition.step^[t + 1] ⟨(Routines.while condition tm).startState, tapes₀⟩ = _
    calc (Routines.while condition tm).transition.step^[t + 1] ⟨(Routines.while condition tm).startState, tapes₀⟩
      _ = (Routines.while condition tm).transition.step^[1 + t] ⟨(Routines.while condition tm).startState, tapes₀⟩ := by rw [Nat.add_comm]
      _ = (Routines.while condition tm).transition.step^[t] ((Routines.while condition tm).transition.step^[1] ⟨(Routines.while condition tm).startState, tapes₀⟩) := by
        rw [ add_comm, Function.iterate_add_apply ]
      _ = (Routines.while condition tm).transition.step^[t] ⟨.sub_routine tm.startState, tapes₀⟩ := by
        -- Substitute h_step1 into the left-hand side of the equation.
        rw [h_step1]
      _ = ⟨.sub_routine tm.stopState, tapes₁⟩ := h_subroutine
  -- Step t+2: Detect stop and return to main 0
  show (Routines.while condition tm).transition.step^[t + 2] _ = _
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

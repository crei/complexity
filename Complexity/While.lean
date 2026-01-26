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
-- and whose semantics is explicitly given by `semantics`.
-- Helper lemma: if tm always halts and semantics describes its behavior,
-- and condition is always true, then the while machine never halts
lemma Routines.while.no_halt_if_condition_always_true {k : ℕ} {Q Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  (condition : Γ → Bool)
  (tm : TM k.succ Q Γ)
  (semantics : (Fin k.succ → (Turing.Tape Γ)) → (Fin k.succ → (Turing.Tape Γ)))
  (h_inner : ∀ tapes, tm.eval tapes = .some (semantics tapes))
  (tapes : Fin k.succ → Turing.Tape Γ)
  (h_always_true : ∀ i, condition ((semantics^[i] tapes) 0).head) :
  ∀ t, ((Routines.while condition tm).configurations tapes t).state ≠
       (Routines.while condition tm).stopState := by
  intro t
  -- The stop state is .main 1
  show ((Routines.while condition tm).configurations tapes t).state ≠ .main 1
  -- We need to show that at each time step, we're either in .main 0 or .sub_routine state
  -- and never reach .main 1 because condition is always true
  have h_transforms : ∀ i, tm.transforms (semantics^[i] tapes) (semantics^[i.succ] tapes) := by
    intro i
    have : semantics (semantics^[i] tapes) = semantics^[i.succ] tapes := by
      simp [Function.iterate_succ_apply']
    rw [← this]
    exact TM.transforms_of_eval (h_inner (semantics^[i] tapes))
  -- The key is that the machine behavior follows a pattern based on semantics iterations
  -- But this is complex to formalize without more infrastructure
  sorry

@[simp]
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
  have h_transforms : ∀ i, tm.transforms (semantics^[i] tapes) (semantics^[i.succ] tapes) := by
    intro i
    have : semantics (semantics^[i] tapes) = semantics^[i.succ] tapes := by
      simp [Function.iterate_succ_apply']
    rw [← this]
    exact TM.transforms_of_eval (h_inner (semantics^[i] tapes))
  by_cases h_stops : ∃ m, ¬condition ((semantics^[m] tapes) 0).head
  · -- Case: the while loop terminates
    have h_while_transforms : (Routines.while condition tm).transforms tapes (semantics^[Nat.find h_stops] tapes) :=
      Routines.while.semantics condition tm (semantics^[·] tapes) h_transforms h_stops
    rw [TM.eval_of_transforms h_while_transforms]
    simp [PartENat.find, Part.map_some]
    sorry
  · -- Case: the while loop does not terminate
    push_neg at h_stops
    have h_no_halt := Routines.while.no_halt_if_condition_always_true condition tm semantics h_inner tapes h_stops
    -- LHS: TM.eval is None because machine never halts
    -- RHS: PartENat.find.map is None because condition is always true (never false)
    ext result
    simp [TM.eval, PartENat.find, Part.mem_map_iff]
    constructor
    · intro h; obtain ⟨⟨t, h_t⟩, _⟩ := h; exfalso; exact h_no_halt t h_t
    · intro h; obtain ⟨⟨t, h_t⟩, _⟩ := h; exfalso;
      have h_true := h_stops t
      -- h_t : condition ... = false,  h_true : condition ... = true
      rw [h_t] at h_true
      sorry

-- Helper lemma for eval' version
lemma Routines.while.no_halt_if_condition_always_true' {k : ℕ} {Q Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  (condition : Γ → Bool)
  (tm : TM k.succ Q Γ)
  (tapes_seq : ℕ → (Fin k.succ → (Turing.Tape Γ)))
  (h_inner : ∀ i, tm.eval (tapes_seq i) = .some (tapes_seq i.succ))
  (h_always_true : ∀ i, condition ((tapes_seq i) 0).head) :
  ∀ t, ((Routines.while condition tm).configurations (tapes_seq 0) t).state ≠
       (Routines.while condition tm).stopState := by
  -- TODO: Similar proof as no_halt_if_condition_always_true but with explicit tape sequence
  sorry

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
  have h_transforms : ∀ i, tm.transforms (tapes_seq i) (tapes_seq i.succ) := by
    intro i
    exact TM.transforms_of_eval (h_inner i)
  by_cases h_stops : ∃ m, ¬condition ((tapes_seq m) 0).head
  · -- Case: the while loop terminates
    have h_while_transforms : (Routines.while condition tm).transforms (tapes_seq 0) (tapes_seq (Nat.find h_stops)) :=
      Routines.while.semantics condition tm tapes_seq h_transforms h_stops
    rw [TM.eval_of_transforms h_while_transforms]
    simp [PartENat.find, Part.map_some]
    sorry
  · -- Case: the while loop does not terminate
    push_neg at h_stops
    have h_no_halt := Routines.while.no_halt_if_condition_always_true' condition tm tapes_seq h_inner h_stops
    -- LHS: TM.eval is None because machine never halts
    -- RHS: PartENat.find.map is None because condition is always true (never false)
    ext result
    simp [TM.eval, PartENat.find, Part.mem_map_iff]
    constructor
    · intro h; obtain ⟨⟨t, h_t⟩, _⟩ := h; exfalso; exact h_no_halt t h_t
    · intro h; obtain ⟨⟨t, h_t⟩, _⟩ := h; exfalso;
      have h_true := h_stops t
      -- h_t : condition ... = false,  h_true : condition ... = true
      rw [h_t] at h_true
      sorry

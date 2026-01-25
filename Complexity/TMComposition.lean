import Mathlib
import Complexity.TuringMachine

inductive CombinedState (Q1 Q2 : Type*) where
  | first (q : Q1)
  | second (q : Q2)
  deriving DecidableEq

instance {Q1 Q2 : Type*} : Coe Q1 (CombinedState Q1 Q2) :=
  ⟨CombinedState.first⟩
instance {Q1 Q2 : Type*} : Coe Q2 (CombinedState Q1 Q2) :=
  ⟨CombinedState.second⟩

@[simp]
theorem coe_first_eq {Q1 Q2 : Type*} (q : Q1) :
    (↑q : CombinedState Q1 Q2) = CombinedState.first q := rfl

@[simp]
theorem coe_second_eq {Q1 Q2 : Type*} (q : Q2) :
    (↑q : CombinedState Q1 Q2) = CombinedState.second q := rfl

-- Combine two transitions: run σ₁ until reaching `final`, then switch to σ₂
-- TODO The start state of σ₂ should maybe really be equal to the final state
-- of σ₁. Now we have the situation where a configuration in state `final`
-- and one in state `start` are NOT equal, but mabye they should.
def transition_seq {k : Nat} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (σ₁ : Transition k Q1 Γ) (final : Q1) (start : Q2) (σ₂ : Transition k Q2 Γ) :
    Transition k (CombinedState Q1 Q2) Γ :=
  fun σ symbols_read =>
    match σ with
    | .first q1 =>
        if q1 = final then
          let ⟨q', rest⟩ := σ₂ start symbols_read
          (CombinedState.second q', rest)
        else
          let ⟨q', rest⟩ := σ₁ q1 symbols_read
          (CombinedState.first q', rest)
    | .second q2 =>
        let (q2', ops) := σ₂ q2 symbols_read
        (CombinedState.second q2', ops)

-- Turing Machine that runs two Turing Machines sequentially.
def TM.seq {k : ℕ} {Q1 Q2 Γ : Type*}
  [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
  (tm₁ : TM k Q1 Γ) (tm₂ : TM k Q2 Γ) : TM k (CombinedState Q1 Q2) Γ :=
  TM.mk
    (transition_seq tm₁.transition tm₁.stopState tm₂.startState tm₂.transition)
    (↑tm₁.startState)
    (if tm₂.startState = tm₂.stopState then
        ↑tm₁.stopState
      else
      (↑tm₂.stopState))

@[simp]
lemma TM.seq_startState {k : ℕ} {Q1 Q2 Γ : Type*}
  [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
  (tm₁ : TM k Q1 Γ) (tm₂ : TM k Q2 Γ) :
  (TM.seq tm₁ tm₂).startState = ↑tm₁.startState := rfl

@[simp]
lemma TM.seq_stopState_trivial {k : ℕ} {Q1 Q2 Γ : Type*}
  [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
  (tm₁ : TM k Q1 Γ) (tm₂ : TM k Q2 Γ) (h_tm₂_trivial : tm₂.startState = tm₂.stopState) :
  (TM.seq tm₁ tm₂).stopState = ↑tm₁.stopState := by
  simp [TM.seq, h_tm₂_trivial]

@[simp]
lemma TM.seq_stopState_nontrivial {k : ℕ} {Q1 Q2 Γ : Type*}
  [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
  (tm₁ : TM k Q1 Γ) (tm₂ : TM k Q2 Γ) (h_tm₂_trivial : tm₂.startState ≠ tm₂.stopState) :
  (TM.seq tm₁ tm₂).stopState = ↑tm₂.stopState := by
  simp [TM.seq, h_tm₂_trivial]

def to_combined_configuration {k : Nat} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [Coe Q1 Q2]
    (conf : Configuration k Q1 Γ) :
    Configuration k Q2 Γ :=
  { state := ↑conf.state, tapes := conf.tapes }

theorem to_combined_configuration_state {k : Nat} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [Coe Q1 Q2]
    (conf : Configuration k Q1 Γ) :
    (to_combined_configuration conf : Configuration k Q2 Γ).state = ↑conf.state := rfl

@[simp]
theorem to_combined_configuration_tapes {k : Nat} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [Coe Q1 Q2]
    (conf : Configuration k Q1 Γ) :
    (to_combined_configuration conf : Configuration k Q2 Γ).tapes = conf.tapes := rfl

@[simp]
theorem to_combined_configuration_state_first {k : Nat} {Q1 Q2 Γ : Type*}
    [Inhabited Γ]
    (conf : Configuration k Q1 Γ) :
    (to_combined_configuration conf : Configuration k (CombinedState Q1 Q2) Γ).state
    = CombinedState.first conf.state := rfl

@[simp]
theorem to_combined_configuration_state_second {k : Nat} {Q1 Q2 Γ : Type*}
    [Inhabited Γ]
    (conf : Configuration k Q2 Γ) :
    (to_combined_configuration conf : Configuration k (CombinedState Q1 Q2) Γ).state
    = CombinedState.second conf.state := rfl

-- Behaviour of Transtition.step with `transition_seq`.

-- Configuration transition in CombinedState.first matches σ₁ step, as long
-- as the state is not the final state.
theorem behaviour_first_part {k : ℕ} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (σ₁ : Transition k Q1 Γ) (final : Q1) (start : Q2) (σ₂ : Transition k Q2 Γ)
    (conf : Configuration k Q1 Γ)
    (h_not_final : conf.state ≠ final) :
    (transition_seq σ₁ final start σ₂).step (to_combined_configuration conf)
    = to_combined_configuration (σ₁.step conf) := by
  simp [h_not_final, transition_seq, Transition.step, to_combined_configuration]
  rfl

-- A configuration in state `final` performs steps in the same way
-- as `σ₂` would from `start`.
theorem step_from_final {k : ℕ} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (σ₁ : Transition k Q1 Γ) (final : Q1) (start : Q2) (σ₂ : Transition k Q2 Γ)
    (conf₁ : Configuration k Q1 Γ)
    (h_final : conf₁.state = final) :
    let conf₂ : Configuration k Q2 Γ := { state := start, tapes := conf₁.tapes }
    (transition_seq σ₁ final start σ₂).step (to_combined_configuration conf₁)
    = to_combined_configuration (σ₂.step conf₂) := by
  simp [h_final, transition_seq, Transition.step, to_combined_configuration]
  subst h_final
  rfl

-- Configuration transition in CombinedState.second matches σ₂ step.
theorem behaviour_second_part {k : ℕ} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (σ₁ : Transition k Q1 Γ) (final : Q1) (start : Q2) (σ₂ : Transition k Q2 Γ)
    (conf : Configuration k Q2 Γ) :
    (transition_seq σ₁ final start σ₂).step (to_combined_configuration conf)
    = to_combined_configuration (σ₂.step conf) := by
  rfl

theorem behaviour_n_steps_first_part {k : ℕ} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (σ₁ : Transition k Q1 Γ) (final : Q1) (start : Q2) (σ₂ : Transition k Q2 Γ)
    (conf : Configuration k Q1 Γ) (n : Nat)
    (no_final : ∀ n' < n, (σ₁.step^[n'] conf).state ≠ final) :
    (transition_seq σ₁ final start σ₂).step^[n] (to_combined_configuration conf)
    = to_combined_configuration (σ₁.step^[n] conf) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      (transition_seq σ₁ final start σ₂).step^[n + 1] (to_combined_configuration conf)
        = (transition_seq σ₁ final start σ₂).step
            ((transition_seq σ₁ final start σ₂).step^[n] (to_combined_configuration conf)) := by
        rw [Function.iterate_succ_apply']
      _ = (transition_seq σ₁ final start σ₂).step
            (to_combined_configuration (σ₁.step^[n] conf)) := by
        rw [ih (by intro n' lt; exact no_final n' (Nat.lt_succ_of_lt lt))]
      _ = to_combined_configuration (σ₁.step (σ₁.step^[n] conf)) := by
        apply behaviour_first_part
        exact no_final n (Nat.lt_succ_self n)
      _ = to_combined_configuration (σ₁.step^[n + 1] conf) := by
        simp [Function.iterate_succ_apply']

theorem n_steps_from_final {k : ℕ} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (σ₁ : Transition k Q1 Γ) (final : Q1) (start : Q2) (σ₂ : Transition k Q2 Γ)
    (conf₁ : Configuration k Q1 Γ) (n : Nat)
    (h_final : conf₁.state = final) :
    let conf₂ : Configuration k Q2 Γ := { state := start, tapes := conf₁.tapes }
    (transition_seq σ₁ final start σ₂).step^[n.succ] (to_combined_configuration conf₁)
    = to_combined_configuration (σ₂.step^[n.succ] conf₂) := by
  induction n with
  | zero => simp [h_final, step_from_final]
  | succ n ih =>
     intro conf₂
     let σ := transition_seq σ₁ final start σ₂
     calc
      σ.step^[n.succ.succ] (to_combined_configuration conf₁)
        = σ.step (σ.step^[n.succ] (to_combined_configuration conf₁)) := by
          rw [Function.iterate_succ_apply']
      _ = σ.step (to_combined_configuration (σ₂.step^[n.succ] conf₂)) := by rw [ih]
      _ = to_combined_configuration (σ₂.step^[n.succ.succ] conf₂) := by
        rw [Function.iterate_succ_apply]
        rw [behaviour_second_part]
        rw [← Function.iterate_succ_apply, ← Function.iterate_succ_apply' (f := σ₂.step) n.succ]


theorem behaviour_n_steps_second_part {k : ℕ} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (σ₁ : Transition k Q1 Γ) (final : Q1) (start : Q2) (σ₂ : Transition k Q2 Γ)
    (conf : Configuration k Q2 Γ) (n : Nat) :
    (transition_seq σ₁ final start σ₂).step^[n] (to_combined_configuration conf)
    = to_combined_configuration (σ₂.step^[n] conf) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih, behaviour_second_part, Function.iterate_succ_apply']

theorem behaviour_n_steps_crossing {k : ℕ} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (σ₁ : Transition k Q1 Γ) (final : Q1) (start : Q2) (σ₂ : Transition k Q2 Γ)
    (conf : Configuration k Q1 Γ) (n₁ n₂ : Nat)
    (no_final : ∀ n' < n₁, (σ₁.step^[n'] conf).state ≠ final)
    (h_final : (σ₁.step^[n₁] conf).state = final) :
    let conf₂ : Configuration k Q2 Γ := { state := start, tapes := (σ₁.step^[n₁] conf).tapes }
    (transition_seq σ₁ final start σ₂).step^[n₁ + n₂ + 1] (to_combined_configuration conf)
    = to_combined_configuration (σ₂.step^[n₂ + 1] conf₂) := by
  intro conf₂
  let σ := transition_seq σ₁ final start σ₂
  have part₁ : σ.step^[n₁] (to_combined_configuration conf)
                      = to_combined_configuration (σ₁.step^[n₁] conf) := by
    apply behaviour_n_steps_first_part; exact no_final
  calc
    σ.step^[n₁ + n₂.succ] (to_combined_configuration conf)
      = σ.step^[n₂.succ] (σ.step^[n₁] (to_combined_configuration conf)) := by
        rw [← Function.iterate_add_apply, Nat.add_comm]
    _ = σ.step^[n₂.succ] (to_combined_configuration (σ₁.step^[n₁] conf)) := by rw [part₁]
    _ = to_combined_configuration (σ₂.step^[n₂.succ] conf₂) := by
        apply n_steps_from_final; exact h_final

--- Main theorem that fully describes Transition.n_steps for the
--- combined transition function.
theorem behaviour_n_steps {k : ℕ} {Q1 Q2 Γ : Type*}
  [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
  (σ₁ : Transition k Q1 Γ) (final : Q1) (start : Q2) (σ₂ : Transition k Q2 Γ)
  (conf : Configuration k Q1 Γ) (n : Nat) :
  (transition_seq σ₁ final start σ₂).step^[n] (to_combined_configuration conf) =
    if h : ∃ m < n, (σ₁.step^[m] conf).state = final then
      let m := Nat.find h
      let conf₂ : Configuration k Q2 Γ := { state := start, tapes := (σ₁.step^[m] conf).tapes }
      to_combined_configuration (σ₂.step^[n - m] conf₂)
    else
      to_combined_configuration (σ₁.step^[n] conf) := by
  by_cases h : ∃ n' < n, (σ₁.step^[n'] conf).state = final
  · let m := Nat.find h
    have hm_spec : m < n ∧ (σ₁.step^[m] conf).state = final := Nat.find_spec h
    have hm_lt : m < n := hm_spec.1
    have h_final : (σ₁.step^[m] conf).state = final := hm_spec.2
    have no_final : ∀ n' < m, (σ₁.step^[n'] conf).state ≠ final := by
      intro n' hn' hfin'
      have : m ≤ n' := Nat.find_min' h ⟨Nat.lt_trans hn' hm_lt, hfin'⟩
      exact (not_le_of_gt hn') this
    have steps_decomp :
        m + (n - m - 1) + 1 = n := by
      calc
        m + (n - m - 1) + 1
            = m + ((n - m - 1) + 1) := by rfl
        _   = m + (n - m)           := by simp [Nat.succ_le_of_lt, Nat.sub_add_cancel, hm_lt]
        _   = n                     := by simp [Nat.add_sub_of_le (Nat.le_of_lt hm_lt)]
    -- Apply the "crossing" lemma at the first hitting time m
    have hcross :=
      behaviour_n_steps_crossing (σ₂:=σ₂) (n₁:=m) (n₂:=n - m - 1) (no_final:=no_final)
    simp_all [m, Nat.succ_le_of_lt]
  · -- Case 2: we *never* hit `final` before `n`
    have no_final : ∀ n' < n, (σ₁.step^[n'] conf).state ≠ final := by
      intro n' hn'
      exact fun hfin => h ⟨n', hn', hfin⟩
    simpa [h] using behaviour_n_steps_first_part σ₁ final start σ₂ conf n no_final

theorem behaviour_n_steps_for_seq {k : ℕ} {Q1 Q2 Γ : Type*}
  [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
  (tm₁ : TM k Q1 Γ) (tm₂ : TM k Q2 Γ)
  (tapes₀ : Fin k → Turing.Tape Γ)
  (n : Nat) :
  (TM.seq tm₁ tm₂).configurations tapes₀ n =
    if h : ∃ m < n, (tm₁.configurations tapes₀ m).state = tm₁.stopState then
      let m := Nat.find h
      to_combined_configuration (tm₂.configurations (tm₁.configurations tapes₀ m).tapes (n - m))
    else
      to_combined_configuration (tm₁.configurations tapes₀ n) := by
  unfold TM.seq
  have h_beh := behaviour_n_steps tm₁.transition tm₁.stopState tm₂.startState tm₂.transition
    (Configuration.mk tm₁.startState tapes₀) n
  simp only [to_combined_configuration] at h_beh
  exact h_beh

lemma TM.seq.if_tm_halts_then_find {k : ℕ} {Q1 Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q1]
  (tm₁ : TM k Q1 Γ)
  (tapes₀ tapes₁ : Fin k → Turing.Tape Γ)
  (t₁ t₂ : ℕ)
  (h_first_transforms : tm₁.transforms_in_exact_time tapes₀ tapes₁ t₁)
  (h : ∃ t' < t₂, (tm₁.configurations tapes₀ t').state = tm₁.stopState) :
  Nat.find h = t₁ := by
  have h_first_transforms_h : tm₁.transforms_in_exact_time
      tapes₀ (tm₁.configurations tapes₀ (Nat.find h)).tapes (Nat.find h) := by
    constructor
    · ext
      · rw [(Nat.find_spec h).2]
      · rfl
    · intro t' h_t'_lt h_stop
      apply Nat.find_min h h_t'_lt
      constructor
      · exact Nat.lt_trans h_t'_lt (Nat.find_spec h).1
      · exact h_stop
  have h_unique := TM.transforms_in_exact_time_unique tm₁ tapes₀ tapes₁
    (tm₁.configurations tapes₀ (Nat.find h)).tapes t₁ (Nat.find h)
    h_first_transforms h_first_transforms_h
  exact h_unique.1.symm

lemma TM.trivial_of_transforms_in_zero_time {k : ℕ} {Q Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ]
  (tm : TM k Q Γ)
  (tapes₀ tapes₁ : Fin k → Turing.Tape Γ)
  (h_transforms : tm.transforms_in_exact_time tapes₀ tapes₁ 0) :
  tm.startState = tm.stopState := by
  let h_stops := h_transforms.1
  simp only [configurations_zero, Configuration.mk.injEq] at h_stops
  exact h_stops.1

lemma TM.seq.halts {k : ℕ} {Q1 Q2 Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q1] [DecidableEq Q2]
  (tm₁ : TM k Q1 Γ) (tm₂ : TM k Q2 Γ)
  (tapes₀ tapes₁ tapes₂ : Fin k → Turing.Tape Γ)
  (t₁ t₂ : ℕ)
  (h_first_transforms : tm₁.transforms_in_exact_time tapes₀ tapes₁ t₁)
  (h_second_transforms : tm₂.transforms_in_exact_time tapes₁ tapes₂ t₂) :
  (tm₁.seq tm₂).configurations tapes₀ (t₁ + t₂) = ⟨(tm₁.seq tm₂).stopState, tapes₂⟩ := by
  rw [behaviour_n_steps_for_seq]
  by_cases h : ∃ m < t₁ + t₂, (tm₁.configurations tapes₀ m).state = tm₁.stopState
  · have h_t₁_eq_find : Nat.find h = t₁ :=
      TM.seq.if_tm_halts_then_find tm₁ tapes₀ tapes₁ t₁ (t₁ + t₂)  h_first_transforms h
    simp only [h, reduceDIte, h_t₁_eq_find, add_tsub_cancel_left]
    have h_t₂_nonzero : 0 < t₂ := by by_contra h_zero; linarith [Nat.find_spec h]
    have h_nontrivial : tm₂.startState ≠ tm₂.stopState := h_second_transforms.2 0 h_t₂_nonzero
    simp_all [h_first_transforms.1, h_second_transforms.1, to_combined_configuration, Coe.coe]
  · simp only [h, ↓reduceDIte]
    have h_t₂_eq_zero : t₂ = 0 := by
      by_contra h_t₂_nonzero
      push_neg at h
      specialize h t₁ (by omega)
      apply h
      simp only [h_first_transforms.1]
    rw [h_t₂_eq_zero] at h_second_transforms
    have h_t₂_trivial : tm₂.startState = tm₂.stopState :=
      TM.trivial_of_transforms_in_zero_time tm₂ tapes₁ tapes₂ h_second_transforms
    simp only [h_t₂_eq_zero, add_zero]
    simp_all only [add_zero, not_exists, not_and, h_first_transforms.1, seq_stopState_trivial]
    unfold TM.transforms_in_exact_time at h_second_transforms
    ext
    · simp
    · let h_second_trans := h_second_transforms.1
      simp only [configurations_zero, Configuration.mk.injEq] at h_second_trans
      simp [h_second_trans]

lemma TM.seq.does_not_halt_yet {k : ℕ} {Q1 Q2 Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q1] [DecidableEq Q2]
  (tm₁ : TM k Q1 Γ) (tm₂ : TM k Q2 Γ)
  (tapes₀ tapes₁ tapes₂ : Fin k → Turing.Tape Γ)
  (t₁ t₂ : ℕ)
  (h_first_transforms : tm₁.transforms_in_exact_time tapes₀ tapes₁ t₁)
  (h_second_transforms : tm₂.transforms_in_exact_time tapes₁ tapes₂ t₂) :
  ∀ t' < t₁ + t₂,
  ((tm₁.seq tm₂).configurations tapes₀ t').state ≠ (tm₁.seq tm₂).stopState := by
  intro t' h_lt
  rw [behaviour_n_steps_for_seq]
  by_cases h : ∃ m < t', (tm₁.configurations tapes₀ m).state = tm₁.stopState
  · have h_t₁_eq_find : Nat.find h = t₁ :=
      TM.seq.if_tm_halts_then_find tm₁ tapes₀ tapes₁ t₁ t'  h_first_transforms h
    simp only [h_t₁_eq_find]
    have h_t₂_nonzero : 0 < t₂ := by by_contra h_zero; linarith [Nat.find_spec h]
    have h_nontrivial : tm₂.startState ≠ tm₂.stopState := h_second_transforms.2 0 h_t₂_nonzero
    unfold TM.transforms_in_exact_time at h_second_transforms
    simpa [h, h_first_transforms.1, h_nontrivial] using h_second_transforms.2 (t' - t₁) (by omega)
  · simp only [h, ↓reduceDIte]
    unfold TM.transforms_in_exact_time at h_first_transforms
    simp_all only [not_exists, not_and, h_first_transforms.1]
    by_cases h_t₂_eq_zero : t₂ = 0
    · rw [h_t₂_eq_zero] at h_second_transforms
      have h_trivial : tm₂.startState = tm₂.stopState :=
        TM.trivial_of_transforms_in_zero_time tm₂ tapes₁ tapes₂ h_second_transforms
      rw [TM.seq_stopState_trivial tm₁ tm₂ h_trivial]
      rw [h_t₂_eq_zero] at h_lt
      simpa using h_first_transforms.2 t' h_lt
    · have h_nontrivial : tm₂.startState ≠ tm₂.stopState := h_second_transforms.2 0 (by omega)
      rw [TM.seq_stopState_nontrivial tm₁ tm₂ h_nontrivial]
      simp only [to_combined_configuration_state_first]
      intro h_states_eq
      injection h_states_eq

lemma TM.seq.inert_after_stop_of_inert_after_stop {k : ℕ} {Q1 Q2 Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q1] [DecidableEq Q2]
  (tm₁ : TM k Q1 Γ) (tm₂ : TM k Q2 Γ)
  (h_nontrivial : tm₂.startState ≠ tm₂.stopState)
  (h_inert_after_stop₂ : tm₂.inert_after_stop) :
  (tm₁.seq tm₂).inert_after_stop := by
  intro conf h_stop
  unfold TM.seq at h_stop ⊢
  simp only [h_nontrivial, ↓reduceIte] at h_stop ⊢
  cases h : conf.state with
  | first q1 =>
    rw [h] at h_stop
    cases h_stop
  | second q2 =>
    rw [h] at h_stop
    injection h_stop with h_q2_stop
    subst h_q2_stop
    let conf₂ : Configuration k Q2 Γ := Configuration.mk tm₂.stopState conf.tapes
    have h_combined: conf = to_combined_configuration conf₂ := by
      simp [to_combined_configuration, conf₂, Coe.coe, ←h]
    let σ := transition_seq tm₁.transition tm₁.stopState tm₂.startState tm₂.transition
    calc σ.step conf
        = σ.step (to_combined_configuration conf₂) := by rw [h_combined]
      _ = to_combined_configuration (tm₂.transition.step conf₂) := by apply behaviour_second_part
      _ = to_combined_configuration conf₂ := by rw [h_inert_after_stop₂ conf₂ rfl]
      _ = conf := h_combined.symm

--- Semantics of sequential composition of Turing Machines using the `TM.transforms` function.
@[simp]
theorem TM.seq.semantics {k : ℕ} {Q1 Q2 Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q1] [DecidableEq Q2]
  {tm₁ : TM k Q1 Γ} {tm₂ : TM k Q2 Γ}
  {tapes₀ tapes₁ tapes₂ : Fin k → Turing.Tape Γ}
  (h_first : tm₁.transforms tapes₀ tapes₁)
  (h_second : tm₂.transforms tapes₁ tapes₂) :
  (TM.seq tm₁ tm₂).transforms tapes₀ tapes₂ := by
  obtain ⟨t₁, h_first_transforms⟩ := h_first
  obtain ⟨t₂, h_second_transforms⟩ := h_second
  unfold TM.transforms TM.transforms_in_exact_time
  use t₁ + t₂
  constructor
  · exact TM.seq.halts
      tm₁ tm₂ tapes₀ tapes₁ tapes₂ t₁ t₂ h_first_transforms h_second_transforms
  · exact TM.seq.does_not_halt_yet
      tm₁ tm₂ tapes₀ tapes₁ tapes₂ t₁ t₂ h_first_transforms h_second_transforms

theorem TM.seq.transforms_iff_exists_and_transforms {k : ℕ} {Q1 Q2 Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q1] [DecidableEq Q2]
  {tm₁ : TM k Q1 Γ} {tm₂ : TM k Q2 Γ}
  {tapes₀ tapes₂ : Fin k → Turing.Tape Γ} :
  (TM.seq tm₁ tm₂).transforms tapes₀ tapes₂ ↔ ∃ tapes₁,
    tm₁.transforms tapes₀ tapes₁ ∧ tm₂.transforms tapes₁ tapes₂ := by
  constructor
  · intro h_seq_transforms
    obtain ⟨t, h_seq_transforms_halts, h_seq_transforms_min⟩ := h_seq_transforms
    rw [behaviour_n_steps_for_seq tm₁ tm₂ tapes₀ t] at h_seq_transforms_halts
    by_cases h_tm₁_stops : ∃ m < t, (tm₁.configurations tapes₀ m).state = tm₁.stopState
    · have h_tm₁_stops_at_all : ∃ m, (tm₁.configurations tapes₀ m).state = tm₁.stopState := by
        obtain ⟨m, _, h_stops⟩ := h_tm₁_stops
        exact ⟨m, h_stops⟩
      have h_find_same : Nat.find h_tm₁_stops = Nat.find h_tm₁_stops_at_all := by
        simp_all [Nat.find_eq_iff, Nat.find_spec h_tm₁_stops_at_all]
      simp [h_tm₁_stops] at h_seq_transforms_halts
      let t₁ := (Nat.find h_tm₁_stops_at_all)
      use (tm₁.configurations tapes₀ t₁).tapes
      constructor
      · exact ⟨t₁, TM.transforms_in_exact_time_of_find h_tm₁_stops_at_all⟩
      · use t - t₁
        subst t₁
        simp_all only [ne_eq, to_combined_configuration, Configuration.mk.injEq]
        constructor
        · simp only [TM.seq, Coe.coe] at *
          aesop
        · intro t' ht' h'
          let t'' := Nat.find h_tm₁_stops_at_all + t'
          convert h_seq_transforms_min t'' (by omega) _
          have h_behaviour : (tm₁.seq tm₂).configurations tapes₀ t'' =
             to_combined_configuration (tm₂.configurations (
                tm₁.configurations tapes₀ (Nat.find h_tm₁_stops_at_all)).tapes t') := by
            convert behaviour_n_steps_for_seq tm₁ tm₂ tapes₀ t'' using 1
            split_ifs with h <;> simp_all only [Nat.find_eq_iff, Nat.find_lt_iff, true_and,
              Nat.lt_find_iff, le_refl, and_false, not_false_eq_true, implies_true, and_true,
              not_exists, not_and]
            · have h_find_eq : Nat.find h = Nat.find h_tm₁_stops_at_all := by
                simp only [Nat.find_eq_iff, Nat.find_lt_iff]
                aesop_cat
              rw [ h_find_eq, Nat.add_sub_cancel_left ]
            · exact False.elim ( h _ ( Nat.lt_add_of_pos_right
                ( Nat.pos_of_ne_zero ( by rintro rfl; simp_all ) ) ) h_find_same )
          simp_all only [configurations, seq, to_combined_configuration_state_second,
            right_eq_ite_iff, reduceCtorEq, imp_false, ne_eq, t'']
          intro h
          simp_all
    · have h_tm₂_trivial: tm₂.startState = tm₂.stopState := by
        contrapose! h_seq_transforms_min;
        split_ifs at h_seq_transforms_halts
        simp_all [ to_combined_configuration ]
      have h_tm1_stop : (tm₁.seq tm₂).stopState = ↑tm₁.stopState :=
        TM.seq_stopState_trivial tm₁ tm₂ h_tm₂_trivial
      have h_tm1_config : (tm₁.configurations tapes₀ t).state = tm₁.stopState := by
        simp_all [ to_combined_configuration, Coe.coe ]
      have h_tapes_eq : (tm₁.configurations tapes₀ t).tapes = tapes₂ := by
        convert congr_arg (fun x => x.tapes) h_seq_transforms_halts using 1
        simp +decide [ h_tm₁_stops ]
      use tapes₂
      constructor
      · use t
        constructor <;> aesop
      · use 0
        constructor <;> simp [h_tm₂_trivial]
  · intro ⟨tapes₁, h_tm₁_transforms, h_tm₂_transforms⟩
    exact TM.seq.semantics h_tm₁_transforms h_tm₂_transforms

@[simp]
--- Semantics of sequential composition of Turing Machines using the `TM.eval` function.
theorem TM.seq.eval {k : ℕ} {Q1 Q2 Γ : Type*}
  [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q1] [DecidableEq Q2]
  {tm₁ : TM k Q1 Γ} {tm₂ : TM k Q2 Γ}
  {tapes₀ : Fin k → Turing.Tape Γ} :
  (TM.seq tm₁ tm₂).eval tapes₀ = (tm₁.eval tapes₀).bind tm₂.eval := by
  apply Part.ext'
  · rw [TM.eval_dom_iff_transforms]
    constructor
    · intro ⟨tapes₂, h_transforms⟩
      obtain ⟨tapes₁, h_tr₁, h_tr₂⟩ := TM.seq.transforms_iff_exists_and_transforms.mp h_transforms
      simp only [Part.bind_dom, eval_dom_iff_transforms]
      use ⟨tapes₁, h_tr₁⟩
      simp only [TM.eval_of_transforms h_tr₁, Part.get_some]
      use tapes₂
    · intro ⟨h_tm₁_dom, h_seq_dom⟩
      rw [TM.eval_dom_iff_transforms] at h_tm₁_dom
      obtain ⟨tapes₁, h_tm₁_trans⟩ := h_tm₁_dom
      simp only [TM.eval_of_transforms h_tm₁_trans, Part.get_some] at h_seq_dom
      obtain ⟨tapes₂, h_tm₂_trans⟩ := TM.eval_dom_iff_transforms.mp h_seq_dom
      exact ⟨tapes₂, TM.seq.semantics h_tm₁_trans h_tm₂_trans⟩
  · intro h_seq_dom h_bind_dom
    obtain ⟨tapes₂, h_seq_trans⟩ := TM.eval_dom_iff_transforms.mp h_seq_dom
    obtain ⟨tapes₁, h_tr₁, h_tr₂⟩ := TM.seq.transforms_iff_exists_and_transforms.mp h_seq_trans
    simp [TM.eval_of_transforms h_tr₁,
          TM.eval_of_transforms h_tr₂,
          TM.eval_of_transforms h_seq_trans]

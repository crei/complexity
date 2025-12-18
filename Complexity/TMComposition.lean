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

-- Combine two transitions: run σ₁ until reaching `final`, then switch to σ₂
-- TODO The start state of σ₂ should maybe really be equal to the final state
-- of σ₁. Now we have the situation where a configuration in state `final`
-- and one in state `start` are NOT equal, but mabye they should.
def do_after {k : Nat} {Q1 Q2 Γ : Type*}
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

def to_combined_configuration {k : Nat} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [Coe Q1 Q2]
    (conf : Configuration k Q1 Γ) :
    Configuration k Q2 Γ :=
  { state := ↑conf.state, tapes := conf.tapes }

-- Behaviour of Transtition.step with `do_after`.

-- Configuration transition in CombinedState.first matches σ₁ step, as long
-- as the state is not the final state.
theorem behaviour_first_part {k : ℕ} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (σ₁ : Transition k Q1 Γ) (final : Q1) (start : Q2) (σ₂ : Transition k Q2 Γ)
    (conf : Configuration k Q1 Γ)
    (h_not_final : conf.state ≠ final) :
    (do_after σ₁ final start σ₂).step (to_combined_configuration conf)
    = to_combined_configuration (σ₁.step conf) := by
  simp [h_not_final, do_after, Transition.step, to_combined_configuration]
  rfl

-- A configuration in state `final` performs steps in the same way
-- as `σ₂` would from `start`.
theorem step_from_final {k : ℕ} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (σ₁ : Transition k Q1 Γ) (final : Q1) (start : Q2) (σ₂ : Transition k Q2 Γ)
    (conf₁ : Configuration k Q1 Γ)
    (h_final : conf₁.state = final) :
    let conf₂ : Configuration k Q2 Γ := { state := start, tapes := conf₁.tapes }
    (do_after σ₁ final start σ₂).step (to_combined_configuration conf₁)
    = to_combined_configuration (σ₂.step conf₂) := by
  simp [h_final, do_after, Transition.step, to_combined_configuration]
  subst h_final
  rfl

-- Configuration transition in CombinedState.second matches σ₂ step.
theorem behaviour_second_part {k : ℕ} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (σ₁ : Transition k Q1 Γ) (final : Q1) (start : Q2) (σ₂ : Transition k Q2 Γ)
    (conf : Configuration k Q2 Γ) :
    (do_after σ₁ final start σ₂).step (to_combined_configuration conf)
    = to_combined_configuration (σ₂.step conf) := by
  rfl

theorem behaviour_n_steps_first_part {k : ℕ} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (σ₁ : Transition k Q1 Γ) (final : Q1) (start : Q2) (σ₂ : Transition k Q2 Γ)
    (conf : Configuration k Q1 Γ) (n : Nat)
    (no_final : ∀ n' < n, (σ₁.step^[n'] conf).state ≠ final) :
    (do_after σ₁ final start σ₂).step^[n] (to_combined_configuration conf)
    = to_combined_configuration (σ₁.step^[n] conf) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      (do_after σ₁ final start σ₂).step^[n + 1] (to_combined_configuration conf)
        = (do_after σ₁ final start σ₂).step
            ((do_after σ₁ final start σ₂).step^[n] (to_combined_configuration conf)) := by
        rw [Function.iterate_succ_apply']
      _ = (do_after σ₁ final start σ₂).step (to_combined_configuration (σ₁.step^[n] conf)) := by
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
    (do_after σ₁ final start σ₂).step^[n.succ] (to_combined_configuration conf₁)
    = to_combined_configuration (σ₂.step^[n.succ] conf₂) := by
  induction n with
  | zero => simp [h_final, step_from_final]
  | succ n ih =>
     intro conf₂
     let σ := do_after σ₁ final start σ₂
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
    (do_after σ₁ final start σ₂).step^[n] (to_combined_configuration conf)
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
    (do_after σ₁ final start σ₂).step^[n₁ + n₂ + 1] (to_combined_configuration conf)
    = to_combined_configuration (σ₂.step^[n₂ + 1] conf₂) := by
  intro conf₂
  let σ := do_after σ₁ final start σ₂
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
  (do_after σ₁ final start σ₂).step^[n] (to_combined_configuration conf) =
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

import Complexity.TuringMachine

import Mathlib

--- Extend a transition function to work with more tapes
--- (and do nothing on the new tapes).
def Transition.extend {k₁ k₂ : ℕ} (h_le : k₁ ≤ k₂) {Q} {Γ}
    (σ : Transition k₁ Q Γ) : Transition k₂ Q Γ :=
  fun state symbols =>
    let (next_state, ops) := σ state (fun i => symbols ⟨i, by omega⟩)
    (next_state, fun i => if h : i < k₁ then (ops ⟨i, h⟩) else (symbols i, none))

--- Extend a Turing machine to work with more tapes.
def TM.extend {k₁ k₂ : ℕ} (h_le : k₁ ≤ k₂) {Q} {Γ} [Inhabited Γ]
    (tm : TM k₁ Q Γ) : TM k₂ Q Γ :=
  TM.mk (tm.transition.extend h_le) tm.startState tm.stopState

--- Restrict a configuration to fewer tapes, i.e. remove the excess tapes.
def Configuration.restrict {k₁ k₂ : ℕ} (h_le : k₁ ≤ k₂) {Q Γ} [Inhabited Γ]
  (conf : Configuration k₂ Q Γ) : Configuration k₁ Q Γ :=
  ⟨conf.state, fun i => conf.tapes ⟨i, by omega⟩⟩

@[simp]
lemma Transition.extend_step_state {Q Γ} [Inhabited Γ]
  {k₁ k₂ : ℕ}
  {h_le : k₁ ≤ k₂}
  (σ : Transition k₁ Q Γ)
  (conf : Configuration k₂ Q Γ) :
  ((σ.extend h_le).step conf).state = (σ.step (conf.restrict h_le)).state := by
  unfold Transition.extend
  simp [Transition.step]
  rfl

@[simp]
lemma Transition.extend_step_tape_first {Q Γ} [Inhabited Γ]
  {k₁ k₂ : ℕ}
  {h_le : k₁ ≤ k₂}
  {σ : Transition k₁ Q Γ}
  {conf : Configuration k₂ Q Γ}
  {i : Fin k₂}
  (h_i_le : i < k₁) :
  ((σ.extend h_le).step conf).tapes i =
    (σ.step (conf.restrict h_le)).tapes ⟨i, by omega⟩ := by
  unfold Transition.extend
  simp [Transition.step, h_i_le]
  rfl

@[simp]
lemma Transition.extend_step_tape_second {Q Γ} [Inhabited Γ]
  {k₁ k₂ : ℕ}
  {h_le : k₁ ≤ k₂}
  {σ : Transition k₁ Q Γ}
  {conf : Configuration k₂ Q Γ}
  {i : Fin k₂}
  (h_i_le : ¬(i < k₁)) :
  ((σ.extend h_le).step conf).tapes i = conf.tapes ⟨i, by omega⟩ := by
  unfold Transition.extend
  simp [Transition.step, h_i_le]

@[simp]
lemma Transition.extend_step {Q Γ} [Inhabited Γ]
  {k₁ k₂ : ℕ}
  {h_le : k₁ ≤ k₂}
  {σ : Transition k₁ Q Γ}
  {conf : Configuration k₂ Q Γ} :
  (σ.extend h_le).step conf =
    ⟨
      (σ.step (conf.restrict h_le)).state,
      fun i => if h : i < k₁ then
        (σ.step (conf.restrict h_le)).tapes ⟨i, h⟩
      else
        conf.tapes i
    ⟩ := by
  ext1
  · simp
  · ext i
    by_cases h_lt : (i : ℕ) < k₁ <;>
    simp [h_lt]

@[simp]
lemma Transition.extend_step_iter {Q Γ} [Inhabited Γ]
  {k₁ k₂ : ℕ}
  {h_le : k₁ ≤ k₂}
  {σ : Transition k₁ Q Γ}
  {conf : Configuration k₂ Q Γ}
  (t : ℕ) :
  (σ.extend h_le).step^[t] conf = ⟨
    (σ.step^[t] (conf.restrict h_le)).state,
    fun i => if h : i < k₁ then
      (σ.step^[t] (conf.restrict h_le)).tapes ⟨i, h⟩
    else
      conf.tapes i
    ⟩ := by
  induction t generalizing conf with
  | zero => simp [Configuration.restrict]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    ext1
    · simp [Configuration.restrict]
    · ext i
      by_cases h_lt : (i : ℕ) < k₁ <;>
      simp [h_lt, Configuration.restrict]

@[simp]
lemma TM.extends_inert_after_stop {k₁ k₂ : ℕ} (h_le : k₁ ≤ k₂) {Q Γ} [Inhabited Γ]
  {tm : TM k₁ Q Γ}
  (h_inert : tm.inert_after_stop) :
  (tm.extend h_le).inert_after_stop := by
  intro conf h_is_stop
  have h_restricted_is_stop : (conf.restrict h_le).state = tm.stopState := by
    simpa [Configuration.restrict] using h_is_stop
  let h_restrict_inert := h_inert (conf.restrict h_le) h_restricted_is_stop
  ext1
  · simp [TM.extend, h_restrict_inert]; rfl
  · ext i
    by_cases h_lt : (i : ℕ) < k₁ <;>
    simp [TM.extend, h_lt, h_restrict_inert]
    rfl

@[simp]
lemma TM.extends_eval {k₁ k₂ : ℕ} (h_le : k₁ ≤ k₂)
  {Q Γ} [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  {tm : TM k₁ Q Γ}
  {tapes : Fin k₂ → Turing.Tape Γ} :
  (tm.extend h_le).eval tapes =
    (tm.eval (fun i => tapes ⟨i, by omega⟩)).map (fun tapes' =>
      fun i : Fin k₂ => if h : i < k₁ then tapes' ⟨i, h⟩ else tapes i) := by
  simp [TM.extend, TM.eval, TM.configurations]
  rfl

@[simp]
lemma TM.extends_transforms {k₁ k₂ : ℕ} {Q Γ} [Inhabited Γ] [DecidableEq Γ]
  {tm : TM k₁ Q Γ}
  {tapes₀ : Fin k₂ → Turing.Tape Γ}
  {tapes₁ : Fin k₁ → Turing.Tape Γ}
  (h_le : k₁ ≤ k₂)
  (h_transforms : tm.transforms (fun i => tapes₀ ⟨i, by omega⟩) tapes₁) :
  (tm.extend h_le).transforms tapes₀ (fun i => if h : i < k₁ then tapes₁ ⟨i, h⟩ else tapes₀ i) := by
  obtain ⟨t, h_transforms⟩ := h_transforms
  use t
  constructor
  · let h_transforms := h_transforms.1
    unfold TM.configurations at h_transforms
    simp [TM.configurations, TM.extend, h_transforms, Configuration.restrict]
  · intro t' h_t'_lt
    let h_transforms := h_transforms.2 t' h_t'_lt
    unfold TM.configurations at h_transforms
    simp [TM.configurations, TM.extend, h_transforms, Configuration.restrict]

import Complexity.TuringMachine

import Mathlib

--- Change the order of the tapes of a Turing machine.
--- tm.with_tapes [2, 4] is a Turing machine whose tape 2 is
--- the original machine's tape 0 and whose tape 4 is the original
--- machine's tape 1
def with_tapes {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
  -- TODO we also need that there are no duplicates in seq
  (tm : TM k.succ Q Γ) (seq : Vector ℕ k.succ) : TM (seq.toList.max (by simp)).succ Q Γ :=
  TM.mk (
    fun state symbols =>
      let (state', ops) := tm.transition state (fun i => symbols ⟨seq[i], by
            have : seq[i] ≤ seq.toList.max _ := List.le_max_of_mem (by simp); omega
          ⟩)
      (state', fun i => match Fin.find? (fun j => seq[j] = i) with
        | some t => ops t
        | none => (symbols i, none))
  ) tm.startState tm.stopState

-- TODO this is rather complicated, maybe easier to implement using swap operations?
-- tm.with_tapes [2, 4] =
--   (tm.extend 5).swap (0 2).swap(1 4)

def TM.swap_tapes {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
  (tm : TM k Q Γ) (i j : Fin k) : TM k Q Γ :=
  TM.mk (
    fun state symbols =>
      let (state', ops) := tm.transition state ((Vector.ofFn symbols).swap i j).get
      (state', ((Vector.ofFn ops).swap i j).get)
  ) tm.startState tm.stopState

-- Permute tapes according to a bijection
def TM.permute_tapes {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
  (tm : TM k Q Γ) (σ : Equiv.Perm (Fin k)) : TM k Q Γ :=
  TM.mk (
    fun state symbols =>
      let (state', ops) := tm.transition state (symbols ∘ σ)
      (state', ops ∘ σ.symm)
  ) tm.startState tm.stopState

-- Helper lemma: one step of permuted machine equals permuted step
lemma TM.permute_tapes.step {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
  (tm : TM k Q Γ) (σ : Equiv.Perm (Fin k)) (conf : Configuration k Q Γ) :
  (tm.permute_tapes σ).transition.step conf =
    let stepped := tm.transition.step { state := conf.state, tapes := conf.tapes ∘ σ }
    { state := stepped.state, tapes := stepped.tapes ∘ σ.symm } := by
  simp only [Transition.step, TM.permute_tapes, Function.comp]
  ext1
  · rfl
  · ext idx
    simp only [performTapeOps, Equiv.apply_symm_apply, Function.comp_apply]
    have : ((fun i => (conf.tapes i).head) ∘ σ) = (fun i => (conf.tapes (σ i)).head) := rfl
    rw [this]

-- General theorem: permuting tapes commutes with evaluation
lemma TM.permute_tapes.eval {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  (tm : TM k Q Γ) (σ : Equiv.Perm (Fin k)) (tapes : Fin k → Turing.Tape Γ) :
  (tm.permute_tapes σ).eval tapes =
    (tm.eval (tapes ∘ σ)).bind (fun tapes' => tapes' ∘ σ.symm) := by
  -- Key insight: configurations are related by the permutation
  have h_config : ∀ t,
    (tm.permute_tapes σ).configurations tapes t =
    let conf := tm.configurations (tapes ∘ σ) t
    { state := conf.state, tapes := conf.tapes ∘ σ.symm } := by
    intro t
    induction t with
    | zero =>
      ext
      · simp [TM.configurations, TM.permute_tapes]
      · simp [TM.configurations, TM.permute_tapes, Function.comp, Equiv.symm_apply_apply]
    | succ t ih =>
      simp only [TM.configurations, Function.iterate_succ_apply']
      have : (tm.permute_tapes σ).transition.step^[t] { state := (tm.permute_tapes σ).startState, tapes := tapes } =
             (let conf := tm.transition.step^[t] { state := tm.startState, tapes := tapes ∘ σ }; { state := conf.state, tapes := conf.tapes ∘ σ.symm }) := ih
      rw [this, TM.permute_tapes.step]
      ext
      · simp only []
      · funext idx
        simp [Function.comp, Equiv.symm_apply_apply]
  
  -- Now prove the main result
  ext result
  simp only [TM.eval, Part.mem_bind_iff]
  constructor
  · intro ⟨⟨t, h_stop⟩, h_result⟩
    simp at h_result h_stop
    use (tm.configurations (tapes ∘ σ) t).tapes
    constructor
    · use ⟨t, by rw [h_config] at h_stop; simp [TM.permute_tapes] at h_stop; exact h_stop⟩
      simp
    · rw [← h_result, h_config]
  · intro ⟨tapes_mid, ⟨⟨t, h_stop⟩, h_mid⟩, h_result⟩
    simp at h_mid h_result
    use ⟨t, by rw [h_config]; simp [TM.permute_tapes]; exact h_stop⟩
    simp
    rw [h_mid]
    exact h_result.symm

-- Swap is a special case of permutation  
lemma TM.swap_tapes.eval {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  {i j : Fin k} {tm : TM k Q Γ} {tapes : Fin k → Turing.Tape Γ} :
  (tm.swap_tapes i j).eval tapes =
    (tm.eval ((Vector.ofFn tapes).swap i j).get).bind
    fun tapes' => ((Vector.ofFn tapes').swap i j).get := by
  sorry

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
    let ⟨state', tapes'⟩ := tm.transition.step ⟨conf.state, conf.tapes ∘ σ⟩
    ⟨state', tapes' ∘ σ.symm⟩ := by
  simp only [Transition.step, TM.permute_tapes, Function.comp]
  ext <;>
  simp only [performTapeOps, Equiv.apply_symm_apply, Function.comp_apply] <;>
  rfl

lemma TM.permute_tapes.configurations {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
  (tm : TM k Q Γ) (σ : Equiv.Perm (Fin k)) (tapes : Fin k → Turing.Tape Γ) (t : ℕ) :
  (tm.permute_tapes σ).configurations tapes t =
    let ⟨state', tapes'⟩ := tm.configurations (tapes ∘ σ) t; ⟨state', tapes' ∘ σ.symm ⟩ := by
  induction t with
  | zero => ext <;> simp [TM.configurations, TM.permute_tapes]
  | succ t ih =>
    unfold TM.configurations at ih ⊢
    simp only [Function.iterate_succ_apply']
    rw [ih, TM.permute_tapes.step]
    simp [Transition.step]

lemma TM.permute_tapes.step_iter {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
  (tm : TM k Q Γ) (σ : Equiv.Perm (Fin k)) (tapes : Fin k → Turing.Tape Γ) (t : ℕ) :
  (tm.permute_tapes σ).configurations tapes t =
    let ⟨state', tapes'⟩ := tm.configurations (tapes ∘ σ) t; ⟨state', tapes' ∘ σ.symm ⟩ := by
  induction t with
  | zero => ext <;> simp [TM.configurations, TM.permute_tapes]
  | succ t ih =>
    unfold TM.configurations at ih ⊢
    simp only [Function.iterate_succ_apply']
    rw [ih, TM.permute_tapes.step]
    simp [Transition.step]

-- General theorem: permuting tapes commutes with evaluation
theorem TM.permute_tapes.eval {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  (tm : TM k Q Γ) (σ : Equiv.Perm (Fin k)) (tapes : Fin k → Turing.Tape Γ) :
  (tm.permute_tapes σ).eval tapes =
    (tm.eval (tapes ∘ σ)).bind (fun tapes' => tapes' ∘ σ.symm) := by
  unfold TM.eval
  simp only [Part.coe_some, Part.bind_some_eq_map]
  simp only [TM.permute_tapes.configurations]
  simp [TM.permute_tapes]
  rfl

-- Swap is a special case of permutation
lemma TM.swap_tapes.eval {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  {i j : Fin k} {tm : TM k Q Γ} {tapes : Fin k → Turing.Tape Γ} :
  (tm.swap_tapes i j).eval tapes =
    (tm.eval ((Vector.ofFn tapes).swap i j).get).bind
    fun tapes' => ((Vector.ofFn tapes').swap i j).get := by
  sorry

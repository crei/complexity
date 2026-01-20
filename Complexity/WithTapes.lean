import Complexity.TuringMachine
import Complexity.TapeExtension

import Mathlib

--- Permute tapes according to a bijection
def TM.permute_tapes {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
  (tm : TM k Q Γ) (σ : Equiv.Perm (Fin k)) : TM k Q Γ :=
  TM.mk (
    fun state symbols =>
      let (state', ops) := tm.transition state (symbols ∘ σ)
      (state', ops ∘ σ.symm)
  ) tm.startState tm.stopState

--- Change the order of the tapes of a Turing machine.
--- Example: For a 2-tape Turing machine tm,
--- tm.with_tapes [2, 4] is a 5-tape Turing machine whose tape 2 is
--- the original machine's tape 0 and whose tape 4 is the original
--- machine's tape 1
--- Note that `seq` should not have repetitions.
--- TODO maybe `seq` should be an injection from Fin k₁ to Fin k₂, then it would be `#v[2, 4].get`.
def TM.with_tapes {k₁ k₂ : ℕ} {h_le : k₁ ≤ k₂} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Γ]
  (tm : TM k₁ Q Γ) (seq : Vector (Fin k₂) k₁) : TM k₂ Q Γ :=
  (seq.mapFinIdx fun i t _ => ((⟨i, by omega⟩ : Fin k₂), t)
    ).foldl (fun tm (a, b) => tm.permute_tapes (Equiv.swap a b)) (tm.extend h_le)

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
@[simp]
theorem TM.permute_tapes.eval {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  (tm : TM k Q Γ) (σ : Equiv.Perm (Fin k)) (tapes : Fin k → Turing.Tape Γ) :
  (tm.permute_tapes σ).eval tapes =
    (tm.eval (tapes ∘ σ)).map (fun tapes' => tapes' ∘ σ.symm) := by
  unfold TM.eval
  simp only [TM.permute_tapes.configurations]
  simp [TM.permute_tapes]
  rfl

theorem TM.with_tapes.eval_1
  {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  {j : Fin k.succ}
  (tm : TM 1 Q Γ)
  (tapes : Fin k.succ → Turing.Tape Γ) :
  (tm.with_tapes #v[j] (h_le := by omega)).eval tapes =
    (tm.eval (fun _ => tapes j)).map
    (fun tapes' => fun t => if t = j then tapes' 0 else tapes t) := by
  unfold TM.with_tapes
  simp




  sorry

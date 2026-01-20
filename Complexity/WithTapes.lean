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

lemma TM.swap_tapes.eval {k : ℕ} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Γ] [DecidableEq Q]
  {i j : Fin k} {tm : TM k Q Γ} {tapes : Fin k → Turing.Tape Γ} :
  (tm.swap_tapes i j).eval tapes =
    (tm.eval ((Vector.ofFn tapes).swap i j).get).bind
    fun tapes => ((Vector.ofFn tapes).swap i j).get := by
  simp [TM.swap_tapes]
  let tapes' := ((Vector.ofFn tapes).swap i j).get
  have : ((Vector.ofFn tapes).swap i j).get = tapes' := rfl
  rw [this]

  ext1
  · simp_all
  · smpp_all


  sorry
  tm := by

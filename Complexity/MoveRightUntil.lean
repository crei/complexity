import Complexity.TuringMachine
import Complexity.Dyadic
import Complexity.TapeLemmas
import Complexity.AbstractTape

import Mathlib

--- Returns a 1-tape Turing machine that moves its head
--- to the right until a condition is met.
def move_right_until {Γ} [Inhabited Γ] (stop_condition : Γ → Bool) :
  TM 1 (Fin 2) Γ :=
  let σ := fun state symbols =>
    match state with
    | 0 => if stop_condition (symbols 0) then
        (1, (symbols · , none))
      else
        (0, (symbols ·, some .right))
    | 1 => (1, (symbols ·, none))
  TM.mk σ 0 1

lemma move_right_until.inert_after_stop {Γ} [Inhabited Γ]
  (stop_condition : Γ → Bool) :
  (move_right_until stop_condition).inert_after_stop := by
  intro conf h_is_stopped
  ext <;> simp_all [Transition.step, performTapeOps, move_right_until]

theorem move_right_until.semantics {Γ} [Inhabited Γ] [DecidableEq Γ]
  (tape : Turing.Tape Γ)
  (stop_condition : Γ → Bool)
  (h_stop : ∃ n, stop_condition (tape.right₀.nth n)) :
  (move_right_until stop_condition).transforms
    (fun _ => tape)
    (fun _ => tape.move_int (Nat.find h_stop)) := by
  let n := Nat.find h_stop
  let tm := move_right_until stop_condition
  have h_conf (t : ℕ) : t ≤ n → tm.transition.step^[t] ⟨tm.startState, (fun _ => tape)⟩ =
    ⟨0, (fun _ => (Turing.Tape.move .right)^[t] tape)⟩ := by
    intro h_lt
    induction t with
    | zero => rfl
    | succ t ih =>
      have h_not_stop : ¬ stop_condition (tape.nth t) := by
        simpa [Turing.Tape.right₀_nth] using Nat.find_min h_stop (m := t) (by omega)
      unfold TM.configurations at ih
      simp only [Function.iterate_succ_apply']
      rw [ih (by omega)]
      simp [tm, move_right_until, Transition.step, h_not_stop]
  have h_conf_n : tm.configurations (fun _ => tape) (n + 1) =
    ⟨1, (fun _ => (Turing.Tape.move .right)^[n] tape)⟩ := by
    have h_is_stop : stop_condition (tape.nth n) := by
      simpa [Turing.Tape.right₀_nth, n] using Nat.find_spec h_stop
    simp only [TM.configurations, Function.iterate_succ_apply', h_conf n (by omega)]
    simp only [Transition.step, move_right_until, Turing.Tape.move_right_n_head,
      h_is_stop, ↓reduceIte, perform_no_move, Configuration.mk.injEq, tm]
    rw [move_right_iter_eq_move_int, write_eq_write_at, move_int_write_at]
    simp
  have h_stops : (tm.configurations (fun _ => tape) (n + 1)).state = tm.stopState := by
    rw [h_conf_n]; rfl
  have h_tapes : (tm.configurations (fun _ => tape) (n + 1)).tapes =
      fun _ => tape.move_int (Nat.find h_stop) := by
    rw [h_conf_n]; rfl
  simpa [h_tapes] using TM.transforms_of_inert tm _ (n + 1)
    (move_right_until.inert_after_stop stop_condition) h_stops

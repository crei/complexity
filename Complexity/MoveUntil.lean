import Complexity.TuringMachine
import Complexity.Dyadic
import Complexity.TapeLemmas
import Complexity.AbstractTape

import Mathlib

def Routines.move {Γ} [Inhabited Γ]
  (dir : Turing.Dir) :
  TM 1 (Fin 2) Γ :=
  let σ := fun state symbols =>
    match state with
    | 0 => (0, (symbols ·, some dir))
    | 1 => (1, (symbols ·, none))
  TM.mk σ 0 1

lemma Routines.move.inert_after_stop {Γ} [Inhabited Γ]
  (dir : Turing.Dir) :
  (Routines.move (Γ := Γ) dir).inert_after_stop := by
  intro conf h_is_stopped
  ext <;> simp_all [Transition.step, performTapeOps, Routines.move]

lemma Routines.move.semantics {Γ} [Inhabited Γ] [DecidableEq Γ]
  (tape : Turing.Tape Γ)
  (dir : Turing.Dir) :
  (Routines.move dir).transforms (fun _ => tape) (fun _ => Turing.Tape.move dir tape) := by
  let tm := Routines.move (Γ := Γ) dir
  refine TM.transforms_of_inert tm _ _ (move.inert_after_stop dir) ?_
  sorry

--- Returns a 1-tape Turing machine that moves its head
--- in a certain direction until a condition is met.
def move_until {Γ} [Inhabited Γ]
  (dir : Turing.Dir)
  (stop_condition : Γ → Bool) :
  TM 1 (Fin 2) Γ :=
  let σ := fun state symbols =>
    match state with
    | 0 => if stop_condition (symbols 0) then
        (1, (symbols · , none))
      else
        (0, (symbols ·, some dir))
    | 1 => (1, (symbols ·, none))
  TM.mk σ 0 1

lemma move_until.inert_after_stop {Γ} [Inhabited Γ]
  (dir : Turing.Dir)
  (stop_condition : Γ → Bool) :
  (move_until dir stop_condition).inert_after_stop := by
  intro conf h_is_stopped
  ext <;> simp_all [Transition.step, performTapeOps, move_until]

theorem move_until.semantics {Γ} [Inhabited Γ] [DecidableEq Γ]
  (tape : Turing.Tape Γ)
  (dir : Turing.Dir)
  (stop_condition : Γ → Bool)
  (h_stop : ∃ n, stop_condition ((match dir with
    | .right => tape.right₀.nth
    | .left => tape.left₀.nth) n)) :
  (move_until dir stop_condition).transforms
    (fun _ => tape)
    (fun _ => tape.move_int (Nat.find h_stop)) := by
  let n := Nat.find h_stop
  let tm := move_until dir stop_condition
  let tape_nth := match dir with
    | .right => tape.right₀.nth
    | .left => tape.left₀.nth
  have h_conf (t : ℕ) : t ≤ n → tm.transition.step^[t] ⟨tm.startState, (fun _ => tape)⟩ =
    ⟨0, (fun _ => (Turing.Tape.move dir)^[t] tape)⟩ := by
    intro h_lt
    induction t with
    | zero => rfl
    | succ t ih =>
      have h_not_stop : ¬ stop_condition (tape_nth t) := by
        simpa [Turing.Tape.right₀_nth] using Nat.find_min h_stop (m := t) (by omega)
      unfold TM.configurations at ih
      simp only [Function.iterate_succ_apply']
      rw [ih (by omega)]
      simp [tm, move_until, Transition.step, h_not_stop]
  have h_conf_n : tm.configurations (fun _ => tape) (n + 1) =
    ⟨1, (fun _ => (Turing.Tape.move dir)^[n] tape)⟩ := by
    have h_is_stop : stop_condition (tape_nth n) := by
      simpa [Turing.Tape.right₀_nth, n] using Nat.find_spec h_stop
    simp only [TM.configurations, Function.iterate_succ_apply', h_conf n (by omega)]
    simp only [Transition.step, move_until, Turing.Tape.move_right_n_head,
      h_is_stop, ↓reduceIte, perform_no_move, Configuration.mk.injEq, tm]
    rw [move_right_iter_eq_move_int, write_eq_write_at, move_int_write_at]
    simp
  have h_stops : (tm.configurations (fun _ => tape) (n + 1)).state = tm.stopState := by
    rw [h_conf_n]; rfl
  have h_tapes : (tm.configurations (fun _ => tape) (n + 1)).tapes =
      fun _ => tape.move_int (Nat.find h_stop) := by
    rw [h_conf_n]; rfl
  simpa [h_tapes] using TM.transforms_of_inert tm _ (n + 1)
    (move_until.inert_after_stop dir stop_condition) h_stops

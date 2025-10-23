import Complexity.TuringMachine
import Complexity.Dyadic

import Mathlib

--- Returns a transition function that starts in state 0,
--- moves the head on tape `tape` right until `stop_condition` is true on
--- the symbol read on the tape. Stays at that symbol and stops in state 1.
def move_right_until {k : ℕ}
  (tape : Fin k)
  (stop_condition : BlankChar -> Bool) : Transition k (Fin 2) BlankChar :=
  fun state symbols =>
    match state with
    | 0 => if stop_condition (symbols tape) then
        (1, fun i => (symbols i, none))
      else
        (0, fun i => (symbols i, if i = tape then some .right else none))
    | st => (st, fun i => (symbols i, none))

lemma move_right_step {k : ℕ}
  (tape : Fin k)
  (stop_condition : BlankChar -> Bool)
  (conf : Configuration k (Fin 2) BlankChar)
  (h_state : conf.state = 0)
  (h_head : ¬ stop_condition (conf.tapes tape).head) :
  ((move_right_until tape stop_condition).step conf).state = 0 ∧
  -- TODO and other tapes are unaffected.
  ((move_right_until tape stop_condition).step conf).tapes tape
    = (conf.tapes tape).move .right := by
  simp [Transition.step, move_right_until, h_state, h_head, Turing.Tape.move]

lemma move_right_multi {k : ℕ}
  (tape : Fin k)
  (stop_condition : BlankChar -> Bool)
  (conf : Configuration k (Fin 2) BlankChar)
  (h_state : conf.state = 0)
  (remaining_length : ℕ)
  (h_remaining : ∀ j < remaining_length, ¬ stop_condition ((conf.tapes tape).nth j)) :
  -- TODO do this without defining conf'?
  let conf' := (move_right_until tape stop_condition).n_steps conf remaining_length
  conf'.state = 0 ∧
  conf'.tapes tape = (Turing.Tape.move .right)^[remaining_length] (conf.tapes tape) := by
  induction remaining_length with
  | zero => exact ⟨h_state, rfl⟩
  | succ m ih =>
    unfold Transition.n_steps
    let conf_pre := (move_right_until tape stop_condition).n_steps conf m
    have ih_cond : ∀ j < m, ¬ stop_condition ((conf.tapes tape).nth j) := by
      intro j hj
      apply h_remaining
      omega
    have pre_state : conf_pre.state = 0 := (ih ih_cond).left
    have pre_tape : conf_pre.tapes tape = (Turing.Tape.move .right)^[m] (conf.tapes tape) :=
      (ih ih_cond).right
    intro conf'
    have h: conf' = (move_right_until tape stop_condition).step conf_pre := rfl
    have h_head : ¬ stop_condition (conf_pre.tapes tape).head := by
      rw [pre_tape]
      simp [Turing.Tape.move_right_n_head, h_remaining m (by simp)]
    simp [h, pre_tape, move_right_step _ _ _ pre_state h_head, Function.iterate_succ]
    rw [Function.Commute.self_iterate (Turing.Tape.move .right) m]

lemma move_right_last_step {k : ℕ}
  (tape : Fin k)
  (stop_condition : BlankChar -> Bool)
  (conf : Configuration k (Fin 2) BlankChar)
  (hstate : conf.state = 0)
  (h_head : stop_condition (conf.tapes tape).head) :
  ((move_right_until tape stop_condition).step conf).state = 1 ∧
  ((move_right_until tape stop_condition).step conf).tapes tape = conf.tapes tape := by
  simp [Transition.step, move_right_until, hstate, h_head]

lemma move_right_until_steps {k : ℕ}
  (tape : Fin k)
  (stop_condition : BlankChar -> Bool)
  (conf : Configuration k (Fin 2) BlankChar)
  (h_state : conf.state = 0)
  (remaining_length : ℕ) -- TODO use "find"
  (h_remaining : ∀ j < remaining_length, ¬ stop_condition ((conf.tapes tape).nth j))
  (h_stop : stop_condition ((conf.tapes tape).nth remaining_length)) :
  let conf' := (move_right_until tape stop_condition).n_steps conf (remaining_length + 1)
  conf'.state = 1 ∧
  conf'.tapes tape = (Turing.Tape.move .right)^[remaining_length] (conf.tapes tape) := by
  let conf_pre := (move_right_until tape stop_condition).n_steps conf remaining_length
  have pre_state : conf_pre.state = 0 := by
    simp [move_right_multi _ _ conf h_state remaining_length h_remaining, conf_pre]
  have pre_tape : conf_pre.tapes tape =
    (Turing.Tape.move .right)^[remaining_length] (conf.tapes tape) :=
    (move_right_multi _ _ conf h_state remaining_length h_remaining).right
  rw [Transition.n_steps]
  intro conf'
  have h_conf_pre : conf' = (move_right_until tape stop_condition).step conf_pre := rfl
  have h_head : stop_condition (conf_pre.tapes tape).head := by
    simp [Turing.Tape.move_right_n_head, pre_tape, h_stop]
  simp [move_right_last_step _ _ conf_pre pre_state h_head, conf', pre_tape, h_conf_pre]

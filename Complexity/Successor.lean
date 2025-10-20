import Complexity.TuringMachine
import Complexity.Dyadic

import Mathlib

-- Custom Char type with ' ' as default (instead of 'A')
def BlankChar := Char

instance : Inhabited BlankChar where
  default := ' '

instance : DecidableEq BlankChar := inferInstanceAs (DecidableEq Char)

-- Coercion from Char to BlankChar
instance : Coe Char BlankChar where
  coe c := c

def succ_transition : Transition 1 (Fin 4) BlankChar :=
  fun state symbols =>
    match state with
    -- we still need to add one (initially or due to carry)
    | 0 => match symbols 0 with
      | ' ' => (2, fun _ => ('1', some .right))
      | '1' => (1, fun _ => ('2', some .right))
      | '2' => (0, fun _ => ('1', some .right))
      | c => (0, fun _ => (c, some .right)) -- should not happen
    -- nothing to add, only copy input to output
    | 1 => match symbols 0 with
      | ' ' => (2, fun i => (symbols i, none))
      | _ => (1, fun i => (symbols i, some .right))
    -- finished
    | st => (st, fun i => (symbols i, none))

-- A Turing machine that computes the successor of a
-- reversely encoded dyadic number
def succ_tm : TM 1 (Fin 4) BlankChar := {
  transition := succ_transition
  startState := 0
  stopState := 2
}

theorem listblank_cons_default_to_empty {Γ} [Inhabited Γ] :
  (Turing.ListBlank.mk [default] : Turing.ListBlank Γ) = Turing.ListBlank.mk [] := by
  have h2 : Turing.BlankRel ([default] : List Γ) [] := by
    unfold Turing.BlankRel; right; use 1; simp
  apply Quotient.sound
  exact h2

theorem listblank_all_blank_is_empty {Γ} [Inhabited Γ]
  (list : List Γ)
  (all_empty : ∀ i, list.getI i = default) :
  Turing.ListBlank.mk list = Turing.ListBlank.mk [] := by
  apply Turing.ListBlank.ext
  simp [all_empty]

theorem listblank_is_empty_all_blank {Γ} [Inhabited Γ]
  (list : Turing.ListBlank Γ)
  (is_empty : list = Turing.ListBlank.mk []) :
  ∀ i, list.nth i = default := by
  intro i
  subst is_empty
  simp_all only [List.getI_nil, Turing.ListBlank.nth_mk]

lemma cons_is_empty {Γ} [Inhabited Γ]
  (c : Γ)
  (list : Turing.ListBlank Γ)
  (is_empty : Turing.ListBlank.cons c list = Turing.ListBlank.mk []) :
  c = default := by
  simpa using listblank_is_empty_all_blank (Turing.ListBlank.cons c list ) is_empty 0

lemma copy_step
  (conf : Configuration 1 (Fin 4) BlankChar)
  (h_state : conf.state = 1)
  (h_head : (conf.tapes 0).head ≠ ' ') :
  (succ_transition.step conf).state = 1 ∧
  (succ_transition.step conf).tapes 0 = (conf.tapes 0).move .right := by
  simp [Transition.step, succ_transition, h_state, Turing.Tape.move]

lemma copy_steps_multi
  (conf : Configuration 1 (Fin 4) BlankChar)
  (h_state : conf.state = 1)
  (remaining_length : ℕ)
  (h_remaining : ∀ j < remaining_length, (conf.tapes 0).nth j ≠ ' ') :
  -- TODO do this without defining conf'?
  let conf' := succ_transition.n_steps conf remaining_length
  conf'.state = 1 ∧
  conf'.tapes 0 = (Turing.Tape.move .right)^[remaining_length] (conf.tapes 0) := by
  induction remaining_length with
  | zero => exact ⟨h_state, rfl⟩
  | succ m ih =>
    unfold Transition.n_steps
    let conf_pre := succ_transition.n_steps conf m
    have ih_cond : ∀ j < m, (conf.tapes 0).nth j ≠ ' ' := by
      intro j hj
      apply h_remaining
      omega
    have pre_state : conf_pre.state = 1 := (ih ih_cond).left
    have pre_tape : conf_pre.tapes 0 = (Turing.Tape.move .right)^[m] (conf.tapes 0) :=
      (ih ih_cond).right
    intro conf'
    have h: conf' = succ_transition.step conf_pre := rfl
    have h_head : (conf_pre.tapes 0).head ≠ ' ' := by
      calc (conf_pre.tapes 0).head
         = (conf.tapes 0).nth m := by simp [Turing.Tape.move_right_n_head, pre_tape]
        _ ≠ ' ' := h_remaining m (by simp)
    simp [h, pre_tape, copy_step conf_pre pre_state h_head, Function.iterate_succ]
    rw [Function.Commute.self_iterate (Turing.Tape.move .right) m]

lemma copy_last_step
  (conf : Configuration 1 (Fin 4) BlankChar)
  (hstate : conf.state = 1)
  (h_head : (conf.tapes 0).head = ' ') :
  (succ_transition.step conf).state = 2 ∧
  (succ_transition.step conf).tapes 0 = conf.tapes 0 := by
  simp [Transition.step, succ_transition, hstate, h_head]

lemma copy_steps
  (conf : Configuration 1 (Fin 4) BlankChar)
  (h_state : conf.state = 1)
  (remaining_length : ℕ) -- TODO use "find"
  (h_remaining : ∀ j < remaining_length, (conf.tapes 0).nth j ≠ ' ')
  (h_blank : (conf.tapes 0).nth remaining_length = ' ') :
  let conf' := succ_transition.n_steps conf (remaining_length + 1)
  conf'.state = 2 ∧
  conf'.tapes 0 = (Turing.Tape.move .right)^[remaining_length] (conf.tapes 0) := by
  let conf_pre := succ_transition.n_steps conf remaining_length
  have pre_state : conf_pre.state = 1 := by
    simp [copy_steps_multi conf h_state remaining_length h_remaining, conf_pre]
  have pre_tape : conf_pre.tapes 0 =
    (Turing.Tape.move .right)^[remaining_length] (conf.tapes 0) :=
    (copy_steps_multi conf h_state remaining_length h_remaining).right
  rw [Transition.n_steps]
  intro conf'
  have h_conf_pre : conf' = succ_transition.step conf_pre := rfl
  have h_head : (conf_pre.tapes 0).head = ' ' := by
    simp [Turing.Tape.move_right_n_head, pre_tape, h_blank]
  simp [copy_last_step conf_pre pre_state h_head, conf', pre_tape, h_conf_pre]


-- TODO we also need a lemma that models the principle of addition that is
-- used by the machine.

-- lemma copies_in_state_one {σ : Configuration 1 (Fin 4) Char}
--   (hstate : σ.state = 1) :
--   let inputTape := σ.tapes 0
--   let remainingInput := inputTape.head :: inputTape.right
--   let (finalConf, output) := succ_tm.run_for_steps σ (remainingInput.length + 1)
--   finalConf.state = succ_tm.acceptState ∧ output = remainingInput := by
--   intros inputTape remainingInput
--   simp [remainingInput]
--   induction inputTape.right generalizing σ with
--   | nil =>
--     simp [TM.run_for_steps, succ_tm, hstate, TM.step]

-- lemma copies_in_state_one_of_dyadic
--   {σ : Configuration 1 (Fin 4) Char}
--   (hstate : σ.state = 1)
--   (hd : ∀ c ∈ ((σ.tapes 0).head :: (σ.tapes 0).right), c = '1' ∨ c = '2') :
--   let inputTape := σ.tapes 0
--   let remainingInput := inputTape.head :: inputTape.right
--   let (finalConf, output) := succ_tm.run_for_steps σ (remainingInput.length + 1)
--   finalConf.state = succ_tm.acceptState ∧ output = remainingInput := by
--   intro inputTape remainingInput
--   have hhead : inputTape.head = '0' ∨ inputTape.head = '1' := by
--     simp [hd, inputTape, hd]

--     simp [List.mem_cons, hd]
--   -- We induct on the structure of the "right" list, keeping σ generalized.
--   induction inputTape.right generalizing σ with
--   | nil =>
--     -- Unfold the run (n+1) convention in your `TM.run_for_steps`
--     -- and the one-step behavior of succ_tm at state 1.
--     -- The `simp` below picks the correct branch using `hstate` and `hhead`.
--     rcases hhead with h0 | h1
--     · simp [remainingInput, TM.run_for_steps, succ_tm, hstate, TM.step, h0]
--     · simp [remainingInput, TM.run_for_steps, succ_tm, hstate, TM.step, h1]
--   | cons c cs ih =>
--     -- Inductive case: right = c :: cs
--     -- We know the head and c are 0/1 by hd; we split on head and use simp.
--     have hhead : inputTape.head = '0' ∨ inputTape.head = '1' := by
--       exact hd inputTape.head (by simp)
--     rcases hhead with h0 | h1
--     · -- head = '0': one step emits '0' and moves right; then apply IH
--       -- After that first copy step, we remain in state 1; the remainingInput shrinks to c::cs.
--       -- Your `run_for_steps` does the n steps first, then one step; we adjust
--       -- lengths accordingly.
--       simp [remainingInput, TM.run_for_steps, succ_tm, hstate, TM.step, h0]
--       -- Now we must apply the IH to the updated configuration after that (n) prefix.
--       -- To justify dyadic well-formedness for the tail, use hd on c and cs.
--       -- The `simp` goal reduces exactly to IH’s statement; we discharge the
--       -- hypothesis as follows:
--       refine ih ?hstate' ?hd'
--       · -- state stays 1 in the copy branch
--         simp [succ_tm, TM.step, hstate, h0]
--       · -- All remaining symbols (c :: cs) are still 0/1
--         intro d hdmem
--         have : d ∈ (inputTape.head :: c :: cs) := by simpa [List.mem_cons] using Or.inr hdmem
--         exact hd d (by simpa)
--     · -- head = '1': symmetric to the '0' case
--       simp [remainingInput, TM.run_for_steps, succ_tm, hstate, TM.step, h1]
--       refine ih ?hstate' ?hd'
--       · simp [succ_tm, TM.step, hstate, h1]
--       · intro d hdmem
--         have : d ∈ (inputTape.head :: c :: cs) := by simpa [List.mem_cons] using Or.inr hdmem
--         exact hd d (by simpa)



-- -- Lemmas for Tape operations
-- @[simp] theorem Tape.move_right_empty {Γ : Type*} [Inhabited Γ] (t : Tape Γ) (h : t.right = []) :
--   (t.move Movement.right) = { left := t.head :: t.left, head := default, right := [] } := by
--   simp [Tape.move, takeFromListOr, h]

-- @[simp] theorem Tape.move_right_cons {Γ : Type*} [Inhabited Γ] (t : Tape Γ) (c : Γ) (cs : List Γ)
--   (h : t.right = c :: cs) :
--   (t.move Movement.right) = { left := t.head :: t.left, head := c, right := cs } := by
--   simp [Tape.move, takeFromListOr, h]

-- theorem Tape.move_right_cons' {Γ : Type*} [Inhabited Γ] (t : Tape Γ) (c : Γ) (cs : List Γ)
--   (h : t.right = c :: cs) :
--   (t.move Movement.right).head = c ∧
--   (t.move Movement.right).left = t.head :: t.left ∧
--   (t.move Movement.right).right = cs := by
--   simp [Tape.move, takeFromListOr, h]


-- -- Simp lemmas for TM.step
-- @[simp] theorem TM.step_accept {k : Nat} {S} [DecidableEq S] {Γ} [Inhabited Γ]
--   (tm : TM k S Γ) (conf : Configuration k S Γ) (h : conf.state = tm.acceptState) :
--   tm.step conf = (conf, none) := by
--   rw [TM.step, h, if_pos (Or.inl rfl)]

-- @[simp] theorem TM.step_reject {k : Nat} {S} [DecidableEq S] {Γ} [Inhabited Γ]
--   (tm : TM k S Γ) (conf : Configuration k S Γ) (h : conf.state = tm.rejectState) :
--   tm.step conf = (conf, none) := by
--   rw [TM.step, h, if_pos (Or.inr rfl)]

-- -- Simplification for successor TM states
-- @[simp] theorem succ_tm_acceptState : succ_tm.acceptState = 2 := rfl
-- @[simp] theorem succ_tm_rejectState : succ_tm.rejectState = 3 := rfl
-- @[simp] theorem succ_tm_startState : succ_tm.startState = 0 := rfl

-- -- Default for BlankChar
-- @[simp] theorem default_BlankChar : (default : BlankChar) = ' ' := rfl

-- -- Helper lemma: after moving right on a tape with empty right, the new head is blank
-- theorem tape_move_right_empty_head {Γ : Type*} [Inhabited Γ] (t : Tape Γ) (h : t.right = []) :
--   (t.move Movement.right).head = default := by
--   simp [Tape.move, takeFromListOr, h]

-- -- Comprehensive lemmas for stepping succ_tm in state 1
-- -- These lemmas describe the complete state after one step, including the new configuration
-- theorem succ_tm_step_state1_char1_complete {c : BlankChar} {cs : List BlankChar}
--   (σ : Configuration 1 (Fin 4) BlankChar)
--   (hstate : σ.state = 1) (htape : (σ.tapes 0).head = '1')
--   (hright : (σ.tapes 0).right = c :: cs) :
--   let (newConf, output) := succ_tm.step σ
--   newConf.state = 1 ∧
--   (newConf.tapes 0).head = c ∧
--   (newConf.tapes 0).left = '1' :: (σ.tapes 0).left ∧
--   (newConf.tapes 0).right = cs ∧
--   output = some '1' := by
--   simp only [TM.step, succ_tm, hstate, htape]
--   simp [Configuration.setState, Configuration.write, Configuration.move]
--   simp [Tape.move, takeFromListOr, hright]
--   exact htape

-- theorem succ_tm_step_state1_char2_complete {c : BlankChar} {cs : List BlankChar}
--   (σ : Configuration 1 (Fin 4) BlankChar)
--   (hstate : σ.state = 1) (htape : (σ.tapes 0).head = '2')
--   (hright : (σ.tapes 0).right = c :: cs) :
--   let (newConf, output) := succ_tm.step σ
--   newConf.state = 1 ∧
--   (newConf.tapes 0).head = c ∧
--   (newConf.tapes 0).left = '2' :: (σ.tapes 0).left ∧
--   (newConf.tapes 0).right = cs ∧
--   output = some '2' := by
--   simp only [TM.step, succ_tm, hstate, htape]
--   simp [Configuration.setState, Configuration.write, Configuration.move]
--   simp [Tape.move, takeFromListOr, hright]
--   exact htape

-- theorem succ_tm_step_state1_blank_complete (σ : Configuration 1 (Fin 4) BlankChar)
--   (hstate : σ.state = 1) (htape : (σ.tapes 0).head = ' ') :
--   let (newConf, output) := succ_tm.step σ
--   newConf.state = 2 ∧
--   output = none := by
--   simp only [TM.step, succ_tm, hstate, htape]
--   simp [Configuration.setState, Configuration.write, Configuration.move]

-- -- Also keep simpler versions for when we don't need full details
-- theorem succ_tm_step_state1_char1 (σ : Configuration 1 (Fin 4) BlankChar)
--   (hstate : σ.state = 1) (htape : (σ.tapes 0).head = '1') :
--   succ_tm.step σ = (((σ.setState 1).write (fun _ => ' ')).move
--     (fun _ => .right), some '1') := by
--   simp only [TM.step, succ_tm, hstate, htape]
--   rfl

-- theorem succ_tm_step_state1_char2 (σ : Configuration 1 (Fin 4) BlankChar)
--   (hstate : σ.state = 1) (htape : (σ.tapes 0).head = '2') :
--   succ_tm.step σ = (((σ.setState 1).write (fun _ => ' ')).move
--     (fun _ => .right), some '2') := by
--   simp only [TM.step, succ_tm, hstate, htape]
--   rfl

-- theorem succ_tm_step_state1_blank (σ : Configuration 1 (Fin 4) BlankChar)
--   (hstate : σ.state = 1) (htape : (σ.tapes 0).head = ' ') :
--   succ_tm.step σ = (((σ.setState 2).write (fun _ => ' ')).move
--     (fun _ => .right), none) := by
--   simp only [TM.step, succ_tm, hstate, htape]
--   rfl

-- -- This lemma shows that when the successor TM is in state 1 (the "copy" state),
-- -- and the remaining input consists of valid dyadic digits ('1' or '2'),
-- -- it will copy those digits to the output and then accept.
-- -- The proof is complex due to the nested structure of run_for_steps and requires
-- -- careful management of the induction and the way steps are computed.
-- lemma copies_in_state_one_of_dyadic
--   {σ : Configuration 1 (Fin 4) BlankChar}
--   (hstate : σ.state = 1)
--   (hd : ∀ c ∈ ((σ.tapes 0).head :: (σ.tapes 0).right), c = '1' ∨ c = '2') :
--   let inputTape := σ.tapes 0
--   let remainingInput := inputTape.head :: inputTape.right
--   let (finalConf, output) := succ_tm.run_for_steps σ (remainingInput.length + 1)
--   finalConf.state = succ_tm.acceptState ∧ output = remainingInput := by
--   intro inputTape remainingInput
--   -- Induction on the length of the remaining input
--   generalize hright_gen : (σ.tapes 0).right = right_list
--   induction right_list generalizing σ with
--   | nil =>
--     -- Base case: single character (either '1' or '2')
--     obtain h | h := hd inputTape.head (by simp [inputTape])
--     <;> simp [remainingInput, inputTape, hright_gen, TM.run_for_steps,
--               succ_tm_step_state1_char1, succ_tm_step_state1_char2,
--               succ_tm_step_state1_blank, hstate, h]
--   | cons c cs ih =>
--     -- Inductive case: head followed by c::cs
--     obtain h | h := hd inputTape.head (by simp [inputTape])
--     <;> simp [remainingInput, inputTape, hright_gen, TM.run_for_steps,
--               succ_tm_step_state1_char1, succ_tm_step_state1_char2, hstate, h]
--     <;> (apply ih <;> simp [TM.step, succ_tm, hstate, h, hright_gen]
--          · intro d hdmem
--            apply hd
--            simp [inputTape, hright_gen, List.mem_cons]
--            exact Or.inr hdmem)

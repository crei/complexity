import Mathlib

universe u v

-- Alias for the transition function type
abbrev Transition (k : Nat) (Q : Type u) (Γ : Type v) :=
  Q → (Fin k → Γ) → Q × ((Fin k) → (Γ × Option Turing.Dir))

structure TM (k : Nat) Q Γ [Inhabited Γ] where
  transition : Transition k Q Γ
  startState : Q
  stopState : Q

structure Configuration (k : Nat) S Γ [Inhabited Γ] where
  state : S
  tapes : Fin k → Turing.Tape Γ

def performTapeOps {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (symbol : Γ) (move : Option Turing.Dir) : Turing.Tape Γ :=
  match move with
  | none => tape.write symbol
  | some d => (tape.write symbol).move d

@[simp]
lemma perform_no_move {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (symbol : Γ) :
  performTapeOps tape symbol none = tape.write symbol := by
  simp [performTapeOps]

@[simp]
lemma perform_write_same_no_move {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (symbol : Γ) (h_same_symbol : tape.head = symbol) :
  performTapeOps tape symbol none = tape := by
  subst h_same_symbol
  simp_all only [perform_no_move, Turing.Tape.write_self]

@[simp]
lemma perform_write_same_move {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (symbol : Γ) (dir : Turing.Dir) (h_same_symbol : tape.head = symbol) :
  performTapeOps tape symbol (some dir) = tape.move dir := by
  subst h_same_symbol; rfl

def Transition.step {k : Nat} {S} [DecidableEq S] {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) : Configuration k S Γ :=
  let (newState, tapeOps) := σ conf.state fun i => (conf.tapes i).head
  {
    state := newState,
    tapes := fun i => performTapeOps (conf.tapes i) (tapeOps i).1 (tapeOps i).2
  }

def Transition.n_steps {k : Nat} {S} [DecidableEq S] {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) (n : Nat) :
  Configuration k S Γ :=
  match n with
  | 0 => conf
  | Nat.succ m => σ.step (σ.n_steps conf m)

theorem n_steps_addition {k : Nat} {S} [DecidableEq S] {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) (m n : Nat) :
  σ.n_steps conf (n + m) = σ.n_steps (σ.n_steps conf n) m := by
  induction m with
  | zero => simp [Transition.n_steps]
  | succ m ih => simp [Transition.n_steps, ih]

@[simp]
lemma single_step {k : Nat} {S} [DecidableEq S] {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) :
  σ.n_steps conf 1 = σ.step conf := by
  rfl

--- In contrast to `Transition.n_steps`, extracts the first step and not the last.
@[simp]
theorem n_steps_first {k : Nat} {S} [DecidableEq S] {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) (n : Nat) :
  σ.n_steps (σ.step conf) n = σ.n_steps conf (n + 1) := by
  calc σ.n_steps (σ.step conf) n
      = σ.n_steps (σ.n_steps conf 1) n := by rfl
      _ = σ.n_steps conf (1 + n) := by simp [n_steps_addition]
      _ = σ.n_steps conf (n + 1) := by rw [Nat.add_comm 1 n]

def TM.initial_configuration {k : Nat} {S} {Γ} [Inhabited Γ]
  (tm : TM k S Γ) (input : List Γ) : Configuration k S Γ :=
  let firstTape := Turing.Tape.mk₁ input
  { state := tm.startState, tapes := fun i => if i.val = 0 then firstTape else default }


-- theorem tm_space_of_initial_configuration {k : Nat} {S} {Γ} [Inhabited Γ]
--   (tm : TM k S Γ) (input : List Γ) :
--   (TM.initial_configuration tm input).space = k := by
--   calc
--     (TM.initial_configuration tm input).space
--     _ = ∑ i, ((TM.initial_configuration tm input).work_tapes i).size := rfl
--     _ = ∑ i: Fin k, ((Tape.fromInput []) : Tape Γ).size :=
--         by simp [TM.initial_configuration, Configuration.work_tapes]
--     _ = k := by simp

-- TOOD At some point we need the statement that we do not change the state
-- after reaching the accept or reject state.

-- def TM.run_on_input_for_steps {k : Nat} {S} [DecidableEq S] {Γ} [Inhabited Γ]
--   (tm : TM k S Γ) (input : List Γ) (steps : ℕ) : Configuration k S Γ :=
--   tm.transition.n_steps (TM.initial_configuration tm input) steps

-- def TM.runs_in_exact_time_and_space {k : Nat} {S} {Γ} [DecidableEq S] [Inhabited Γ]
--   (tm : TM k S Γ) (input : List Γ) (output : List Γ) (t : Nat) (s : Nat) : Prop :=
--   let (conf, output') := tm.run_on_input_for_steps input t
--   output = output' ∧ conf.state = tm.acceptState ∧ conf.space = s

-- def TM.runs_in_time_and_space {k : Nat} {S} {Γ} [DecidableEq S] [Inhabited Γ]
--   (tm : TM k S Γ) (input : List Γ) (output : List Γ) (t : Nat) (s : Nat) : Prop :=
--   ∃ t' ≤ t,
--   let (conf, output') := tm.run_on_input_for_steps input t'
--   output = output' ∧ conf.state = tm.acceptState ∧ conf.space ≤ s

-- def computable_in_time_and_space {Γ} [Inhabited Γ]
--   (f : List Γ → List Γ) (t : Nat → Nat) (s : Nat → Nat) : Prop :=
--   ∃ (k : Nat) (st : Nat) (S : Finset (Fin st)) (tm : TM k S Γ),
--     ∀ input, tm.runs_in_time_and_space input (f input) (t input.length) (s input.length)

-- -- TODO maybe force dyadic encoding so that the bounds make sense?
-- -- or express the bounds in terms of log of the input?
-- def nat_function_computable_in_time_and_space (f : ℕ → ℕ) (t : ℕ → ℕ) (s : ℕ → ℕ) : Prop :=
--   ∃ (encoder : ℕ → List Bool) (decoder : List Bool → ℕ) (_ : ∀ n, decoder (encoder n) = n),
--   ∃ (k : Nat) (st : Nat) (S : Finset (Fin st)) (tm : TM k S Bool),
--   ∀ n, tm.runs_in_time_and_space (encoder n) (encoder (f n)) (t n) (s n)

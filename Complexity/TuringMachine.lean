import Mathlib

inductive Movement
  | left
  | right
  | stay

universe u v

-- Alias for the transition function type
abbrev Transition (k : Nat) (Q : Type u) (Γ : Type v) :=
  Q → (Fin k → Γ) → Q × ((Fin k) → Γ) × ((Fin k) → Movement)

structure TM (k : Nat) Q Γ [Inhabited Γ] where
  transition : Transition k Q Γ
  startState : Q
  stopState : Q

structure Tape Γ where
  left : List Γ
  head : Γ -- The head is pointing at this symbol
  right : List Γ

-- Actually: blank should not be part of input!
@[simp]
def Tape.fromInput {Γ : Type u} (input : List Γ) [Inhabited Γ] : Tape Γ :=
  match input with
    | [] => { left := [], head := default, right := [] }
    | h :: t => { left := [], head := h, right := t }

@[inline]
def takeFromListOr {Γ : Type u} [Inhabited Γ] (l : List Γ) : Γ × List Γ :=
  match l with
    | [] => (default, [])
    | h :: t => (h, t)

def Tape.move {Γ : Type u} [Inhabited Γ] (τ : Tape Γ) (m : Movement) : Tape Γ :=
  match m with
  | .stay => τ
  | .right =>
      let (h, t) := takeFromListOr τ.right
      { left := τ.head :: τ.left, head := h, right := t }
  | .left =>
      let (h, t) := takeFromListOr τ.left
      { left := t, head := h, right := τ.head :: τ.right }

def Tape.write {Γ : Type u} (τ : Tape Γ) (symbol : Γ) : Tape Γ :=
  { τ with head := symbol }

@[simp]
def Tape.size {Γ : Type u} (τ : Tape Γ) : Nat :=
  τ.left.length + 1 + τ.right.length

@[simp] theorem Tape.move_stay {Γ : Type*} [Inhabited Γ] (t : Tape Γ) :
  t.move Movement.stay = t := rfl

@[simp] theorem Tape.write_same {Γ : Type*} (t : Tape Γ) :
  t.write t.head = t := by rfl

example {Γ : Type u} (τ : Tape Γ) : τ.size ≥ 1 := by
  simp [Tape.size]
  linarith

theorem move_at_most_one_space {Γ : Type u} [Inhabited Γ]
  (τ : Tape Γ)
  (m : Movement) :
  (τ.move m).size ≤ τ.size + 1 := by
  cases m
  · simp [Tape.move, Tape.size]
    cases τ.left <;> simp [takeFromListOr] <;> linarith
  · simp [Tape.move, Tape.size]
    cases τ.right <;> simp [takeFromListOr]; linarith
  · simp [Tape.move, Tape.size]

structure Configuration (k : Nat) S Γ where
  state : S
  tapes : Fin k → Tape Γ

-- We also count the input tape.
-- TODO later define a different space measure that does not count the input
-- or output tape if the input tape is not written to and the output tape
-- is never read from.
def Configuration.space {k : Nat} {S} {Γ} (conf : Configuration k S Γ) : Nat :=
  ∑ i, (conf.tapes i).size

def Transition.step {k : Nat} {S} [DecidableEq S] {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) : Configuration k S Γ :=
  let (newState, writeSymbols, moves) := σ conf.state fun i => (conf.tapes i).head
  {
    state := newState,
    tapes := fun i => ((conf.tapes i).write (writeSymbols i)).move (moves i)
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

def TM.initial_configuration {k : Nat} {S} {Γ} [Inhabited Γ]
  (tm : TM k S Γ) (input : List Γ) : Configuration k S Γ :=
  let firstTape := Tape.fromInput input
  let emptyTape := Tape.fromInput []
  { state := tm.startState, tapes := fun i => if i.val = 0 then firstTape else emptyTape }


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

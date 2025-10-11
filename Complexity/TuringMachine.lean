import Mathlib

inductive Movement
  | left
  | right
  | stayj

-- Turing machine with input tape, k work tapes, and one output tape with work alphabet Γ.
structure TM (k : Nat) Q Γ [Inhabited Γ] where
  -- input: state, one symbol from the input tape, k symbols from the k work tapes
  -- output: state, k symbols to write to the work tapes, one optional symbol to write
  -- to the output tape, k + 1 movements (output head is moved always after outputting)
  transition : (σ : Q) → (symbols_read : Fin (k + 1) → Γ) →
               Q × (Fin k → Γ) × Option Γ × (Fin (k + 1) → Movement)
  startState : Q
  acceptState : Q
  rejectState : Q

structure Tape Γ where
  left : List Γ
  head : Γ -- The head is pointing at this symbol
  right : List Γ

universe u

-- Actually: blank should not be part of input!
@[simp]
def Tape.fromInput {Γ : Type u} (input : List Γ) [Inhabited Γ] : Tape Γ :=
  match input with
    | [] => { left := [], head := default, right := [] }
    | h :: t => { left := [], head := h, right := t }

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
  tapes : Fin (k + 1) → Tape Γ
-- output?

def Configuration.work_tapes {k : Nat} {S} {Γ} (conf : Configuration k S Γ) : Fin k → Tape Γ :=
  fun i => conf.tapes i.succ

-- The space required for a configuration. We do not count the space of the input tape,
-- but it does include all cells ever visited, not only the non-empty.
def Configuration.space {k : Nat} {S} {Γ} (conf : Configuration k S Γ) : Nat :=
  ∑ i, (conf.work_tapes i).size

def Configuration.setState {k : Nat} {S} {Γ}
  (conf : Configuration k S Γ) (σ : S) : Configuration k S Γ :=
  { conf with state := σ }

def Configuration.write {k : Nat} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (writes : Fin k → Γ) : Configuration k S Γ :=
  { conf with tapes := fun i => match i with
    | ⟨0, _⟩ => conf.tapes 0
    | ⟨j + 1, h⟩ => (conf.tapes i).write (writes ⟨j, Nat.lt_of_succ_lt_succ h⟩) }

def Configuration.move {k : Nat} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (moves : Fin (k + 1) → Movement) : Configuration k S Γ :=
  { conf with tapes := fun i => (conf.tapes i).move (moves i) }

def TM.step {k : Nat} {S} [DecidableEq S] {Γ} [Inhabited Γ]
  (tm : TM k S Γ) (conf : Configuration k S Γ) : Configuration k S Γ × Option Γ :=
  if conf.state = tm.acceptState ∨ conf.state = tm.rejectState then
    (conf, none)
  else
    let readSymbols := fun i => (conf.tapes i).head
    let (newState, writeSymbols, output, moves) := tm.transition conf.state readSymbols
    (((conf.setState newState).write writeSymbols).move moves, output)

def TM.initial_configuration {k : Nat} {S} {Γ} [Inhabited Γ]
  (tm : TM k S Γ) (input : List Γ) : Configuration k S Γ :=
  let firstTape := Tape.fromInput input
  let emptyTape := Tape.fromInput []
  { state := tm.startState, tapes := fun i => if i.val = 0 then firstTape else emptyTape }

theorem tm_space_of_initial_configuration {k : Nat} {S} {Γ} [Inhabited Γ]
  (tm : TM k S Γ) (input : List Γ) :
  (TM.initial_configuration tm input).space = k := by
  calc
    (TM.initial_configuration tm input).space
    _ = ∑ i, ((TM.initial_configuration tm input).work_tapes i).size := rfl
    _ = ∑ i: Fin k, ((Tape.fromInput []) : Tape Γ).size :=
        by simp [TM.initial_configuration, Configuration.work_tapes]
    _ = k := by simp

def TM.run_for_steps {k : Nat} {S} [DecidableEq S] {Γ} [Inhabited Γ]
  (tm : TM k S Γ) (conf : Configuration k S Γ) (steps : ℕ) : Configuration k S Γ × List Γ :=
  match steps with
  | 0 => (conf, [])
  | Nat.succ n =>
    let (conf, output_word) := TM.run_for_steps tm conf n
    let (newConf, output_char) := tm.step conf
    (newConf, match output_char with
      | none => output_word
      | some o => output_word ++ [o])

def TM.run_on_input_for_steps {k : Nat} {S} [DecidableEq S] {Γ} [Inhabited Γ]
  (tm : TM k S Γ) (input : List Γ) (steps : ℕ) : Configuration k S Γ × List Γ :=
  tm.run_for_steps (TM.initial_configuration tm input) steps

def TM.runs_in_exact_time_and_space {k : Nat} {S} {Γ} [DecidableEq S] [Inhabited Γ]
  (tm : TM k S Γ) (input : List Γ) (output : List Γ) (t : Nat) (s : Nat) : Prop :=
  let (conf, output') := tm.run_on_input_for_steps input t
  output = output' ∧ conf.state = tm.acceptState ∧ conf.space = s

def TM.runs_in_time_and_space {k : Nat} {S} {Γ} [DecidableEq S] [Inhabited Γ]
  (tm : TM k S Γ) (input : List Γ) (output : List Γ) (t : Nat) (s : Nat) : Prop :=
  ∃ t' ≤ t,
  let (conf, output') := tm.run_on_input_for_steps input t'
  output = output' ∧ conf.state = tm.acceptState ∧ conf.space ≤ s

def computable_in_time_and_space {Γ} [Inhabited Γ]
  (f : List Γ → List Γ) (t : Nat → Nat) (s : Nat → Nat) : Prop :=
  ∃ (k : Nat) (st : Nat) (S : Finset (Fin st)) (tm : TM k S Γ),
    ∀ input, tm.runs_in_time_and_space input (f input) (t input.length) (s input.length)

-- TODO maybe force dyadic encoding so that the bounds make sense?
-- or express the bounds in terms of log of the input?
def nat_function_computable_in_time_and_space (f : ℕ → ℕ) (t : ℕ → ℕ) (s : ℕ → ℕ) : Prop :=
  ∃ (encoder : ℕ → List Bool) (decoder : List Bool → ℕ) (_ : ∀ n, decoder (encoder n) = n),
  ∃ (k : Nat) (st : Nat) (S : Finset (Fin st)) (tm : TM k S Bool),
  ∀ n, tm.runs_in_time_and_space (encoder n) (encoder (f n)) (t n) (s n)

import Mathlib

namespace Complexity


inductive Movement
  | left
  | right
  | stay

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
    cases τ.left
    · simp [takeFromListOr]; rfl
    · simp [takeFromListOr]; linarith
  · simp [Tape.move, Tape.size]
    cases τ.right
    · simp [takeFromListOr]
    · simp [takeFromListOr]; linarith
  · simp [Tape.move, Tape.size]

structure Configuration (k : Nat) S Γ where
  state : S
  tapes : Fin (k + 1) → Tape Γ
-- output?

def Configuration.work_tapes {k : Nat} {S} {Γ} (conf : Configuration k S Γ) : Fin k → Tape Γ :=
  fun i => conf.tapes i.succ

-- The space required for a configuration. We do not count the space of the input tape,
-- but it does include all cells even visited, not only the non-empty.
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

def TM.run {k : Nat} {S} [DecidableEq S] {Γ} [Inhabited Γ]
  (tm : TM k S Γ) (input : List Γ) (steps : ℕ) : Configuration k S Γ × List Γ :=
  match steps with
  | 0 => (TM.initial_configuration tm input, [])
  | Nat.succ n =>
    let (conf, output_word) := TM.run tm input n
    let (newConf, output_char) := tm.step conf
    (newConf, match output_char with
      | none => output_word
      | some o => output_word ++ [o])

def TM.runs_in_exact_time_and_space {k : Nat} {S} {Γ} [DecidableEq S] [Inhabited Γ]
  (tm : TM k S Γ) (input : List Γ) (output : List Γ) (t : Nat) (s : Nat) : Prop :=
  let (conf, output') := tm.run input t
  output = output' ∧ conf.state = tm.acceptState ∧ conf.space = s

def TM.runs_in_time_and_space {k : Nat} {S} {Γ} [DecidableEq S] [Inhabited Γ]
  (tm : TM k S Γ) (input : List Γ) (output : List Γ) (t : Nat) (s : Nat) : Prop :=
  ∃ t' ≤ t,
  let (conf, output') := tm.run input t'
  output = output' ∧ conf.state = tm.acceptState ∧ conf.space ≤ s

def computable_in_time_and_space {Γ} [Inhabited Γ]
  (f : List Γ → List Γ) (t : Nat → Nat) (s : Nat → Nat) : Prop :=
  ∃ (k : Nat) (st : Nat) (S : Finset (Fin st)) (tm : TM k S Γ),
    ∀ input, tm.runs_in_time_and_space input (f input) (t input.length) (s input.length)

def nat_function_computable_in_time_and_space (f : ℕ → ℕ) (t : ℕ → ℕ) (s : ℕ → ℕ) : Prop :=
  ∃ (encoder : ℕ → List Bool) (decoder : List Bool → ℕ) (_ : ∀ n, decoder (encoder n) = n),
  ∃ (k : Nat) (st : Nat) (S : Finset (Fin st)) (tm : TM k S Bool),
  ∀ n, tm.runs_in_time_and_space (encoder n) (encoder (f n)) (t n) (s n)

def dyadic_decoding_reverse (x : List Bool) : ℕ :=
  match x with
  | [] => 0
  | false :: xs => (dyadic_decoding_reverse xs) * 2 + 1
  | true :: xs => (dyadic_decoding_reverse xs) * 2 + 2

def dyadic_decoding (x : List Bool) : ℕ :=
  dyadic_decoding_reverse x.reverse

def dyadic_encoding (n : ℕ) : List Bool :=
  if n = 0 then []
  else if Even n then
    dyadic_encoding (n / 2 - 1) ++ [true]
  else
    dyadic_encoding ((n - 1) / 2) ++ [false]

theorem dyadic_encoding_prop_one (n : ℕ) :
  dyadic_encoding (2 * n + 1) = dyadic_encoding n ++ [false] := by
  conv => rw [dyadic_encoding]
  simp

theorem dyadic_encoding_prop_two (n : ℕ) :
  dyadic_encoding (2 * n + 2) = dyadic_encoding n ++ [true] := by
  have h : Even (2 * n + 2) := by
    apply Even.add <;> simp
  conv => rw [dyadic_encoding]
  simp [h]

theorem dyadic_bijective (n : ℕ) :
  dyadic_decoding (dyadic_encoding n) = n := by
  refine Nat.strong_induction_on n ?_; intro n IH
  unfold dyadic_decoding at IH
  by_cases hEven : Even n
  · match n with
    | .zero => simp [dyadic_encoding, dyadic_decoding, dyadic_decoding_reverse]
    | .succ m =>
      have h2 : ∃ n', m = 2 * n' + 1 := by
        simp [Nat.even_add_one, Nat.succ_eq_add_one] at hEven
        exact hEven
      rcases h2 with ⟨n', h2⟩
      rw [h2]
      simp [dyadic_encoding_prop_two, dyadic_decoding, dyadic_decoding_reverse]
      simp [IH n' (by linarith), Nat.mul_comm]
  · have h2 : ∃ n', n = 2 * n' + 1 := by
      simp_all only [Nat.not_even_iff_odd]
      exact hEven
    rcases h2 with ⟨n', hn'⟩
    rw [hn']
    simp [dyadic_encoding_prop_one, dyadic_decoding, dyadic_decoding_reverse]
    simp [IH n' (by linarith), Nat.mul_comm]

theorem id_is_computable_in_constant_time_and_space :
  (nat_function_computable_in_time_and_space (fun x => x) (fun n => 1) (fun n => 1)) := by
  let encoder : ℕ → List Bool := fun n =>
    if n = 0 then [] else List.replicate (n - 1) true ++ [false]
  sorry

--- TODO continue with defining:
-- computes function f in time t and space s
-- and then have a theorem for function composition
-- and then also have a theorem for writing the output into a work tape.


inductive TM.reachable_in_time {k : Nat} {S} {Γ} [DecidableEq S] [Inhabited Γ]
  (tm : TM k S Γ) : Configuration k S Γ → Configuration k S Γ → Nat → Prop where
  | zero (σ : Configuration k S Γ) : TM.reachable_in_time tm σ σ 0
  | succ (σ₁ σ₂ : Configuration k S Γ) (t : Nat) :
      TM.reachable_in_time tm σ₁ σ₂ t →
      TM.reachable_in_time tm σ₁ (tm.step σ₂).1 (t + 1)

-- TODO the input should be over a subset of Γ
def TM.accepts_in_exact_time_with_final_configuration { k: Nat } {S} {Γ} [ DecidableEq S ] (tm : TM k S Γ) (input : List Γ) (t : Nat) (conf : Configuration k S Γ) : Prop :=
  let σ₀ := TM.initial_configuration tm input
  conf.state = tm.acceptState ∧ TM.reachable_in_time tm σ₀ conf t

def TM.accepts_in_exact_time { k: Nat } {S} {Γ} [ DecidableEq S ] (tm : TM k S Γ) (input : List Γ) (t : Nat) : Prop :=
  ∃ σ, TM.accepts_in_exact_time_with_final_configuration tm input t σ

def TM.accepts_in_time { k: Nat } {S} {Γ} [ DecidableEq S ] (tm : TM k S Γ) (input : List Γ) (t : Nat) : Prop :=
  ∃ t' ≤ t, tm.accepts_in_exact_time input t'

def TM.accepts_language_in_time { k : Nat } {S} {Γ} [ DecidableEq S ] (tm : TM k S Γ) (L : List (List Γ)) (t : Nat → Nat) : Prop :=
  ∀ w ∈ L, tm.accepts_in_time w (t w.length)

def DetTime {Γ} (t : Nat → Nat) (L : List (List Γ)) : Prop :=
  ∃ (k : Nat) (s : Nat) (S : Finset (Fin s)) (tm : TM k S Γ),
  tm.accepts_language_in_time L t

def TM.accepts_in_space_with_final_configuration {k : Nat} {S} {Γ} [DecidableEq S]
  (tm : TM k S Γ) (input : List Γ) (s : Nat) (conf : Configuration k S Γ) : Prop :=
  let σ₀ := TM.initial_configuration tm input
  conf.state = tm.acceptState ∧ TM.reachable_in_time tm σ₀ conf s ∧ (conf.space ≤ s)

def TM.accepts_in_space {k : Nat} {S} {Γ} [DecidableEq S]
  (tm : TM k S Γ) (input : List Γ) (s : Nat) : Prop :=
  ∃ conf, TM.accepts_in_space_with_final_configuration tm input s conf

def DetSpace {Γ} (s : Nat → Nat) (L : List (List Γ)) : Prop :=
  ∃ (k : Nat) (st : Nat) (S : Finset (Fin st)) (tm : TM k S Γ),
    tm.accepts_language_in_time L s

theorem tm_move_each_at_most_1_space {k : Nat} {S} {Γ}
  (tm : TM k S Γ) (conf : Configuration k S Γ) (m : Fin k → Movement) :
  ∀ i, ((tm.move conf m).tapes i).size ≤ (conf.tapes i).size + 1 := by
  intro i
  simp [TM.move, move_at_most_one_space]

theorem tm_move_at_most_k_space {k : Nat} {S} {Γ}
  (tm : TM k S Γ) (conf : Configuration k S Γ) (moves : Fin k → Movement) :
  (tm.move conf moves).space ≤ conf.space + k := by
  calc
    (tm.move conf moves).space
      = ∑ i, ((tm.move conf moves).tapes i).size := rfl
    _ ≤ ∑ i, ((conf.tapes i).size + 1) := by simp [Finset.sum_le_sum, tm_move_each_at_most_1_space]
    _ = (∑ i, (conf.tapes i).size) + ∑ i : Fin k, 1 := by simp [Finset.sum_add_distrib]
    _ = conf.space + k := by simp [Configuration.space]

theorem tm_step_at_most_k_space {k : Nat} {S} {Γ} [DecidableEq S]
  (tm : TM k S Γ) (conf : Configuration k S Γ) :
  (tm.step conf).space ≤ conf.space + k := by
  simp [TM.step]
  by_cases hhalt : conf.state = tm.acceptState ∨ conf.state = tm.rejectState
  · simp [hhalt]
  · simp [hhalt]
    apply tm_move_at_most_k_space

theorem reachable_space_at_most_time {k : Nat} {S} {Γ} [DecidableEq S]
  (tm : TM k S Γ) (input : List Γ) (t : Nat) (conf : Configuration k S Γ)
  (h : TM.reachable_in_time tm (TM.initial_configuration tm input) conf t) :
  conf.space ≤ (max 1 input.length) + k + t * (k + 1) := by
  induction h with
  | zero => simp [tm_space_of_initial_configuration]
  | succ σ t' hpref ih =>
    calc
      (tm.step σ).space
      _ ≤ σ.space + k := by apply tm_step_at_most_k_space
      _ ≤ max 1 input.length + k + t' * (k + 1) + k := by simp [ih]
      _ ≤ (max 1 input.length) + k + (t' + 1) * (k + 1) := by linarith

theorem space_at_most_time {k : Nat} {S} {Γ} [DecidableEq S]
  (tm : TM k S Γ) (input : List Γ) (t : Nat) (conf : Configuration k S Γ)
  (h : TM.accepts_in_exact_time_with_final_configuration tm input t conf) :
  conf.space ≤ (max 1 input.length) + k + t * (k + 1) := by
  simp [reachable_space_at_most_time tm input t conf h.right]

-- Space compression:
-- start with a TM t with k tapes.
-- Add another tape which will be used to store the input in a compressed format.
-- Copy the input tape in a compressed way to the new tape.
-- Then simulate t, but whenever t wants to read or write the input tape,
-- we read or write the compressed tape instead.
-- Operations on the other tapes are also compressed.
-- Each symbol of the compressed symbol set represents a pair of symbols of the original tape.

def compressed_transition { k: Nat } {S} {Γ}
  (transition : S → (Fin k → Γ) → (S × (Fin k → Γ) × (Fin k → Movement)))
  (state : S) (symbols_read₁ symbols_read₂ : Fin k → Γ) :
    (S × (Fin k → Γ) × (Fin k → Γ) × (Fin k → Movement)) :=



def compressed_tm { k: Nat } {S} {Γ}
  (tm : TM k S Γ) : TM (k + 1) (Fin 2 × S) (Γ × Γ) :=
  { blank := (tm.blank, tm.blank)
    transition := fun state symbols_read => sorry
      -- let inputSymbol := symbols 0
      -- let symbols₁: Fin k → Γ := fun i => (symbols (i + 1)).1
      -- let (newState, writeSymbols₁, moves₁) := tm.transition s symbols₁
      -- let writeSymbols : Fin (k + 1) → (Γ × Γ) := fun i =>
      --   if i.val = 0 then inputSymbol
      --   else (writeSymbols₁ (i - 1), (symbols i).2)
      -- let moves : Fin (k + 1) → Movement := fun i =>
      --   if i.val = 0 then .stay
      --   else moves₁ (i - 1)
      -- (newState, writeSymbols, moves)
    startState := tm.startState
    acceptState := tm.acceptState
    rejectState := tm.rejectState
    k_nonzero := by simp
  }


def doesNotModifyInputTape { k: Nat } {S} {Γ} [ DecidableEq S ] (tm : TM k S Γ) : Prop :=
  ∀ s symbols,
    let (_, writeSymbols, _) := tm.transition s symbols
    symbols.take 1 = writeSymbols.take 1

-- -- TODO this is actually wrong because the tapes are different, because
-- -- the heads are at different positions.
-- theorem input_tape_not_modified_then_also_in_step
--   [ DecidableEq S ]
--   (tm : TM k S Γ)
--   (σ : Configuration k S Γ)
--   (nm : doesNotModifyInputTape tm) :
--   σ.tapes.take 1 = (tm.step σ).tapes.take 1 := by
--   unfold TM.step
--   by_cases hhalt : σ.state = tm.acceptState ∨ σ.state = tm.rejectState
--   · simp [hhalt, TM.step]
--   · simp [hhalt]
--     let (newState, writeSymbols, moves) := tm.transition σ.state (σ.tapes.map (·.head))
--     unfold doesNotModifyInputTape at nm
--     specialize nm σ.state (σ.tapes.map (·.head))
--     simpa [TM.move, nm] using rfl


def productTM { k₁ k₂: Nat } {S₁ S₂} {Γ}
  (tm₁ : TM k₁ S₁ Γ) (tm₂ : TM k₂ S₂ Γ) : TM (k₁ + k₂ - 1) (S₁ × S₂) Γ :=
  { blank := tm₁.blank -- TODO is that a problem?
    transition := fun (s₁, s₂) symbols =>
      -- first symbol is the input symbol
      let input := symbols.take 1
      let symbols₁: Vector Γ k₁ := (Vector.take symbols k₁).cast ( by
          zify at *
          have h1 : 0 ≤ ↑ k₂ - 1 := by simp
          have h : k₁ ≤ k₁ + k₂ - 1 := by zify; linarith
          exact Nat.min_eq_left h
        )
      let (newState₁, writeSymbols₁, moves₁) := tm₁.transition s₁ symbols₁
      let symbols₂ : Vector Γ k₂ := #v[input] ++ (Vector.drop symbols k₁)
      let (newState₂, writeSymbols₂, moves₂) := tm₂.transition s₂ symbols₂
      ( (newState₁, newState₂),
        writeSymbols₁ ++ writeSymbols₂,
        moves₁ ++ moves₂ )
    startState := (tm₁.startState, tm₂.startState)
    acceptState := (tm₁.acceptState, tm₂.acceptState)
    rejectState := (tm₁.rejectState, tm₂.rejectState)
    k_nonzero := by simp
  }


end Complexity

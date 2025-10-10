import Mathlib

namespace Complexity


inductive Movement
  | left
  | right
  | stay

structure TM (k : Nat) S Γ where
  blank : Γ -- the blank symbol
  transition : S → Vector Γ k → (S × Vector Γ k × Vector Movement k)
  startState : S
  acceptState : S
  rejectState : S
  k_nonzero : k ≥ 1


structure Tape Γ where
  left : List Γ
  head : Γ -- The head is pointing at this symbol
  right : List Γ

universe u

-- Actually: blank should not be part of input!
def Tape.fromInput {Γ : Type u} (input : List Γ) (blank : Γ) : Tape Γ :=
  match input with
    | [] => { left := [], head := blank, right := [] }
    | h :: t => { left := [], head := h, right := t }

def takeFromListOr {α : Type u} (l : List α) (default : α) : α × List α :=
  match l with
    | [] => (default, [])
    | h :: t => (h, t)

def Tape.move {Γ : Type u} (τ : Tape Γ) (m : Movement) (blank : Γ) : Tape Γ :=
  match m with
  | .stay => τ
  | .right =>
      let (h, t) := takeFromListOr τ.right blank
      { left := τ.head :: τ.left, head := h, right := t }
  | .left =>
      let (h, t) := takeFromListOr τ.left blank
      { left := t, head := h, right := τ.head :: τ.right }

def Tape.write {Γ : Type u} (τ : Tape Γ) (symbol : Γ) : Tape Γ :=
  { τ with head := symbol }

def Tape.size {Γ : Type u} (τ : Tape Γ) : Nat :=
  τ.left.length + 1 + τ.right.length

example {Γ : Type u} (τ : Tape Γ) : τ.size ≥ 1 := by
  simp [Tape.size]
  linarith

theorem space_of_input {Γ : Type u} (x : List Γ) (blank : Γ) :
  (Tape.fromInput x blank).size = max 1 x.length := by
  cases x
  · simp [Tape.size, Tape.fromInput]
  · simp [Tape.size, Tape.fromInput]
    rw [Nat.add_comm]

theorem move_at_most_one_space {Γ : Type u}
  (τ : Tape Γ)
  (m : Movement)
  (blank : Γ) :
  (τ.move m blank).size ≤ τ.size + 1 := by
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
  tapes : Vector (Tape Γ) k

def Configuration.space {k : Nat} {S} {Γ} (conf : Configuration k S Γ) : Nat :=
  (conf.tapes.map (fun τ => τ.size)).sum

def TM.move { k: Nat } {S} {Γ}
  (tm : TM k S Γ) (conf : Configuration k S Γ) (moves : Vector Movement k) :
    Configuration k S Γ :=
  { conf with tapes := (conf.tapes.zip moves).map fun (τ, m) => τ.move m tm.blank }

def TM.step { k: Nat } {S} {Γ} [ DecidableEq S ] (tm : TM k S Γ) (conf : Configuration k S Γ) : Configuration k S Γ :=
  if conf.state = tm.acceptState ∨ conf.state = tm.rejectState then
    conf
  else
    let (newState, writeSymbols, moves) := tm.transition conf.state (conf.tapes.map (·.head))
    let conf := { state := newState, tapes := (conf.tapes.zip writeSymbols).map (fun (τ, s) => Tape.write τ s) }
    tm.move conf moves

def TM.initial_configuration { k: Nat } {S} {Γ} (tm : TM k S Γ) (input : List Γ) : Configuration k S Γ :=
  let firstTape := Tape.fromInput input tm.blank
  let emptyTape := Tape.fromInput [] tm.blank
  { state := tm.startState, tapes := (Vector.replicate k emptyTape).set! 0 firstTape }

inductive TM.reachable_in_time { k: Nat } {S} {Γ} [ DecidableEq S ] (tm : TM k S Γ) : Configuration k S Γ → Configuration k S Γ → Nat → Prop where
  | zero (σ : Configuration k S Γ) : TM.reachable_in_time tm σ σ 0
  | succ (σ₁ σ₂ : Configuration k S Γ) (t : Nat) :
      TM.reachable_in_time tm σ₁ σ₂ t →
      TM.reachable_in_time tm σ₁ (tm.step σ₂) (t + 1)


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

def TM.accepts_in_space_with_final_configuration {k : Nat} {S} {Γ} [DecidableEq S]
  (tm : TM k S Γ) (input : List Γ) (s : Nat) (conf : Configuration k S Γ) : Prop :=
  let σ₀ := TM.initial_configuration tm input
  conf.state = tm.acceptState ∧ TM.reachable_in_time tm σ₀ conf s ∧ (conf.space ≤ s)

def TM.accepts_in_space {k : Nat} {S} {Γ} [DecidableEq S]
  (tm : TM k S Γ) (input : List Γ) (s : Nat) : Prop :=
  ∃ conf, TM.accepts_in_space_with_final_configuration tm input s conf

theorem tm_move_each_at_most_1_space {k : Nat} {S} {Γ}
  (tm : TM k S Γ) (conf : Configuration k S Γ) (m : Vector Movement k) :
  ∀ before after,
  (before, after) ∈ conf.tapes.zip (tm.move conf m).tapes → after.size ≤ before.size + 1 := by
  intros before after h
  simp [TM.move] at h



theorem tm_move_at_most_k_space { k: Nat } {S} {Γ}
  (tm : TM k S Γ) (conf : Configuration k S Γ) (moves : Vector Movement k) :
  (tm.move conf moves).space ≤ conf.space + k := by
  simp [Configuration.space]
  have h : ∀ τ ∈ conf.tapes, ∀ movements : Vector Movement k, tm.move m tm.blank).size ≤ τ.size + 1 := by
    simp [move_at_most_one_space]
  simp [TM.move, Vector.sum]

  rw [Array.sum_eq_sum_toList]


  -- we need List.sum_le_card_nsmul

  apply?
  sorry

theorem space_at_most_time {k : Nat} {S} {Γ} [DecidableEq S]
  (tm : TM k S Γ) (input : List Γ) (t : Nat) (conf : Configuration k S Γ)
  (h : TM.accepts_in_exact_time_with_final_configuration tm input t conf) :
  conf.space ≤ t * (k + 1) := by
  sorry

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

def hello := "world"


namespace Sat


inductive Literal
  | pos : Nat → Literal
  | neg : Nat → Literal

def Literal.encode (lit : Literal) : String :=
  match lit with
  | .pos v => s!"{v}"
  | .neg v => s!"¬{v}"

def Clause := List Literal

def Clause.eval (clause : Clause) (assignment : Nat → Bool) : Bool :=
  clause.any (fun
    | .pos v => assignment v
    | .neg v => !assignment v)

def Clause.encode (clause : Clause) : String :=
  let literalsStr := clause.map Literal.encode
  let joined := literalsStr.intersperse "∨"
  let clause := joined.foldl (· ++ ·) ""
  s!"({clause})"

def Formula := List Clause

def evaluate (f : Formula) (assignment : Nat → Bool) : Bool :=
  f.all fun clause => clause.eval assignment

def Formula.encode (f : Formula) : String :=
  let clausesStr := f.map Clause.encode
  let joined := clausesStr.intersperse "∧"
  joined.foldl (· ++ ·) ""

def isSatisfiable (f : Formula) : Prop :=
  ∃ assignment, evaluate f assignment

end Sat

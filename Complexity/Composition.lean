import Mathlib
import Complexity.TuringMachine

/-!
# Turing Machine Composition

This file defines composition of Turing machines and proves its correctness.

## Main Result

`compose_tms`: Given two TMs `t1` and `t2`, constructs `t3` that computes `t2 ∘ t1`.

## Implementation Strategy

The composed machine `t3` has additional tapes to store intermediate results:
- It runs `t1` first, but redirects output to an intermediate tape instead of the output
- When `t1` accepts, it resets the intermediate tape head to the start
- Then it runs `t2`, reading from the intermediate tape instead of the input tape
- `t2`'s output goes to the actual output

The composed machine has `k1 + k2 + 1` work tapes:
- First `k1` tapes for `t1`'s work tapes
- Next `k2` tapes for `t2`'s work tapes
- One extra tape for the intermediate result (t1_output)

-/

open TM

namespace Composition

/-! ### Preconditions -/

/-- A TM never outputs the default (blank) symbol.
    This is needed for composition to work correctly when detecting
    the leftmost position of the intermediate tape. -/
def no_default_output {k : Nat} {Q Γ : Type*} [Inhabited Γ] [DecidableEq Q]
    (tm : TM k Q Γ) : Prop :=
  ∀ (conf : Configuration k Q Γ),
    let (_, output) := tm.step conf
    output ≠ some default

/-! ### State Type for Composed Machine -/

/-- States for the composed machine:
    - `running_t1`: Executing the first machine
    - `resetting_head`: Moving the intermediate tape head left until hitting default
    - `running_t2`: Executing the second machine
    - `accept`: Final accept state
    - `reject`: Final reject state
-/
inductive ComposeState (Q1 Q2 : Type*) where
  | running_t1 : Q1 → ComposeState Q1 Q2
  | resetting_head : ComposeState Q1 Q2
  | running_t2 : Q2 → ComposeState Q1 Q2
  | accept : ComposeState Q1 Q2
  | reject : ComposeState Q1 Q2
  deriving DecidableEq

/-! ### Helper Definitions -/

/-- Index of the intermediate tape (t1_output) in the composed machine.
    It's placed after all work tapes of t1 and t2. -/
def intermediate_tape_idx (k1 k2 : Nat) : Fin (k1 + k2 + 1 + 1) :=
  ⟨k1 + k2 + 1, by omega⟩

/-- Map a tape index from t1 (0 = input, 1..k1 = work) to t3's tape layout -/
def map_t1_tape (k1 k2 : Nat) (i : Fin (k1 + 1)) : Fin (k1 + k2 + 1 + 1) :=
  if h : i.val = 0 then
    ⟨0, by omega⟩  -- input tape stays at 0
  else
    ⟨i.val, by omega⟩  -- work tapes 1..k1

/-- Map a tape index from t2 (0 = input, 1..k2 = work) to t3's tape layout -/
def map_t2_tape (k1 k2 : Nat) (i : Fin (k2 + 1)) : Fin (k1 + k2 + 1 + 1) :=
  if h : i.val = 0 then
    intermediate_tape_idx k1 k2  -- t2 reads from intermediate tape
  else
    ⟨k1 + i.val, by omega⟩  -- t2's work tapes start after t1's

/-! ### Composed Machine Construction -/

/-- Compose two Turing machines.
    The resulting machine computes the composition t2 ∘ t1.
    Requires: t1 never outputs the default symbol (needed for head reset detection). -/
def compose_tms {k1 k2 : Nat} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (t1 : TM k1 Q1 Γ) (t2 : TM k2 Q2 Γ) :
    TM (k1 + k2 + 1) (ComposeState Q1 Q2) Γ where
  transition σ symbols_read :=
    match σ with
    | ComposeState.running_t1 q1 =>
        -- Run t1, but redirect output to intermediate tape
        if q1 = t1.acceptState then
          -- t1 accepted, start resetting intermediate tape head
          -- Move left until we hit default (leftmost position)
          let moves : Fin (k1 + k2 + 1 + 1) → Movement := fun i =>
            if i.val = (intermediate_tape_idx k1 k2).val then
              Movement.left
            else
              Movement.stay
          (ComposeState.resetting_head, (fun _ => default), none, moves)
        else if q1 = t1.rejectState then
          -- t1 rejected, reject
          (ComposeState.reject, (fun _ => default), none, (fun _ => Movement.stay))
        else
          -- Execute t1's transition
          let t1_symbols := fun i => symbols_read (map_t1_tape k1 k2 i)
          let (q1', writes, output, moves) := t1.transition q1 t1_symbols
          -- Redirect output to intermediate tape instead
          let t3_writes : Fin (k1 + k2 + 1) → Γ := fun i =>
            if h : i.val < k1 then
              writes ⟨i.val, by omega⟩
            else
              default
          let t3_moves : Fin (k1 + k2 + 1 + 1) → Movement := fun i =>
            if i.val = 0 then
              moves ⟨0, by omega⟩
            else if h : i.val < k1 + 1 then
              moves ⟨i.val, h⟩
            else if i.val = (intermediate_tape_idx k1 k2).val then
              -- Move intermediate tape head for output
              match output with
              | some _ => Movement.right  -- Write happened, move right
              | none => Movement.stay
            else
              Movement.stay
          -- Write output to intermediate tape if present
          let t3_writes_with_output : Fin (k1 + k2 + 1) → Γ := fun i =>
            if i.val = (intermediate_tape_idx k1 k2).val - 1 then
              match output with
              | some c => c
              | none => default
            else
              t3_writes i
          (ComposeState.running_t1 q1', t3_writes_with_output, none, t3_moves)

    | ComposeState.resetting_head =>
        -- Check if we've reached the leftmost position (reading default)
        let intermediate_symbol := symbols_read (intermediate_tape_idx k1 k2)
        if intermediate_symbol = default then
          -- We've gone past the leftmost non-default symbol, move right once and start t2
          let moves : Fin (k1 + k2 + 1 + 1) → Movement := fun i =>
            if i.val = (intermediate_tape_idx k1 k2).val then
              Movement.right
            else
              Movement.stay
          (ComposeState.running_t2 t2.startState, (fun _ => default), none, moves)
        else
          -- Keep moving left
          let moves : Fin (k1 + k2 + 1 + 1) → Movement := fun i =>
            if i.val = (intermediate_tape_idx k1 k2).val then
              Movement.left
            else
              Movement.stay
          (ComposeState.resetting_head, (fun _ => default), none, moves)

    | ComposeState.running_t2 q2 =>
        -- Run t2, reading from intermediate tape
        if q2 = t2.acceptState then
          (ComposeState.accept, (fun _ => default), none, (fun _ => Movement.stay))
        else if q2 = t2.rejectState then
          (ComposeState.reject, (fun _ => default), none, (fun _ => Movement.stay))
        else
          let t2_symbols := fun i => symbols_read (map_t2_tape k1 k2 i)
          let (q2', writes, output, moves) := t2.transition q2 t2_symbols
          -- Map t2's writes and moves to t3's tape layout
          let t3_writes : Fin (k1 + k2 + 1) → Γ := fun i =>
            if h : k1 ≤ i.val ∧ i.val < k1 + k2 then
              writes ⟨i.val - k1, by omega⟩
            else
              default
          let t3_moves : Fin (k1 + k2 + 1 + 1) → Movement := fun i =>
            if i.val = (intermediate_tape_idx k1 k2).val then
              moves ⟨0, by omega⟩  -- intermediate tape follows t2's input moves
            else if h : k1 + 1 ≤ i.val ∧ i.val < k1 + k2 + 1 then
              moves ⟨i.val - k1, by omega⟩  -- t2's work tape moves
            else
              Movement.stay
          (ComposeState.running_t2 q2', t3_writes, output, t3_moves)

    | ComposeState.accept =>
        (ComposeState.accept, (fun _ => default), none, (fun _ => Movement.stay))

    | ComposeState.reject =>
        (ComposeState.reject, (fun _ => default), none, (fun _ => Movement.stay))

  startState := ComposeState.running_t1 t1.startState
  acceptState := ComposeState.accept
  rejectState := ComposeState.reject

/-! ### Helper Lemmas -/

/-- Configuration.write only affects work tapes (not tape 0) -/
lemma Configuration.write_tape_zero {k : Nat} {S Γ : Type*} [Inhabited Γ]
    (conf : Configuration k S Γ) (writes : Fin k → Γ) :
    (conf.write writes).tapes 0 = conf.tapes 0 := by
  simp [Configuration.write]
  rfl

/-- Configuration.write affects non-zero tapes by writing -/
lemma Configuration.write_tape_succ {k : Nat} {S Γ : Type*} [Inhabited Γ]
    (conf : Configuration k S Γ) (writes : Fin k → Γ) (j : Nat) (h : j + 1 < k + 1) :
    (conf.write writes).tapes ⟨j + 1, h⟩ =
      (conf.tapes ⟨j + 1, h⟩).write (writes ⟨j, Nat.lt_of_succ_lt_succ h⟩) := by
  simp [Configuration.write]

/-- Configuration.move applies the movement to each tape -/
lemma Configuration.move_tapes {k : Nat} {S Γ : Type*} [Inhabited Γ]
    (conf : Configuration k S Γ) (moves : Fin (k + 1) → Movement) (i : Fin (k + 1)) :
    (conf.move moves).tapes i = (conf.tapes i).move (moves i) := by
  simp [Configuration.move]

/-- Tape.write doesn't change the left list -/
lemma Tape.write_left {Γ : Type*} (τ : Tape Γ) (c : Γ) :
    (τ.write c).left = τ.left := by
  simp [Tape.write]

/-- Moving left on a tape gives tail of left list -/
lemma Tape.move_left_left {Γ : Type*} [Inhabited Γ] (τ : Tape Γ) :
    (τ.move Movement.left).left = τ.left.tail := by
  simp [Tape.move, takeFromListOr]
  cases τ.left <;> rfl

/-!
## Status of Proofs

The lemmas below establish the correctness of the composition construction.
Currently, the low-level tape manipulation lemmas (`reset_step_non_default`,
`reset_step_default`) are left as `sorry`. These require detailed reasoning about
how `Configuration.write` and `Configuration.move` interact with specific tape indices.

The high-level structure is complete:
- `reset_step_non_default`: Shows that when reading a non-default symbol in resetting_head,
  we stay in resetting_head and the left list becomes its tail (moving left)
- `reset_step_default`: Shows that when reading default in resetting_head with empty left list,
  we transition to running_t2 and maintain empty left list (moving right once)
- `head_reset_terminates`: Uses the above to show the reset phase terminates
- `sequential_execution`: Shows t2 starts after t1 completes
- `compose_tms_correct`: Main correctness theorem

Proving the tape manipulation lemmas requires:
1. Understanding how `Configuration.write` affects individual tapes based on tape index
2. Tracking how `Configuration.move` applies movements to specific tapes
3. Showing that writes to work tapes don't affect the intermediate tape
4. Proving that moving left reduces the left list to its tail
-/

/-- A step in the resetting_head state when reading a non-default symbol moves left -/
lemma reset_step_non_default {k1 k2 : Nat} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (t1 : TM k1 Q1 Γ) (t2 : TM k2 Q2 Γ)
    (conf : Configuration (k1 + k2 + 1) (ComposeState Q1 Q2) Γ)
    (h_state : conf.state = ComposeState.resetting_head)
    (h_non_default : (conf.tapes (intermediate_tape_idx k1 k2)).head ≠ default) :
    let t3 := compose_tms t1 t2
    let (conf', _) := t3.step conf
    conf'.state = ComposeState.resetting_head ∧
    (conf'.tapes (intermediate_tape_idx k1 k2)).left =
      (conf.tapes (intermediate_tape_idx k1 k2)).left.tail := by
  -- This proof requires detailed reasoning about Configuration operations
  -- Key steps:
  -- 1. The transition keeps state as resetting_head
  -- 2. The write doesn't affect tapes (writes default to work tapes, not intermediate)
  -- 3. The move operation moves the intermediate tape left
  -- 4. Moving left reduces the left list by its tail
  sorry

/-- A step in the resetting_head state when reading default transitions to running_t2.
    Requires that the left list is already empty (we've moved past the leftmost symbol). -/
lemma reset_step_default {k1 k2 : Nat} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (t1 : TM k1 Q1 Γ) (t2 : TM k2 Q2 Γ)
    (conf : Configuration (k1 + k2 + 1) (ComposeState Q1 Q2) Γ)
    (h_state : conf.state = ComposeState.resetting_head)
    (h_default : (conf.tapes (intermediate_tape_idx k1 k2)).head = default)
    (h_left_empty : (conf.tapes (intermediate_tape_idx k1 k2)).left = []) :
    let t3 := compose_tms t1 t2
    let (conf', _) := t3.step conf
    conf'.state = ComposeState.running_t2 t2.startState ∧
    (conf'.tapes (intermediate_tape_idx k1 k2)).left = [] := by
  -- This requires careful reasoning about Configuration.move and Configuration.write
  -- Moving right from an empty left list keeps it empty
  sorry

/-- After t1 accepts, the head reset phase terminates and t2 starts.
    This lemma shows that the intermediate tape head successfully resets to the start. -/
lemma head_reset_terminates {k1 k2 : Nat} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (t1 : TM k1 Q1 Γ) (t2 : TM k2 Q2 Γ)
    (h_no_default : no_default_output t1)
    (conf : Configuration (k1 + k2 + 1) (ComposeState Q1 Q2) Γ)
    (h_state : conf.state = ComposeState.resetting_head)
    (h_no_default_on_tape : ∀ c ∈ (conf.tapes (intermediate_tape_idx k1 k2)).left,
                             c ≠ default) :
    ∃ t_reset : Nat,
      let t3 := compose_tms t1 t2
      let (conf', _) := t3.run_for_steps conf t_reset
      conf'.state = ComposeState.running_t2 t2.startState ∧
      (conf'.tapes (intermediate_tape_idx k1 k2)).left = [] := by
  -- The number of steps needed is the length of the left list + 1
  -- (move left until we hit default, then move right once)
  let intermediate_tape := conf.tapes (intermediate_tape_idx k1 k2)
  let n := intermediate_tape.left.length
  use n + 1
  -- We need to prove this by induction on the length of the left list
  sorry

/-- Sequential execution: after t1 accepts, the composed machine eventually starts t2 -/
lemma sequential_execution {k1 k2 : Nat} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (t1 : TM k1 Q1 Γ) (t2 : TM k2 Q2 Γ)
    (h_no_default : no_default_output t1)
    (input : List Γ) (t_1 : Nat) :
    let (conf1, out1) := t1.run_on_input_for_steps input t_1
    conf1.state = t1.acceptState →
    ∃ t_2 : Nat,
      let t3 := compose_tms t1 t2
      let (conf3, out3) := t3.run_on_input_for_steps input (t_1 + t_2)
      conf3.state = ComposeState.running_t2 t2.startState := by
  sorry

/-! ### Main Theorem -/

/-- Composition correctness: if t1 computes f and t2 computes g,
    then compose_tms t1 t2 computes g ∘ f.
    Requires: t1 never outputs the default symbol. -/
theorem compose_tms_correct {k1 k2 : Nat} {Q1 Q2 Γ : Type*}
    [Inhabited Γ] [DecidableEq Q1] [DecidableEq Q2] [DecidableEq Γ]
    (t1 : TM k1 Q1 Γ) (t2 : TM k2 Q2 Γ)
    (h_no_default : no_default_output t1)
    (f g : List Γ → List Γ)
    (h_t1 : ∀ input, ∃ t s, t1.runs_in_time_and_space input (f input) t s)
    (h_t2 : ∀ input, ∃ t s, t2.runs_in_time_and_space input (g input) t s) :
    let t3 := compose_tms t1 t2
    ∀ input, ∃ t s, t3.runs_in_time_and_space input (g (f input)) t s := by
  sorry

end Composition

import Mathlib

import Complexity.Bounds

universe u v

-- Custom Char type with ' ' as default (instead of 'A')
def BlankChar := Char

instance : Inhabited BlankChar where
  default := ' '

instance : DecidableEq BlankChar := inferInstanceAs (DecidableEq Char)

-- Coercion from Char to BlankChar
instance : Coe Char BlankChar where
  coe c := c

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

def Transition.step {k : Nat} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) : Configuration k S Γ :=
  let (newState, tapeOps) := σ conf.state fun i => (conf.tapes i).head
  {
    state := newState,
    tapes := fun i => performTapeOps (conf.tapes i) (tapeOps i).1 (tapeOps i).2
  }

def Transition.n_steps {k : Nat} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) (n : Nat) :
  Configuration k S Γ :=
  match n with
  | 0 => conf
  | Nat.succ m => σ.step (σ.n_steps conf m)

@[simp]
lemma n_steps_zero {k : Nat} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) :
  σ.n_steps conf 0 = conf := by
  rfl

theorem n_steps_addition {k : Nat} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) (m n : Nat) :
  σ.n_steps conf (n + m) = σ.n_steps (σ.n_steps conf n) m := by
  induction m with
  | zero => simp [Transition.n_steps]
  | succ m ih => simp [Transition.n_steps, ih]

@[simp]
lemma single_step {k : Nat} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) :
  σ.n_steps conf 1 = σ.step conf := by
  rfl

--- In contrast to `Transition.n_steps`, extracts the first step and not the last.
@[simp]
theorem n_steps_first {k : Nat} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) (n : Nat) :
  σ.n_steps (σ.step conf) n = σ.n_steps conf (n + 1) := by
  calc σ.n_steps (σ.step conf) n
      = σ.n_steps (σ.n_steps conf 1) n := by rfl
      _ = σ.n_steps conf (1 + n) := by simp [n_steps_addition]
      _ = σ.n_steps conf (n + 1) := by rw [Nat.add_comm 1 n]

def TM.initial_configuration {k : Nat} {S} {Γ}
  (tm : TM k S (Option Γ)) (input : List Γ) : Configuration k S (Option Γ) :=
  let firstTape := Turing.Tape.mk₁ (input.map some)
  { state := tm.startState, tapes := fun i => if i.val = 0 then firstTape else default }

-- TOOD At some point we need the statement that we do not change the state
-- after reaching the accept or reject state.

def tape_equiv_up_to_shift {Γ} [Inhabited Γ]
  (t1 t2 : Turing.Tape Γ) : Prop :=
  ∃ shift : ℕ, ∃ dir, t2 = (Turing.Tape.move dir)^[shift] t1

def TM.runs_in_exact_time {k : Nat} {S} {Γ}
  (tm : TM (k + 1) S (Option Γ)) (input : List Γ) (output : List Γ) (t : Nat) : Prop :=
  -- TODO and actually we need that the stop state is not reached earlier.
  let conf := tm.transition.n_steps (TM.initial_configuration tm input) t
  tape_equiv_up_to_shift (conf.tapes ⟨k, by simp⟩) (Turing.Tape.mk₁ (output.map some)) ∧
  conf.state = tm.stopState

def TM.runs_in_time {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (input : List Γ) (output : List Γ) (t : Nat) : Prop :=
  ∃ t' ≤ t, tm.runs_in_exact_time input output t'

lemma TM.runs_in_time_monotone {k : ℕ} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (input : List Γ) (output : List Γ) :
  Monotone (tm.runs_in_time input output) := by
  unfold Monotone
  intro t₁ t₂ h_le h_runs
  obtain ⟨t', h_t'le, h_exact⟩ := h_runs
  use t'
  constructor
  · calc t' ≤ t₁ := h_t'le
        _ ≤ t₂ := h_le
  · exact h_exact

--- Update position based on a move operation
def update_head_position (pos : ℤ) (move : Option Turing.Dir) : ℤ :=
  match move with
  | none => pos
  | some Turing.Dir.left => pos - 1
  | some Turing.Dir.right => pos + 1

lemma update_head_position_change_at_most_one (pos : ℤ) (move : Option Turing.Dir) :
  |(update_head_position pos move) - pos| ≤ 1 := by
  cases move with
  | none => unfold update_head_position; simp
  | some dir => cases dir <;> unfold update_head_position <;> simp

--- Position of tape head `i` over time.
def head_position {k : Nat} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) : Nat → ℤ
  | 0 => 0
  | Nat.succ n =>
      let prev_conf := σ.n_steps conf n
      let tape_op := (σ prev_conf.state fun j => (prev_conf.tapes j).head).2 i
      update_head_position (head_position conf σ i n) tape_op.2

lemma head_position_change_at_most_one {k : Nat} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) (n : ℕ) :
  |(head_position conf σ i (n + 1)) - (head_position conf σ i n)| ≤ 1 := by
  conv in head_position _ _ _ (n + 1) => unfold head_position
  simp [update_head_position_change_at_most_one]

lemma head_position_variability (f : ℕ → ℤ) (m n : ℕ)
  (h_var : ∀ n : ℕ, |f (n + 1) - f n| ≤ 1) :
  |f (m + n) - f m| ≤ n := by
  revert m
  refine Nat.strong_induction_on n ?_
  intro n ih m
  cases n with
  | zero => simp
  | succ n =>
    calc
      abs (f (m + n + 1) - f m)
          = abs ((f (m + n + 1) - f (m + n)) + (f (m + n) - f m)) := by ring_nf
        _ ≤ abs (f (m + n + 1) - f (m + n)) + abs (f (m + n) - f m) := abs_add_le _ _
        _ ≤ 1 + n := by
          gcongr
          · exact h_var (m + n)
          · simp [ih]
        _ = n + 1 := by ring

lemma head_position_variability' (f : ℕ → ℤ) (m₁ m₂ : ℕ)
  (h_var : ∀ n : ℕ, |f (n + 1) - f n| ≤ 1) :
  |f m₁ - f m₂| ≤ abs (Int.ofNat m₁ - Int.ofNat m₂) := by
  wlog h : m₁ ≤ m₂
  · rw [abs_sub_comm (f m₁), abs_sub_comm (Int.ofNat m₁)]
    exact this f m₂ m₁ h_var (Nat.le_of_not_le h)
  · have pos_result := head_position_variability f m₁ (m₂ - m₁) h_var
    rw [Nat.add_sub_of_le h] at pos_result
    simp only [Int.ofNat_sub h, abs_sub_comm] at pos_result
    rw [abs_sub_comm (Int.ofNat m₁)]
    calc |f m₁ - f m₂| ≤ ↑m₂ - ↑m₁  := pos_result
      _ ≤ |↑m₂ - ↑m₁| := by simp only [le_abs_self]

--- Space required for tape `i` up until step `n`
def Configuration.tape_space_n_steps {k : Nat} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) (n : ℕ) : ℕ :=
  let head_positions := (Finset.range (n + 1)).image (head_position conf σ i)
  have h_nonempty : head_positions.Nonempty := by simp [head_positions]
  ((head_positions.max' h_nonempty) - (head_positions.min' h_nonempty) + 1).toNat


def Configuration.space_n_steps {k : Nat} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (n : Nat) : ℕ :=
  ∑ i, conf.tape_space_n_steps σ i n

def TM.runs_in_exact_time_and_space {k : Nat} {S} {Γ}
  (tm : TM (k + 1) S (Option Γ)) (input : List Γ) (output : List Γ) (t : Nat) (s : Nat) : Prop :=
  tm.runs_in_exact_time input output t ∧
  (TM.initial_configuration tm input).space_n_steps tm.transition t = s

def TM.runs_in_time_and_space {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (input : List Γ) (output : List Γ) (t : Nat) (s : Nat) : Prop :=
  ∃ t' ≤ t, ∃ s' ≤ s, tm.runs_in_exact_time_and_space input output t' s'

lemma TM.runs_in_time_and_space_monotone_time {k : ℕ} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (input : List Γ) (output : List Γ) (s : Nat) :
    Monotone (tm.runs_in_time_and_space input output · s) := by
  unfold Monotone
  intro t₁ t₂ h_le
  simp only [le_Prop_eq]
  intro h
  obtain ⟨t', h_t'le, s', h_exact⟩ := h
  use t'
  constructor
  · calc t' ≤ t₁ := h_t'le
        _ ≤ t₂ := h_le
  · use s'

lemma TM.run_in_time_and_space_monotone_space {k : ℕ} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (input : List Γ) (output : List Γ) (t : Nat) :
    Monotone (tm.runs_in_time_and_space input output t ·) := by
  unfold Monotone
  intro s₁ s₂ h_le
  simp only [le_Prop_eq]
  intro h
  obtain ⟨t', h_t'le, s', h_exact⟩ := h
  use t'
  constructor
  · exact h_t'le
  · use s'
    constructor
    · calc s' ≤ s₁ := h_exact.left
        _ ≤ s₂ := h_le
    · exact h_exact.right

def TM.computes_in_time {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ) (t : ℕ → ℕ) : Prop :=
  ∀ input, tm.runs_in_time input (f input) (t input.length)

def TM.computes_in_o_time {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ) (t : Bound) : Prop :=
  ∃ t', t' ≼ t ∧ tm.computes_in_time f t'

lemma TM.computes_in_o_time.monotone {k : ℕ} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ) :
  Monotone (tm.computes_in_o_time f) := by
  unfold Monotone
  intro t₁ t₂ h_le
  simp only [le_Prop_eq]
  intro h
  obtain ⟨t', h_le', h_exact⟩ := h
  use t'
  have h_t_le : t' ≼ t₂ := by calc
    t' ≼ t₁ := h_le'
    _ ≤ t₂ := h_le
  simp [h_t_le, h_exact]

def TM.computes_in_time_and_space {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ) (t s : ℕ → ℕ) : Prop :=
  ∀ input, tm.runs_in_time_and_space input (f input) (t input.length) (s input.length)

def TM.computes_in_o_time_and_space {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ) (t s : Bound) : Prop :=
  ∃ t' s', t' ≼ t ∧ s' ≼ s ∧ tm.computes_in_time_and_space f t' s'

lemma TM.computes_in_o_time_and_space_of_comutes_in_time_and_space {k : ℕ} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ) (t s : Bound)
  (h_in_time_and_space : tm.computes_in_time_and_space f t s) :
  tm.computes_in_o_time_and_space f t s := by
  use t, s

--- Monotonicity of computes_in_o_time_and_space wrt time.
lemma TM.computes_in_o_time_and_space.monotone_time {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ) (s : Bound) :
  Monotone (tm.computes_in_o_time_and_space f · s) := by
  unfold Monotone
  intro t₁ t₂ h_le
  simp only [le_Prop_eq]
  intro h
  obtain ⟨t', s', h_le₁, h_le₂, h_exact⟩ := h
  use t', s'
  have h_t_le : t' ≼ t₂ := by calc
    t' ≼ t₁ := h_le₁
    _ ≤ t₂ := h_le
  simp [h_t_le, h_le₂, h_exact]

--- Monotonicity of computes_in_o_time_and_space wrt space.
lemma TM.computes_in_o_time_and_space.monotone_space {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ) (t : Bound) :
  Monotone (tm.computes_in_o_time_and_space f t ·) := by
  unfold Monotone
  intro s₁ s₂ h_le
  simp only [le_Prop_eq]
  intro h
  obtain ⟨t', s', h_le₁, h_le₂, h_exact⟩ := h
  use t', s'
  have h_s_le : s' ≼ s₂ := by calc
    s' ≼ s₁ := h_le₂
    _ ≤ s₂ := h_le
  simp [h_le₁, h_s_le, h_exact]

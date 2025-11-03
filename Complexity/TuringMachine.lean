import Mathlib

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

-- TODO remove
def TM.runs_in_exact_time {k : Nat} {S} {Γ}
  (tm : TM (k + 1) S (Option Γ)) (input : List Γ) (output : List Γ) (t : Nat) : Prop :=
  -- TODO and actually we need that the stop state is not reached earlier.
  let conf := tm.transition.n_steps (TM.initial_configuration tm input) t
  tape_equiv_up_to_shift (conf.tapes ⟨k, by simp⟩) (Turing.Tape.mk₁ (output.map some)) ∧
  conf.state = tm.stopState

-- TODO remove
def TM.runs_in_time {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (input : List Γ) (output : List Γ) (t : Nat) : Prop :=
  ∃ t' ≤ t, tm.runs_in_exact_time input output t'

-- TODO remove
lemma TM.runs_in_time_monotone {k : ℕ} {S} {Γ}
  (tm : TM k.succ S (Option Γ))
  (t₁ t₂ : ℕ)
  (h_le : t₁ ≤ t₂)
  (input : List Γ) (output : List Γ) (h : tm.runs_in_time input output t₁) :
  tm.runs_in_time input output t₂ := by
  obtain ⟨t', h_t'le, h_exact⟩ := h
  use t'
  constructor
  · calc t' ≤ t₁ := h_t'le
        _ ≤ t₂ := h_le
  · exact h_exact

-- TODO remove
def TM.computes_in_o_time {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ) (t : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ input, tm.runs_in_time input (f input) (c * t input.length + c)

-- TODO prove equivalent for computes_in_o_time_and_space
lemma computes_in_o_time_related {k : Nat} {S} {Γ}
  (t₁ : ℕ → ℕ) (t₂ : ℕ → ℕ)
  (h_related : ∃ c : ℕ, t₁ ≤ c * t₂ + c)
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ)
  (h : tm.computes_in_o_time f t₁) :
  tm.computes_in_o_time f t₂ := by
  obtain ⟨c', h_related⟩ := h_related
  obtain ⟨c, h⟩ := h
  unfold TM.computes_in_o_time
  let c'' := c * c' + c
  use c''
  intro input
  let n := input.length
  refine TM.runs_in_time_monotone tm
    (c * (t₁ n) + c) (c'' * (t₂ n) + c'') ?_ input (f input) (h input)
  calc
    c * (t₁ n) + c ≤ c * (c' * (t₂ n) + c') + c := by gcongr; exact h_related n
    _ = (c * c') * (t₂ n) + (c * c' + c) := by ring
    _ ≤ (c * c' + c) * (t₂ n) + (c * c' + c) := by gcongr; exact Nat.le_add_right _ _
    _ = c'' * (t₂ n) + c'' := by rfl

-- TODO remove - replace with definition through computes_in_o_time_and_space
--- Functions computable in deterministic time `t`.
def dtime {Γ} (t : ℕ → ℕ) (f : List Γ → List Γ) : Prop :=
  Finite Γ ∧
  ∃ (k : ℕ) (S : Type) (tm : TM k.succ S (Option Γ)),
    Finite S ∧ tm.computes_in_o_time f t

--- Structure to track position and bounds for a single tape head
structure PositionState where
  pos : ℤ        -- current position of tape head
  min_pos : ℤ    -- minimum position visited
  max_pos : ℤ    -- maximum position visited

--- Update position based on a move operation
def update_position (pos : ℤ) (move : Option Turing.Dir) : ℤ :=
  match move with
  | none => pos
  | some Turing.Dir.left => pos - 1
  | some Turing.Dir.right => pos + 1

--- Update position state after a move operation
def update_position_state (state : PositionState) (move : Option Turing.Dir) : PositionState :=
  let new_pos := update_position state.pos move
  {
    pos := new_pos,
    min_pos := min state.min_pos new_pos,
    max_pos := max state.max_pos new_pos
  }

--- Initial position state (position starts at 0)
def initial_position_state : PositionState :=
  {
    pos := 0,
    min_pos := 0,
    max_pos := 0
  }

--- Compute position state after n steps, inductively
def position_state_n_steps {k : Nat} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) : Nat → (Fin k → PositionState)
  | 0 => fun _ => initial_position_state
  | Nat.succ n =>
      let prev_states := position_state_n_steps σ conf n
      let prev_conf := σ.n_steps conf n
      let (_, tapeOps) := σ prev_conf.state fun i => (prev_conf.tapes i).head
      -- Update position state for each tape based on its move operation
      fun i => update_position_state (prev_states i) (tapeOps i).2

--- Total space complexity: sum over all tapes of (max_pos - min_pos + 1)
def space_from_position_states {k : Nat} (states : Fin k → PositionState) : ℕ :=
  ∑ i, ((states i).max_pos - (states i).min_pos + 1).toNat

--- Space complexity for a configuration after n steps
def Configuration.space_n_steps {k : Nat} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) (n : Nat) : ℕ :=
  space_from_position_states (position_state_n_steps σ conf n)

def TM.runs_in_exact_time_and_space {k : Nat} {S} {Γ}
  (tm : TM (k + 1) S (Option Γ)) (input : List Γ) (output : List Γ) (t : Nat) (s : Nat) : Prop :=
  let conf := tm.transition.n_steps (TM.initial_configuration tm input) t
  tape_equiv_up_to_shift (conf.tapes ⟨k, by simp⟩) (Turing.Tape.mk₁ (output.map some)) ∧
  -- TODO and actually we need that the stop state is not reached earlier.
  conf.state = tm.stopState ∧
  Configuration.space_n_steps tm.transition (TM.initial_configuration tm input) t = s

def TM.runs_in_time_and_space {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (input : List Γ) (output : List Γ) (t : Nat) (s : Nat) : Prop :=
  ∃ t' ≤ t, ∃ s' ≤ s, tm.runs_in_exact_time_and_space input output t' s'

lemma TM.runs_in_time_and_space_monotone_time {k : ℕ} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (input : List Γ) (output : List Γ) (s : Nat) :
    Monotone (fun t => tm.runs_in_time_and_space input output t s) := by
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
    Monotone (fun s => tm.runs_in_time_and_space input output t s) := by
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

structure Bound where
  to_fun : ℕ → ℕ

instance : Coe Bound (ℕ → ℕ) where
  coe f := f.to_fun

--- Big-O-Notation: Function `f` is in `O(g)`.
def bound_le (f g : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, f ≤ c * g + c

def Bound.le (f g : Bound) : Prop := bound_le f g

infix:50 " ≼ " => Bound.le

@[refl]
lemma Bound.le.refl (f : Bound) : le f f := by
  use 1; simp

@[trans]
lemma Bound.le.trans (f g h : Bound)
  (h_fg : le f g) (h_gh : le g h) : le f h := by
  obtain ⟨c₁, h_fg⟩ := h_fg
  obtain ⟨c₂, h_gh⟩ := h_gh
  use c₁ * c₂ + c₁
  intro n
  calc
    f.to_fun n ≤ c₁ * g.to_fun n + c₁ := h_fg n
    _ ≤ c₁ * (c₂ * h.to_fun n + c₂) + c₁ := by gcongr; exact h_gh n
    _ = (c₁ * c₂) * h.to_fun n + (c₁ * c₂ + c₁) := by ring
    _ ≤ (c₁ * c₂ + c₁) * h.to_fun n + (c₁ * c₂ + c₁) := by gcongr; exact Nat.le_add_right _ _

-- Bound.le is a Preorder
instance : Preorder Bound where
  le := Bound.le
  le_refl := Bound.le.refl
  le_trans := Bound.le.trans

--- le_o is a coarse version of ≤
lemma Bound.le.le_of_le {f g : ℕ → ℕ} (h_gh : f ≤ g) : Bound.le ⟨ f ⟩ ⟨ g ⟩ := by
  use 1; intro n; specialize h_gh n;
  calc
    f n ≤ g n := h_gh
    _ ≤ 1 * g n + 1 := by linarith

@[trans]
theorem Bounds.trans_is_bounds_le {f g h : Bound}
    (h_le₁ : f ≼ g) (h_le₂ : g ≤ h) : f ≼ h := by
  have h : g ≼ h := by sorry
  exact Bound.le.trans _ _ _ h_le₁ h

instance : Trans (· ≼ ·) (· ≤ ·) (· ≼ ·) where
  trans := Bounds.trans_is_bounds_le

def Bound.degree (f : Bound) := { g : ℕ → ℕ // Bound.le ⟨ g ⟩ f }

def TM.computes_in_time_and_space {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ) (t s : ℕ → ℕ) : Prop :=
  ∀ input, tm.runs_in_time_and_space input (f input) (t input.length) (s input.length)

def TM.computes_in_o_time_and_space {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ) (t s : Bound) : Prop :=
  ∃ t' s', Bound.le t' t ∧ Bound.le s' s ∧ tm.computes_in_time_and_space f t' s'

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
    _ ≤ t₂ := by sorry
  simp [h_t_le, h_le₂, h_exact]

--- Monotonicity of computes_in_o_time_and_space wrt space.
lemma TM.computes_in_o_time_and_space.monotone_space {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ) (t : Bound) :
  Monotone (tm.computes_in_o_time_and_space f t ·) := by
  sorry

--- Functions computable in deterministic space `s`.
def dspace {Γ} (s : ℕ → ℕ) (f : List Γ → List Γ) : Prop :=
  Finite Γ ∧
  ∃ (k : ℕ) (S : Type) (t : ℕ → ℕ) (tm : TM k.succ S (Option Γ)),
    Finite S ∧ tm.computes_in_o_time_and_space f t s

--- Functions on the natural numbers, computable in deterministic time `t`.
def dtime_nat (t : ℕ → ℕ) (f : ℕ → ℕ) : Prop :=
  ∃ (Γ : Type) (encoder : ℕ → List Γ),
    Function.Bijective encoder ∧
    dtime t (encoder ∘ f ∘ (Function.invFun encoder))

--- Functions on the natural numbers, computable in deterministic space `s`.
def dspace_nat (s : ℕ → ℕ) (f : ℕ → ℕ) : Prop :=
  ∃ (Γ : Type) (encoder : ℕ → List Γ),
    Function.Bijective encoder ∧
    dspace s (encoder ∘ f ∘ (Function.invFun encoder))

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

def tape_equiv_up_to_shift {Γ} [Inhabited Γ]
  (t1 t2 : Turing.Tape Γ) : Prop :=
  ∃ shift : ℕ, ∃ dir, t2 = (Turing.Tape.move dir)^[shift] t1

-- def TM.runs_in_exact_time_and_space {k : Nat} {S} {Γ} [DecidableEq S] [Inhabited Γ]
--   (tm : TM k S Γ) (input : List Γ) (output : List Γ) (t : Nat) (s : Nat) : Prop :=
--   let (conf, output') := tm.run_on_input_for_steps input t
--   output = output' ∧ conf.state = tm.acceptState ∧ conf.space = s

def TM.runs_in_exact_time {k : Nat} {S} {Γ}
  (tm : TM (k + 1) S (Option Γ)) (input : List Γ) (output : List Γ) (t : Nat) : Prop :=
  -- TODO and actually we need that the stop state is not reached earlier.
  let conf := tm.transition.n_steps (TM.initial_configuration tm input) t
  tape_equiv_up_to_shift (conf.tapes ⟨k, by simp⟩) (Turing.Tape.mk₁ (output.map some)) ∧
  conf.state = tm.stopState

-- def TM.runs_in_exact_time_and_space {k : Nat} {S} {Γ} [DecidableEq S] [Inhabited Γ]
--   (tm : TM k S Γ) (input : List Γ) (output : List Γ) (t : Nat) (s : Nat) : Prop :=
--   let (conf, output') := tm.run_on_input_for_steps input t
--   output = output' ∧ conf.state = tm.acceptState ∧ conf.space = s

-- def TM.runs_in_time_and_space {k : Nat} {S} {Γ} [DecidableEq S] [Inhabited Γ]
--   (tm : TM k S Γ) (input : List Γ) (output : List Γ) (t : Nat) (s : Nat) : Prop :=
--   ∃ t' ≤ t,
--   let (conf, output') := tm.run_on_input_for_steps input t'
--   output = output' ∧ conf.state = tm.acceptState ∧ conf.space ≤ s

def TM.runs_in_time {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (input : List Γ) (output : List Γ) (t : Nat) : Prop :=
  ∃ t' ≤ t, tm.runs_in_exact_time input output t'

lemma tm_runs_in_time_monotone {k : ℕ} {S} {Γ}
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

def TM.computes_in_o_time {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ) (t : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ input, tm.runs_in_time input (f input) (c * t input.length + c)

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
  refine tm_runs_in_time_monotone tm
    (c * (t₁ n) + c) (c'' * (t₂ n) + c'') ?_ input (f input) (h input)
  calc
    c * (t₁ n) + c ≤ c * (c' * (t₂ n) + c') + c := by gcongr; exact h_related n
    _ = (c * c') * (t₂ n) + (c * c' + c) := by ring
    _ ≤ (c * c' + c) * (t₂ n) + (c * c' + c) := by gcongr; exact Nat.le_add_right _ _
    _ = c'' * (t₂ n) + c'' := by rfl

-- def computable_in_time_and_space {Γ} [Inhabited Γ]
--   (f : List Γ → List Γ) (t : Nat → Nat) (s : Nat → Nat) : Prop :=
--   ∃ (k : Nat) (st : Nat) (S : Finset (Fin st)) (tm : TM k S Γ),
--     ∀ input, tm.runs_in_time_and_space input (f input) (t input.length) (s input.length)

-- def computable_in_time {Γ} [Inhabited Γ]
--   (f : List Γ → List Γ) (t : Nat → Nat) : Prop :=
--   ∃ (k : Nat) (st : Nat) (tm : TM k (Fin st) Γ),
--     ∀ input, tm.runs_in_time input (f input) (t input.length)

--- Functions computable in deterministic time `t`.
def dtime {Γ} (t : ℕ → ℕ) (f : List Γ → List Γ) : Prop :=
  Finite Γ ∧
  ∃ (k : ℕ) (S : Type) (tm : TM k.succ S (Option Γ)),
    Finite S ∧ tm.computes_in_o_time f t

-- TODO define space complexity

--- Functions on the natural numbers, computable in deterministic time `t`.
def dtime_nat (t : ℕ → ℕ) (f : ℕ → ℕ) : Prop :=
  ∃ (Γ : Type) (encoder : ℕ → List Γ),
    Function.Bijective encoder ∧
    dtime t (encoder ∘ f ∘ (Function.invFun encoder))

lemma dtime_nat_encoder {k : ℕ} {S : Type} {Γ : Type}
  (encoder : ℕ → List Γ) (t : ℕ → ℕ) (f : ℕ → ℕ)
  (h_bij : Function.Bijective encoder)
  (h_Γ_fin : Finite Γ)
  (h_S_fin : Finite S)
  (tm : TM k.succ S (Option Γ))
  (h_time : ∃ c, ∀ n,
    tm.runs_in_time (encoder n) (encoder (f n)) (c * (t (encoder n).length) + c)) :
  dtime_nat t f := by
  use Γ, encoder
  simp [h_bij]
  unfold dtime
  simp [h_Γ_fin]
  obtain ⟨c, htime'⟩ := h_time
  use k, S
  simp [h_S_fin]
  use tm
  unfold TM.computes_in_o_time
  use c
  rw [Function.Surjective.forall h_bij.2]
  intro n
  have hleft : Function.LeftInverse (Function.invFun encoder) encoder :=
    Function.leftInverse_invFun (f := encoder) h_bij.injective
  simpa [(hleft n)] using htime' n

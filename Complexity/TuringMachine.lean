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

@[ext]
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

def TM.initial_configuration {k : Nat} {S} {Γ}
  (tm : TM k S (Option Γ)) (input : List Γ) : Configuration k S (Option Γ) :=
  let firstTape := Turing.Tape.mk₁ (input.map some)
  { state := tm.startState, tapes := fun i => if i.val = 0 then firstTape else default }


@[simp]
lemma TM.initial_configuration_first_tape {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (input : List Γ) :
  (tm.initial_configuration input).tapes 0 = Turing.Tape.mk₁ (input.map some) := by
  simp [TM.initial_configuration]

@[simp]
lemma TM.initial_configuration_other_tapes {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (input : List Γ) (i : Fin k.succ) (h_i_nonzero : i ≠ 0) :
  (TM.initial_configuration tm input).tapes i = default := by
  simp [TM.initial_configuration, h_i_nonzero]

def tape_equiv_up_to_shift {Γ} [Inhabited Γ]
  (t1 t2 : Turing.Tape Γ) : Prop :=
  ∃ shift : ℕ, ∃ dir, t2 = (Turing.Tape.move dir)^[shift] t1

def TM.configurations_on_input {k : Nat} {S} {Γ}
  (tm : TM k S (Option Γ)) (input : List Γ) (t : Nat) : Configuration k S (Option Γ) :=
  tm.transition.step^[t] (TM.initial_configuration tm input)

def TM.stops_and_outputs {k : Nat} {S} {Γ}
  (tm : TM (k + 1) S (Option Γ)) (input : List Γ) (output : List Γ) (t : Nat) : Prop :=
  tape_equiv_up_to_shift
    ((tm.configurations_on_input input t).tapes ⟨k, by simp⟩)
    (Turing.Tape.mk₁ (output.map some)) ∧
  (tm.configurations_on_input input t).state = tm.stopState

def TM.runs_in_exact_time {k : Nat} {S} {Γ}
  (tm : TM (k + 1) S (Option Γ)) (input : List Γ) (output : List Γ) (t : Nat) : Prop :=
  tm.stops_and_outputs input output t ∧
  ∀ t' < t, (tm.configurations_on_input input t').state ≠ tm.stopState

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

-- If a TM stays inert when reaching the stop state, it suffices to show that it stops
-- with the correct output (i.e. we do not need to find the first time step it reaches
-- the stop state).
lemma TM.runs_in_time_of_inert {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (input : List Γ) (output : List Γ) (t : Nat)
  (h_inert : ∀ conf, conf.state = tm.stopState → tm.transition.step conf = conf)
  (h_stops_with_output : tm.stops_and_outputs input output t) :
  tm.runs_in_time input output t := by
  classical
  by_cases h_first : ∀ t' < t, (tm.configurations_on_input input t').state ≠ tm.stopState
  · unfold TM.runs_in_time TM.runs_in_exact_time
    use t
  · simp only [not_forall, not_not, exists_prop] at h_first
    let t' := Nat.find h_first
    have ⟨h_t'_lt_t, h_t'_stops⟩ := Nat.find_spec h_first
    -- Since the machine is inert at the stop state, it stays stopped
    have h_conf_eq (d : ℕ) : tm.configurations_on_input input (t' + d) =
                            tm.configurations_on_input input t' := by
      induction d with
      | zero => simp
      | succ d ih =>
        calc tm.configurations_on_input input (t' + Nat.succ d)
          = tm.configurations_on_input input (Nat.succ (t' + d)) := by rw [Nat.add_succ]
          _ = tm.transition.step (tm.configurations_on_input input (t' + d)) := by
              unfold TM.configurations_on_input
              rw [Function.Commute.self_iterate tm.transition.step]
              simp
          _ = tm.configurations_on_input input t' := by simpa [ih] using h_inert _ h_t'_stops
    have h_stops_at_t' : tm.stops_and_outputs input output t' := by
      have h_t_eq_t'_plus : t = t' + (t - t') := by omega
      unfold TM.stops_and_outputs at *
      rw [← h_conf_eq, ← h_t_eq_t'_plus]
      exact h_stops_with_output
    unfold TM.runs_in_time TM.runs_in_exact_time
    use t'
    refine ⟨Nat.le_of_lt h_t'_lt_t, h_stops_at_t', ?_⟩
    intro t'' h_t''_lt_t'
    have h_min := Nat.find_min h_first h_t''_lt_t'
    simp only [not_and] at h_min
    intro h_eq
    exact h_min (Nat.lt_trans h_t''_lt_t' h_t'_lt_t) h_eq


def head_position_update {k : Nat} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) : ℤ :=
  match ((σ conf.state fun j => (conf.tapes j).head).2 i).2 with
  | none => 0
  | some Turing.Dir.left => -1
  | some Turing.Dir.right => 1

lemma head_position_update_at_most_one {k : ℕ} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) :
  |head_position_update conf σ i| ≤ 1 := by
  unfold head_position_update
  cases ((σ conf.state fun j => (conf.tapes j).head).2 i).2 with
  | none => simp
  | some dir => cases dir <;> simp

--- Position of tape head `i` over time.
def head_position {k : Nat} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) (n : ℕ) : ℤ :=
  -- sum over integers less than n
  ∑ j ∈ Finset.range n, head_position_update (σ.step^[j] conf) σ i

@[simp]
lemma head_position_zero {k : ℕ} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) :
  head_position conf σ i 0 = 0 := by
  rfl

@[simp]
lemma head_position_single_step {k : ℕ} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) :
  head_position conf σ i 1 = head_position_update conf σ i := by
  unfold head_position
  simp

lemma head_position_last_step {k : ℕ} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) (n : ℕ) :
  head_position conf σ i (n + 1) =
    head_position conf σ i n + head_position_update (σ.step^[n] conf) σ i := by
  unfold head_position
  rw [Finset.sum_range_succ]


lemma head_position_add_steps {k : ℕ} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) (n m : ℕ) :
  head_position conf σ i (n + m) =
    head_position conf σ i n + head_position (σ.step^[n] conf) σ i m := by
  unfold head_position
  rw [Finset.sum_range_add]
  simp [← Function.iterate_add_apply, Nat.add_comm]

lemma head_position_change_at_most_one {k : Nat} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) (n : ℕ) :
  |(head_position conf σ i (n + 1)) - (head_position conf σ i n)| ≤ 1 := by
  simp [head_position_add_steps, head_position_update_at_most_one]

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

lemma Configuration.tape_space_n_steps_exists_min {k : Nat} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) (n : ℕ) :
  ∃ min : ℤ,
    (∀ m ≤ n, min ≤ head_position conf σ i m ∧
    head_position conf σ i m < min + (conf.tape_space_n_steps σ i n)) := by
  let head_positions := (Finset.range (n + 1)).image (head_position conf σ i)
  have h_nonempty : head_positions.Nonempty := by simp [head_positions]
  use head_positions.min' h_nonempty
  intro m h_m_le
  constructor
  · refine Finset.min'_le head_positions (head_position conf σ i m) ?_
    apply Finset.mem_image_of_mem
    simp only [Finset.mem_range]
    linarith
  · unfold Configuration.tape_space_n_steps
    have h_max_ge_min : 0 ≤ head_positions.max' h_nonempty -
                            head_positions.min' h_nonempty + 1 := by
      have : head_positions.min' h_nonempty ≤ head_positions.max' h_nonempty + 1 := by
        apply Int.le_add_one
        simp [Finset.max'_mem, Finset.min'_le head_positions]
      linarith
    rw [Int.toNat_of_nonneg h_max_ge_min]
    simp [← Int.add_assoc]
    have h_le := head_positions.le_max' (head_position conf σ i m) (by
      apply Finset.mem_image_of_mem
      simpa [Finset.mem_range] using Nat.lt_add_one_of_le h_m_le)
    linarith

lemma Configuration.tape_space_n_steps.monotone {k : ℕ} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) :
  Monotone (conf.tape_space_n_steps σ i) := by
  intro n₁ n₂ h_le
  apply Int.toNat_le_toNat
  gcongr
  · apply Finset.sup'_mono; refine Finset.image_subset_image ?_; gcongr
  · apply Finset.inf'_mono; refine Finset.image_subset_image ?_; gcongr

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

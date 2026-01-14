import Complexity.TuringMachine
import Complexity.Dyadic
import Complexity.TapeLemmas
import Complexity.AbstractTape
import Complexity.While

import Mathlib

--- A 1-tape Turing machine that moves its head in a given direction
--- once and then halts.
def Routines.move {Γ} [Inhabited Γ]
  (dir : Turing.Dir) :
  TM 1 (Fin 2) Γ :=
  let σ := fun state symbols =>
    match state with
    | 0 => (1, (symbols ·, some dir))
    | 1 => (1, (symbols ·, none))
  TM.mk σ 0 1

lemma Routines.move.inert_after_stop {Γ} [Inhabited Γ]
  (dir : Turing.Dir) :
  (Routines.move (Γ := Γ) dir).inert_after_stop := by
  intro conf h_is_stopped
  ext <;> simp_all [Transition.step, performTapeOps, Routines.move]

lemma Routines.move.semantics {Γ} [Inhabited Γ] [DecidableEq Γ]
  (tape : Turing.Tape Γ)
  (dir : Turing.Dir) :
  (Routines.move dir).transforms (fun _ => tape) (fun _ => Turing.Tape.move dir tape) := by
  let tm := Routines.move (Γ := Γ) dir
  exact TM.transforms_of_inert tm _ _ (move.inert_after_stop dir) ⟨1, rfl⟩

--- A 1-tape Turing machine that moves its head
--- in a given direction until a condition is met.
def move_until {Γ} [Inhabited Γ]
  (dir : Turing.Dir) (stop_condition : Γ → Bool) :=
  Routines.while (¬stop_condition ·) (Routines.move dir)

theorem move_until.right_semantics {Γ} [Inhabited Γ] [DecidableEq Γ]
  (tape : Turing.Tape Γ)
  (stop_condition : Γ → Bool)
  (h_stop : ∃ n : ℕ, stop_condition (tape.nth n)) :
  (move_until .right stop_condition).transforms
    (fun _ => tape)
    (fun _ => tape.move_int (Nat.find h_stop)) := by
  let h_while := Routines.while.semantics
    (¬stop_condition ·)
    (Routines.move .right)
    (fun n => fun i => tape.move_int n)
    (by
      intro i
      have : tape.move_int (↑i + 1) = (tape.move_int ↑i).move .right := by
        simp [← move_int_one]
      simpa [this] using Routines.move.semantics (tape.move_int i) .right
    )
    (by simp [h_stop, Turing.Tape.move_int])
  simpa [move_until, Turing.Tape.move_int] using h_while

theorem move_until.left_semantics {Γ} [Inhabited Γ] [DecidableEq Γ]
  (tape : Turing.Tape Γ)
  (stop_condition : Γ → Bool)
  (h_stop : ∃ n : ℕ, stop_condition (tape.nth (-n))) :
  (move_until .left stop_condition).transforms
    (fun _ => tape)
    (fun _ => tape.move_int (-(Nat.find h_stop))) := by
  let h_while := Routines.while.semantics
    (¬stop_condition ·)
    (Routines.move .left)
    (fun n => fun _ => tape.move_int (-n))
    (by
      intro i
      simp
      have : tape.move_int (-1 + -i) = (tape.move_int (-i)).move .left := by
        simp [← move_int_neg_one, Int.add_comm]
      simpa [this] using Routines.move.semantics (tape.move_int (-i)) .left
    )
    (by simp [h_stop])
  simp at h_while
  simpa [move_until, Turing.Tape.move_int] using h_while

theorem move_until.right_till_separator {Γ} [Inhabited Γ] [DecidableEq Γ]
  (l r₁ r₂ : List Γ)
  (sep : Γ)
  (h_sep : ∀ i, r₁.get i ≠ sep) :
  (move_until .right (fun c => c = sep)).transforms
    (fun _ => Turing.Tape.mk₂ l (r₁ ++ (sep :: r₂)))
    (fun _ => (Turing.Tape.mk₂ l (r₁ ++ (sep :: r₂))).move_int r₁.length) := by
  let tape := Turing.Tape.mk₂ l (r₁ ++ (sep :: r₂))
  have h_stop : ∃ n : ℕ, (fun c => decide (c = sep)) (tape.nth n) := by
    use r₁.length
    simp [tape]
  convert move_until.right_semantics tape (fun c => c = sep) h_stop
  rw [(Nat.find_eq_iff h_stop (m := r₁.length)).mpr]
  constructor
  · simp [tape]
  · intro n h_nlt
    have : tape.nth n = List.get r₁ ⟨n, (by omega)⟩ := by
      simp [tape]
      have : ¬((n : ℤ) < 0) := by omega
      simp [this, List.getElem?_append, h_nlt]
    rw [this]
    simpa using h_sep ⟨n, (by omega)⟩


theorem move_until.left_till_blank {Γ} [Inhabited Γ] [DecidableEq Γ]
  (l : List Γ)
  (n : ℕ)
  (h_nlt : n < l.length)
  (h_non_blank : ∀ i : Fin l.length, i < n → l.get i ≠ default) :
  (move_until .left (fun c => c = default)).transforms
    (fun _ => (Turing.Tape.move .right)^[n] (Turing.Tape.mk₁ l))
    (fun _ => (Turing.Tape.mk₁ l).move .left) := by
  sorry
  -- let tape := Turing.Tape.mk₂ (l₁ ++ (sep :: l₂)) r
  -- have h_stop : ∃ n : ℕ, (fun c => decide (c = sep)) (tape.nth (-n)) := by
  --   use l₁.length
  --   simp [tape]
  -- convert move_until.left_semantics tape (fun c => c = sep) h_stop
  -- rw [(Nat.find_eq_iff h_stop (m := l₁.length)).mpr]
  -- constructor
  -- · simp [tape]
  -- · intro n h_nlt
  --   have : tape.nth n = List.get r₁ ⟨n, (by omega)⟩ := by
  --     simp [tape]
  --     have : ¬((n : ℤ) < 0) := by omega
  --     simp [this, List.getElem?_append, h_nlt]
  --   rw [this]
  --   simpa using h_sep ⟨n, (by omega)⟩

import Mathlib

import Complexity.TuringMachine
import Complexity.Classes

--- Upper space bound for a given time limit, for a single tape.
lemma tape_space_n_steps_linear_bound {k : ℕ} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) (n : ℕ) :
  conf.tape_space_n_steps σ i n ≤ n + 1 := by
  unfold Configuration.tape_space_n_steps
  simp only [Int.toNat_le]
  -- Get max and min exist in the range
  let head_positions := (Finset.range (n + 1)).image (head_position conf σ i)
  have h_nonempty : head_positions.Nonempty := by simp [head_positions]
  have h_max_mem := Finset.max'_mem head_positions h_nonempty
  have h_min_mem := Finset.min'_mem head_positions h_nonempty
  simp only [head_positions, Finset.mem_image, Finset.mem_range] at h_max_mem h_min_mem
  obtain ⟨m₁, hm₁_range, hm₁_eq⟩ := h_max_mem
  obtain ⟨m₂, hm₂_range, hm₂_eq⟩ := h_min_mem
  have min_le_max : head_positions.min' h_nonempty ≤ head_positions.max' h_nonempty := by
    apply Finset.min'_le_max'
  -- Apply head_position_variability'
  have h_var := head_position_change_at_most_one conf σ i
  have pos_bound := head_position_variability' (head_position conf σ i) m₁ m₂ h_var
  rw [hm₁_eq, hm₂_eq] at pos_bound
  -- Both m₁ and m₂ are in range [0, n]
  have hm₁_le : m₁ ≤ n := Nat.lt_succ_iff.mp hm₁_range
  have hm₂_le : m₂ ≤ n := Nat.lt_succ_iff.mp hm₂_range
  have : abs (Int.ofNat m₁ - Int.ofNat m₂) ≤ n := by
    have : abs (Int.ofNat m₁ - Int.ofNat m₂) ≤ max m₁ m₂ := by
      by_cases h : m₁ ≤ m₂
      · rw [← abs_neg, abs_of_nonneg]
        simp [h]
        simpa [Int.sub_nonneg] using h
      · rw [abs_of_nonneg]
        simp
        simp [Int.sub_nonneg]
        let h := Nat.le_of_not_le h
        simp_all only [Int.ofNat_eq_coe]
    omega
  calc
    head_positions.max' h_nonempty - head_positions.min' h_nonempty + 1
        = abs (head_positions.max' h_nonempty - head_positions.min' h_nonempty) + 1 := by
          rw [abs_of_nonneg (by simp [min_le_max])]
      _ ≤ abs (Int.ofNat m₁ - Int.ofNat m₂) + 1 := by gcongr
      _ ≤ ↑n + 1 := by omega

--- Upper space bound for a given time limit.
lemma Configuration.space_n_steps_upper_bound {k : ℕ} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (n : Nat) :
  conf.space_n_steps σ n ≤ k * (n + 1) := by
  calc
    conf.space_n_steps σ n
        = ∑ i, conf.tape_space_n_steps σ i n := by rfl
      _ ≤ ∑ i, (n + 1) := by apply Finset.sum_le_sum; simp [tape_space_n_steps_linear_bound]
      _ = k * (n + 1) := by simp


lemma TM.runs_in_time_and_space_of_runs_in_time {k : ℕ} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (input : List Γ) (output : List Γ) (t : ℕ)
  (h_in_time : tm.runs_in_time input output t) :
  tm.runs_in_time_and_space input output t (k.succ * (t + 1)) := by
  obtain ⟨t', h_t'le, h_exact⟩ := h_in_time
  use t', h_t'le
  use (TM.initial_configuration tm input).space_n_steps tm.transition t'
  unfold TM.runs_in_exact_time_and_space
  simp [h_exact]
  calc
    (tm.initial_configuration input).space_n_steps tm.transition t'
      ≤ k.succ * (t' + 1) := by apply Configuration.space_n_steps_upper_bound
    _ ≤ k.succ * (t + 1) := by gcongr

lemma TM.computes_in_time_and_space_of_computes_in_time {k : Nat} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ) (t : ℕ → ℕ)
  (h_comp : tm.computes_in_time f t) :
  tm.computes_in_time_and_space f t (k.succ * (t + 1)) := by
  intro input
  specialize h_comp input
  exact TM.runs_in_time_and_space_of_runs_in_time tm input (f input) (t input.length) h_comp

lemma TM.computes_in_o_time_and_space_of_computes_in_time {k : ℕ} {S} {Γ}
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ) (t : Bound)
  (h_in_o_time : tm.computes_in_o_time f t) :
  tm.computes_in_o_time_and_space f t t := by
  obtain ⟨t', h_t_le, h_in_time⟩ := h_in_o_time
  use t', ⟨(k.succ * (t' + 1))⟩
  simp [h_t_le]
  constructor
  · calc
      ⟨(k.succ * (t'.to_fun + 1))⟩ ≼ ⟨(t'.to_fun + 1)⟩ := by exact Bounds.mul_le
      _ ≼ ⟨t'.to_fun⟩ := by exact Bounds.add_le
      _ ≼ t := by exact h_t_le
  · exact TM.computes_in_time_and_space_of_computes_in_time tm f t' h_in_time

theorem dtime_in_dspace {Γ} (t : ℕ → ℕ) (f : List Γ → List Γ) :
  dtime t f → dspace t f := by
  intro h
  obtain ⟨k, S, tm, h_Γ_finite, h_S_finite, h_comp⟩ := h
  unfold dspace
  use k, S, t, tm
  simp only [h_Γ_finite, h_S_finite, true_and]
  exact TM.computes_in_o_time_and_space_of_computes_in_time tm f ⟨t⟩ h_comp

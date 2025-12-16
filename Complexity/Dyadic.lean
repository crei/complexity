import Mathlib

def dyadic_decoding_reverse (x : List Bool) : ℕ :=
  match x with
  | [] => 0
  | false :: xs => (dyadic_decoding_reverse xs) * 2 + 1
  | true :: xs => (dyadic_decoding_reverse xs) * 2 + 2

/-- Dyadic encoding of a natural number, but reversed,
i.e. starting with the least significant bit.
-/
def dyadic_encoding_reverse (n : ℕ) : List Bool :=
  if n = 0 then []
  else if Even n then
    true :: dyadic_encoding_reverse (n / 2 - 1)
  else
    false :: dyadic_encoding_reverse ((n - 1) / 2)

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


theorem dyadic_encoding_reverse_prop_one (n : ℕ) :
  dyadic_encoding_reverse (2 * n + 1) = false :: dyadic_encoding_reverse n := by
  conv => rw [dyadic_encoding_reverse]
  simp

theorem dyadic_encoding_reverse_prop_two (n : ℕ) :
  dyadic_encoding_reverse (2 * n + 2) = true :: dyadic_encoding_reverse n := by
  have h : Even (2 * n + 2) := by
    apply Even.add <;> simp
  conv => rw [dyadic_encoding_reverse]
  simp [h]

@[elab_as_elim]
theorem dyadic_induction_on {p : ℕ → Prop} (n : ℕ)
  (h0 : p 0)
  (h1 : ∀ n, p n → p (2 * n + 1))
  (h2 : ∀ n, p n → p (2 * n + 2)) : p n := by
  -- strong induction
  refine Nat.strong_induction_on n ?_; intro n IH
  cases n with
  | zero => exact h0
  | succ m =>
    by_cases hEven : Even m.succ
    · have he : ∃ n', m + 1 = 2 * n' + 2 := by
        simpa [Nat.add_right_cancel_iff, Nat.succ_eq_add_one,
           Nat.even_add_one, Nat.not_even_iff_odd] using hEven
      rcases he with ⟨n', hn'⟩
      rw [hn']
      exact h2 n' (IH n' (by linarith))
    · have h2 : ∃ n', m + 1 = 2 * n' + 1 := by
        simp_all only [Nat.not_even_iff_odd]
        exact hEven
      rcases h2 with ⟨n', hn'⟩
      rw [hn']
      exact h1 n' (IH n' (by linarith))

lemma log2_succ (n : ℕ) : (2 * n + 2 + 1).log2 = (2 * (n + 1)).log2 := by
  calc
    (2 * (n + 1) + 1).log2 = ((2 * (n + 1) + 1) / 2).log2 + 1 := by rw [Nat.log2_def]; simp
      _ = ((2 * (n + 1) + 1).div2).log2 + 1 := by rw [← Nat.div2_val]
      _ = (n + 1).log2 + 1 := by simp [Nat.div2_succ]
      _ = (2 * (n + 1)).log2 := by simp [Nat.log2_two_mul]

theorem dyadic_length (n : ℕ) : (dyadic_encoding n).length = (n + 1).log2 := by
  refine dyadic_induction_on n ?_ ?_ ?_
  · unfold dyadic_encoding; decide
  · intro n IH
    simp only [dyadic_encoding_prop_one, List.length_append, IH, List.length_cons, List.length_nil,
      zero_add]
    rw [← Nat.log2_two_mul]
    · rfl
    · simp
  · intro n IH
    simp only [dyadic_encoding_prop_two, List.length_append, IH, List.length_cons, List.length_nil,
      zero_add]
    rw [← Nat.log2_two_mul] <;> simp [log2_succ]

theorem dyadic_reverse_length (n : ℕ) :
  (dyadic_encoding_reverse n).length = (n + 1).log2 := by
  refine dyadic_induction_on n ?_ ?_ ?_
  · unfold dyadic_encoding_reverse; decide
  · intro n IH
    simp only [dyadic_encoding_reverse_prop_one, List.length_cons, IH]
    rw [← Nat.log2_two_mul]
    · rfl
    · simp
  · intro n IH
    simp only [dyadic_encoding_reverse_prop_two, List.length_cons, IH]
    rw [← Nat.log2_two_mul] <;> simp [log2_succ]

theorem dyadic_bijective (n : ℕ) :
  dyadic_decoding (dyadic_encoding n) = n := by
  refine Nat.strong_induction_on n ?_; intro n IH
  unfold dyadic_decoding at IH
  by_cases hEven : Even n
  · match n with
    | .zero => simp [dyadic_encoding, dyadic_decoding, dyadic_decoding_reverse]
    | .succ m =>
      have h2 : ∃ n', m = 2 * n' + 1 := by
        simpa [Nat.even_add_one, Nat.succ_eq_add_one] using hEven
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

theorem dyadic_encoding_reverse_injective (n : ℕ) :
  dyadic_decoding_reverse (dyadic_encoding_reverse n) = n := by
  refine dyadic_induction_on n ?_ ?_ ?_
  · simp [dyadic_encoding_reverse, dyadic_decoding_reverse]
  · intro n IH
    simp [dyadic_encoding_reverse_prop_one, dyadic_decoding_reverse]
    simp [IH, Nat.mul_comm]
  · intro n IH
    simp [dyadic_encoding_reverse_prop_two, dyadic_decoding_reverse]
    simp [IH, Nat.mul_comm]

theorem dyadic_encoding_reverse_surjective (xs : List Bool) :
  dyadic_encoding_reverse (dyadic_decoding_reverse xs) = xs := by
  induction xs with
  | nil => simp [dyadic_decoding_reverse, dyadic_encoding_reverse]
  | cons b xs IH =>
    cases b
    · simp only [dyadic_decoding_reverse]
      rw [Nat.mul_comm, dyadic_encoding_reverse_prop_one, IH]
    · simp only [dyadic_decoding_reverse]
      rw [Nat.mul_comm, dyadic_encoding_reverse_prop_two, IH]

theorem dyadic_encoding_reverse_bijective : Function.Bijective dyadic_encoding_reverse := by
  constructor
  · exact Function.LeftInverse.injective dyadic_encoding_reverse_injective
  · exact Function.RightInverse.surjective dyadic_encoding_reverse_surjective

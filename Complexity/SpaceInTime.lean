import Mathlib

import Complexity.TuringMachine
import Complexity.Classes
import Complexity.TapeLemmas
import Complexity.AbstractTape

--- Prove that deterministic space is in exponential deterministic time using the
--- pigeonhole principle.

--- A write operation on a tape relative to the initial head position.
structure WriteOperation (Γ) where
  pos : ℤ
  symbol : Γ

def next_write_symbol {k : Nat} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) (i : Fin k) : Γ :=
  ((σ conf.state fun j => (conf.tapes j).head).2 i).1

def write_operation {k : Nat} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) (i : Fin k) (n : ℕ) : WriteOperation Γ :=
  {
    pos := head_position conf σ i n,
    symbol := next_write_symbol σ (σ.n_steps conf n) i
  }

@[simp]
lemma write_operation_pos {k : Nat} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) (i : Fin k) (n : ℕ) :
  (write_operation σ conf i n).pos = head_position conf σ i n := by
  rfl

@[simp]
lemma write_operation_n_step_symbol {k : Nat} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) (i : Fin k) (n : ℕ) :
  (write_operation σ (σ.n_steps conf n) i 0).symbol = (write_operation σ conf i n).symbol := by
  rfl

def Turing.Tape.apply_write_operation {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (op : WriteOperation Γ) : Turing.Tape Γ :=
  tape.write_at op.pos op.symbol

@[simp]
lemma apply_write_operation_move_int {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (op : WriteOperation Γ) (s : ℤ) :
  let op' := { pos := op.pos - s, symbol := op.symbol }
  (tape.apply_write_operation op).move_int s =
    (tape.move_int s).apply_write_operation op' := by
  simp [Turing.Tape.apply_write_operation, write_at_move_int]

def Turing.Tape.apply_write_operations {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) (ops : List (WriteOperation Γ)) : Turing.Tape Γ :=
  ops.foldl apply_write_operation tape

@[simp]
lemma apply_write_operations_cons {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ)
  (op : WriteOperation Γ)
  (ops : List (WriteOperation Γ)) :
  tape.apply_write_operations (op :: ops) =
    (tape.apply_write_operation op).apply_write_operations ops := by
  rfl

@[simp]
lemma apply_write_operations_empty {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ) :
  tape.apply_write_operations [] = tape := by rfl

@[simp]
lemma apply_write_operations_append {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ)
  (ops₁ ops₂ : List (WriteOperation Γ)) :
  tape.apply_write_operations (ops₁ ++ ops₂) =
    (tape.apply_write_operations ops₁).apply_write_operations ops₂ := by
  unfold Turing.Tape.apply_write_operations
  simp [List.foldl_append]

@[simp]
lemma apply_write_operations_all_different {Γ} [Inhabited Γ]
  (tape : Turing.Tape Γ)
  (ops : List (WriteOperation Γ))
  (i : ℤ)
  (h_different : ∀ op ∈ ops, op.pos ≠ i) :
  (tape.apply_write_operations ops).nth i = tape.nth i := by
  induction ops generalizing tape with
  | nil => simp
  | cons op ops ih =>
    simp only [apply_write_operations_cons]
    simp only [List.mem_cons, forall_eq_or_imp] at h_different
    rw [ih (tape.apply_write_operation op) h_different.2]
    unfold Turing.Tape.apply_write_operation
    simp [Turing.Tape.write_at_nth, h_different]

def write_operations_up_to {k : ℕ} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) (i : Fin k) (n : ℕ) :
    List (WriteOperation Γ) :=
  (List.range n).map fun n' => write_operation σ conf i n'

--- A view on a Turing tape where the tape does not move but instead
--- write operations are performed at certain locations.
--- This allows reasoning about how a tape changes without having to tape
--- tape movements into account.
def static_tape_up_to {k : ℕ} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) (i : Fin k) (n : ℕ) : Turing.Tape Γ :=
  (conf.tapes i).apply_write_operations ((List.range n).map fun n' => write_operation σ conf i n')

lemma tape_step_is_write_operations {k : Nat} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) (i : Fin k) :
  (σ.step conf).tapes i = (
      (conf.tapes i).apply_write_operation (write_operation σ conf i 0)
    ).move_int (head_position conf σ i 1) := by
  simp only [head_position_single_step]
  unfold write_operation next_write_symbol Transition.step Turing.Tape.apply_write_operation
    performTapeOps Turing.Tape.write_at head_position_update
  simp only [n_steps_zero, head_position_zero, move_int_zero, neg_zero, Int.reduceNeg]
  match ((σ conf.state fun i ↦ (conf.tapes i).head).2 i).2 with
  | some .left => rfl
  | some .right => rfl
  | none => rfl

lemma n_steps_tapes_eq_static_tape {k : Nat} {S} {Γ} [Inhabited Γ]
  (σ : Transition k S Γ) (conf : Configuration k S Γ) (i : Fin k) (n : ℕ) :
  (σ.n_steps conf n).tapes i =
    (static_tape_up_to σ conf i n).move_int (head_position conf σ i n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold Transition.n_steps static_tape_up_to
    rw [head_position_last_step, ← move_int_move_int, List.range_succ]
    unfold static_tape_up_to at ih
    simp [tape_step_is_write_operations, ih]

def head_position_bounded {k : Nat} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) (n : ℕ) (min : ℤ) (space : ℕ) :=
  ∀ n' ≤ n, min ≤ (head_position conf σ i n') ∧ head_position conf σ i n' < min + space

lemma head_position_bounded_antitone {k : Nat} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (i : Fin k) (min : ℤ) (space : ℕ) :
  Antitone (head_position_bounded conf σ i · min space) :=
  fun _ _ h_le h_forall _ h_n'_le => h_forall _ (Nat.le_trans h_n'_le h_le)

lemma tape_write_ops_encard {Γ} [Inhabited Γ] [Fintype Γ]
  (tape : Turing.Tape Γ)
  (ops_set : Set (List (WriteOperation Γ))) :
  { tape.apply_write_operations ops | ops ∈ ops_set }.encard ≤
    ops_set.encard := by
  apply Set.encard_image_le

def ops_bounded {Γ} [Fintype Γ] (ops : List (WriteOperation Γ)) (min : ℤ) (space : ℕ) :=
  ∀ op ∈ ops, min ≤ op.pos ∧ op.pos < min + space

def tapes_bounded {Γ} [Inhabited Γ] [Fintype Γ]
  (tape : Turing.Tape Γ) (min : ℤ) (space : ℕ) :=
  { t | ∃ ops, ops_bounded ops min space ∧ t = tape.apply_write_operations ops }

def bounded_tapes_to_gamma_of_space {Γ} [Inhabited Γ] [Fintype Γ]
  (tape : Turing.Tape Γ) (min : ℤ) (space : ℕ) :
    tapes_bounded tape min space → Fin space → Γ :=
  fun t i => t.val.nth (min + i)

lemma bounded_tapes_to_gamma_of_space_inj {Γ} [Inhabited Γ] [Fintype Γ]
  (tape : Turing.Tape Γ) (min : ℤ) (space : ℕ) :
  (bounded_tapes_to_gamma_of_space tape min space).Injective := by
  intro ⟨t₁, h_t₁⟩ ⟨t₂, h_t₂⟩ h_eq
  ext i
  by_cases h_inside : (min ≤ i ∧ i < min + space)
  · have h_eq_at := congrFun h_eq ⟨(i - min).toNat, by omega⟩
    simpa [bounded_tapes_to_gamma_of_space, h_inside] using h_eq_at
  · obtain ⟨ops₁, h_ops₁, rfl⟩ := h_t₁
    obtain ⟨ops₂, h_ops₂, rfl⟩ := h_t₂
    rw [apply_write_operations_all_different, apply_write_operations_all_different]
    · intro op h_op; exact fun h => h_inside ⟨h ▸ (h_ops₂ op h_op).1, h ▸ (h_ops₂ op h_op).2⟩
    · intro op h_op; exact fun h => h_inside ⟨h ▸ (h_ops₁ op h_op).1, h ▸ (h_ops₁ op h_op).2⟩

lemma tape_write_ops_bounded_encard {Γ} [Inhabited Γ] [Fintype Γ]
  (tape : Turing.Tape Γ) (min : ℤ) (space : ℕ) :
  ENat.card (tapes_bounded tape min space) ≤ (Fintype.card Γ) ^ space := by
  calc (tapes_bounded tape min space).encard
      ≤ ENat.card (Fin space → Γ) := ENat.card_le_card_of_injective
             (bounded_tapes_to_gamma_of_space_inj tape min space)
    _ = (Fintype.card Γ) ^ space := by simp

lemma tapes_card_of_fixed_tape_card_head_position_card
  {k : ℕ} {S} [Fintype S] {Γ} [Inhabited Γ] [Fintype Γ]
  (σ : Transition k S Γ) (conf₀ : Configuration k S Γ) (n : ℕ)
  (i : Fin k) :
  ((fun n' => (σ.n_steps conf₀ n').tapes i) '' (Finset.range n)).encard ≤
  ((static_tape_up_to σ conf₀ i ·) '' (Finset.range n)).encard *
     ((head_position conf₀ σ i ·) '' (Finset.range n)).encard := by
  simp only [n_steps_tapes_eq_static_tape]
  calc ((fun n' => (static_tape_up_to σ conf₀ i n').move_int (head_position conf₀ σ i n')) ''
          (Finset.range n)).encard
      ≤ ((fun p : Turing.Tape Γ × ℤ => p.1.move_int p.2) ''
          (((static_tape_up_to σ conf₀ i ·) '' (Finset.range n)) ×ˢ
           ((head_position conf₀ σ i ·) '' (Finset.range n)))).encard := by
        apply Set.encard_mono
        intro t ⟨n', hn', h_eq⟩
        refine ⟨(static_tape_up_to σ conf₀ i n', head_position conf₀ σ i n'),
                ⟨⟨n', hn', rfl⟩, ⟨n', hn', rfl⟩⟩, ?_⟩
        simp only [h_eq]
    _ ≤ (((static_tape_up_to σ conf₀ i ·) '' (Finset.range n)) ×ˢ
         ((head_position conf₀ σ i ·) '' (Finset.range n))).encard := Set.encard_image_le ..
    _ = ((static_tape_up_to σ conf₀ i ·) '' (Finset.range n)).encard *
        ((head_position conf₀ σ i ·) '' (Finset.range n)).encard := Set.encard_prod ..

lemma head_position_card_of_head_position_bounded
  {k : ℕ} {S} [Fintype S] {Γ} [Inhabited Γ] [Fintype Γ]
  (σ : Transition k S Γ) (conf₀ : Configuration k S Γ) (n : ℕ)
  (i : Fin k) (min : ℤ) (space : ℕ)
  (h_bounded : head_position_bounded conf₀ σ i n min space) :
  ((head_position conf₀ σ i ·) '' (Finset.range n.succ)).encard ≤ space := by
  set head_positions := (head_position conf₀ σ i ·) '' (Finset.range n.succ)
  have h_bounded_pos : ∀ p ∈ head_positions, min ≤ p ∧ p < min + space := by
    intro p ⟨n', h_n', h_eq⟩
    subst h_eq
    exact h_bounded n' (Finset.mem_range_succ_iff.mp h_n')
  let f : head_positions → Fin space := fun ⟨p, h_p⟩ =>
    ⟨(p - min).toNat, by have := h_bounded_pos p h_p; omega⟩
  have : f.Injective := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ h_eq
    simp only [f, Fin.mk.injEq, Subtype.mk.injEq] at h_eq ⊢
    have ⟨hx1, hx2⟩ := h_bounded_pos x hx
    have ⟨hy1, hy2⟩ := h_bounded_pos y hy
    omega
  calc head_positions.encard ≤ ENat.card (Fin space) := ENat.card_le_card_of_injective this
    _ = space := by simp

lemma ops_bounded_of_head_position_bounded
  {k : ℕ} {S} [Fintype S] {Γ} [Inhabited Γ] [Fintype Γ]
  (σ : Transition k S Γ) (conf₀ : Configuration k S Γ) (n : ℕ)
  (i : Fin k) (min : ℤ) (space : ℕ)
  (h_bounded : head_position_bounded conf₀ σ i n min space) :
  ops_bounded (write_operations_up_to σ conf₀ i n) min space := by
  intro op h_op_elem
  unfold write_operations_up_to at h_op_elem
  simp only [List.mem_map, List.mem_range] at h_op_elem
  obtain ⟨n', h_n'_lt, rfl⟩ := h_op_elem
  simp only [write_operation_pos]
  exact h_bounded n' (Nat.le_of_lt h_n'_lt)

lemma tape_card_of_head_positions_bounded
  {k : ℕ} {S} [Fintype S] {Γ} [Inhabited Γ] [Fintype Γ]
  (σ : Transition k S Γ) (conf₀ : Configuration k S Γ) (n : ℕ)
  (i : Fin k) (min : ℤ) (space : ℕ)
  (h_bounded : head_position_bounded conf₀ σ i n min space) :
  ((·.tapes i) '' ((σ.n_steps conf₀ ·) '' (Finset.range (n.succ)))).encard ≤
      (Fintype.card Γ)^space * space:= by
  have : (·.tapes i) '' ((σ.n_steps conf₀ ·) '' (Finset.range (n.succ))) =
         ((fun n' => (σ.n_steps conf₀ n').tapes i) '' (Finset.range n.succ)) := by
    ext tape
    simp [Set.image_image]
  rw [this]
  calc ((fun n' => (σ.n_steps conf₀ n').tapes i) '' (Finset.range n.succ)).encard
      ≤ ((static_tape_up_to σ conf₀ i ·) '' (Finset.range n.succ)).encard *
        ((head_position conf₀ σ i ·) '' (Finset.range n.succ)).encard :=
          tapes_card_of_fixed_tape_card_head_position_card σ conf₀ n.succ i
    _ ≤ ((static_tape_up_to σ conf₀ i ·) '' (Finset.range n.succ)).encard *
        space := by
          gcongr; exact head_position_card_of_head_position_bounded σ conf₀ n i min space h_bounded
    _ ≤ (tapes_bounded (conf₀.tapes i) min space).encard * space := by
        gcongr
        apply Set.encard_mono
        intro t ⟨n', h_n_le, h_eq⟩
        simp only [static_tape_up_to] at h_eq
        refine ⟨_, ?_, h_eq.symm⟩
        exact ops_bounded_of_head_position_bounded σ conf₀ n' i min space
          (head_position_bounded_antitone _ _ _ _ _ (Finset.mem_range_succ_iff.mp h_n_le) h_bounded)
    _ ≤ (Fintype.card Γ) ^ space * space := by
      gcongr
      exact tape_write_ops_bounded_encard (conf₀.tapes i) min space

lemma encard_pi_prod {α : Type*} {k : ℕ} (s : Fin k → Set α) :
  (Set.pi Set.univ s).encard = ∏ i, (s i).encard := by
  simp only [Set.encard, ENat.card]
  rw [Cardinal.mk_congr (Equiv.Set.univPi s)]
  simp [Cardinal.prod_eq_of_fintype]

lemma tapes_card_of_head_positions_bounded
  {k : ℕ} {S} [Fintype S] {Γ} [Inhabited Γ] [Fintype Γ]
  (σ : Transition k S Γ) (conf₀ : Configuration k S Γ) (n : ℕ)
  (min : Fin k → ℤ) (space : ℕ)
  (h_bounded : ∀ i, head_position_bounded conf₀ σ i n (min i) space) :
  let configs := σ.n_steps conf₀ '' (Finset.range (n.succ))
  ((fun c => (fun i => c.tapes i)) '' configs).encard ≤
      (((Fintype.card Γ)^space) * space)^k := by
  let configs := σ.n_steps conf₀ '' ↑(Finset.range n.succ)
  -- A set of "some" tuples is the subset of the full cartesian product.
  have h_subset : ((fun c i ↦ c.tapes i) '' configs) ⊆
    { f : Fin k → _ | ∀ i, ∃ c ∈ configs, (c.tapes i) = f i } := by
    calc (fun c i ↦ c.tapes i) '' configs
        = { f : Fin k → _ | ∃ c ∈ configs, ∀ i, (c.tapes i) = f i } := by
          unfold Set.image
          conv in (∀ i, (_ : Fin k → _) _ = _) => rw [← funext_iff]
      _ ⊆ {f | ∀ (i : Fin k), ∃ c ∈ configs, c.tapes i = f i} := by
        intro f ⟨c, h_f_el⟩ i
        use c
        simp_all
  let tapes := fun i => { c.tapes i | c ∈ configs }
  have h_tapes_card (i : Fin k) : (tapes i).encard ≤ ((Fintype.card Γ) ^ space * space) :=
    tape_card_of_head_positions_bounded σ conf₀ n i (min i) space (h_bounded i)
  calc ((fun c => (fun i => c.tapes i)) '' configs).encard
      ≤ { f : Fin k → (Turing.Tape Γ) | ∀ i, ∃ c ∈ configs, (c.tapes i) = f i }.encard := by
        apply Set.encard_mono h_subset
    _ = (Set.pi Set.univ tapes).encard := by
        unfold Set.univ Set.pi tapes; simp
    _ = ∏ i, (tapes i).encard := by apply encard_pi_prod
    _ ≤ ∏ i : Fin k, ↑((Fintype.card Γ) ^ space * space) := by
        apply Finset.prod_le_prod
        · intro i _; simp
        · intro i _; exact h_tapes_card i
    _ ≤ ((Fintype.card Γ) ^ space * space) ^ k := by
      simp [Finset.prod_const, Fintype.card_fin]


lemma configuration_card_of_head_positions_bounded
  {k : ℕ} {S} [Fintype S] {Γ} [Inhabited Γ] [Fintype Γ]
  (σ : Transition k S Γ) (conf₀ : Configuration k S Γ) (n : ℕ)
  (min : Fin k → ℤ) (space : ℕ)
  (h_bounded : ∀ i, head_position_bounded conf₀ σ i n (min i) space) :
  (σ.n_steps conf₀ '' (Finset.range (n.succ))).encard ≤
      (Fintype.card S) * (((Fintype.card Γ)^space) * space)^k := by
  let configs := σ.n_steps conf₀ '' (Finset.range (n.succ))
  have h_tape : ∏ i, ({ c.tapes i | c ∈ configs}.encard) ≤ ((Fintype.card Γ)^space * space)^k := by
    calc ∏ i, ((·.tapes i) '' configs).encard
        ≤ ∏ _, (((Fintype.card Γ)^space * space : ℕ) : ℕ∞) :=
          Finset.prod_le_prod (fun _ _ => zero_le _)
            (fun i _ => tape_card_of_head_positions_bounded _ _ _ _ (min i) _ (h_bounded i))
      _ = (((Fintype.card Γ)^space * space))^k := by simp [Finset.prod_const]
  calc configs.encard
      = ((fun c => (c.state, fun i => c.tapes i)) '' configs).encard := by
        refine (Set.InjOn.encard_image ?_).symm
        intro c₁ _ c₂ _ h_eq
        simp only [Prod.mk.injEq] at h_eq
        ext <;> simp [h_eq]
    _ ≤ (((·.state) '' configs) ×ˢ (((fun c => (fun i => c.tapes i)) '' configs))).encard := by
        apply Set.encard_le_encard
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha, rfl⟩, ⟨a, ha, rfl⟩⟩
    _ = ((·.state) '' configs).encard * ((fun c => (fun i => c.tapes i)) '' configs).encard :=
        Set.encard_prod
    _ = ((·.state) '' configs).encard * { f | ∃ c ∈ configs, (fun i => c.tapes i) = f }.encard := by
        unfold Set.image; simp
    _ ≤ (Fintype.card S) * { f | ∃ c ∈ configs, (fun i => c.tapes i) = f }.encard := by
        gcongr
        calc ((·.state) '' configs).encard
          ≤ (Set.univ : Set S).encard := Set.encard_mono (by simp)
        _ = Fintype.card S := by simp
    _ ≤ (Fintype.card S) * ((Fintype.card Γ)^space * space)^k := by
        gcongr
        exact tapes_card_of_head_positions_bounded σ conf₀ n min space h_bounded

--- If we have more configurations than the bound, by the pigeonhole principle,
--- some must repeat
theorem configuration_repeat_in_bounded_space
  {k : ℕ} {S} [Fintype S] {Γ} [Inhabited Γ] [Fintype Γ]
  (σ : Transition k S Γ) (conf₀ : Configuration k S Γ) (n : ℕ)
  (min : Fin k → ℤ) (space : ℕ)
  (h_bounded : ∀ i, head_position_bounded conf₀ σ i n (min i) space)
  (h_large : n > Fintype.card S * ((Fintype.card Γ ^ space) * space) ^ k) :
  ∃ i₁ i₂, i₁ < i₂ ∧ i₂ ≤ n ∧ σ.n_steps conf₀ i₁ = σ.n_steps conf₀ i₂ := by
  let configs := σ.n_steps conf₀ '' (Finset.range (n.succ) : Set ℕ)
  have h_lt : configs.encard < (n.succ : ℕ∞) := by
    calc configs.encard
        ≤ (Fintype.card S) * (((Fintype.card Γ)^space) * space)^k :=
          configuration_card_of_head_positions_bounded σ conf₀ n min space h_bounded
      _ < n.succ := by norm_cast; omega
  have h_finite : configs.Finite := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp h_lt.ne_top
    exact Set.finite_of_encard_eq_coe hm.symm
  let img := h_finite.toFinset
  have h_card_lt : img.card < (Finset.range (n.succ)).card := by
    rw [Finset.card_range]
    have : (↑img.card : ℕ∞) = configs.encard := by
      rw [← Set.Finite.coe_toFinset h_finite, Set.encard_coe_eq_coe_finsetCard]
    exact Nat.cast_lt.mp (this ▸ h_lt)
  have h_maps : Set.MapsTo (σ.n_steps conf₀) (Finset.range (n.succ) : Set ℕ) (img : Set _) := by
    intro x hx; rw [Set.Finite.coe_toFinset]; exact ⟨x, hx, rfl⟩
  obtain ⟨i₁, hi₁, i₂, hi₂, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_card_lt h_maps
  simp only [Finset.mem_range] at hi₁ hi₂
  obtain h | h := hne.lt_or_gt
  · exact ⟨i₁, i₂, h, by omega, heq⟩
  · exact ⟨i₂, i₁, h, by omega, heq.symm⟩

-- If a computation reaches an accepting state within bounded space,
-- it reaches it within at most |S| × |Γ|^(k×space) steps
theorem accepting_state_reached_in_bounded_steps
  {k : ℕ} {S} [Fintype S] {Γ} [Inhabited Γ] [Fintype Γ]
  (σ : Transition k S Γ) (conf₀ : Configuration k S Γ) (is_accepting : S → Bool)
  (min : Fin k → ℤ) (space : ℕ)
  (n : ℕ) (h_accepting : is_accepting (σ.n_steps conf₀ n).state = true)
  (h_bounded : ∀ i, head_position_bounded conf₀ σ i n (min i) space)
  (h_first : ∀ i < n, is_accepting (σ.n_steps conf₀ i).state = false) :
  n ≤ Fintype.card S * ((Fintype.card Γ ^ space) * space) ^ k := by
  by_contra h_large; push_neg at h_large
  obtain ⟨i₁, i₂, h_lt, hi₂_le, h_eq⟩ :=
    configuration_repeat_in_bounded_space σ conf₀ n min space h_bounded h_large
  have hi₂_lt_n : i₂ < n := Nat.lt_of_le_of_ne hi₂_le (fun h => by
    subst h
    have : is_accepting (σ.n_steps conf₀ i₁).state = false := h_first i₁ (by omega)
    rw [← h_eq] at h_accepting
    rw [this] at h_accepting
    trivial)
  have h_eq' : σ.n_steps conf₀ (i₁ + (n - i₂)) = σ.n_steps conf₀ n := by
    rw [n_steps_addition, h_eq, ← n_steps_addition]; congr 1; omega
  have : is_accepting (σ.n_steps conf₀ (i₁ + (n - i₂))).state = false :=
    h_first (i₁ + (n - i₂)) (by omega)
  rw [← h_eq'] at h_accepting
  rw [this] at h_accepting
  trivial

-- Helper lemma: If a TM computes with time/space bounds, head positions are bounded
lemma head_position_bounded_of_tape_space_n_steps
  {k : ℕ} {S} [Fintype S] {Γ} [Inhabited Γ] [Fintype Γ]
  (σ : Transition k S Γ)
  (conf₀ : Configuration k S Γ)
  (t : ℕ)
  (i : Fin k) :
  ∃ min, head_position_bounded conf₀ σ i t min (conf₀.tape_space_n_steps σ i t) := by
  let s := conf₀.tape_space_n_steps σ i t
  obtain ⟨min, h_min⟩ := Configuration.tape_space_n_steps_exists_min conf₀ σ i t
  use min
  exact h_min

lemma accepting_state_reached_in_time_of_bounded_space
  {k : ℕ} {S} [Fintype S] {Γ} [Inhabited Γ] [Fintype Γ]
  (σ : Transition k S Γ)
  (conf₀ : Configuration k S Γ)
  (t s : ℕ)
  (stopState : S)
  (h_stops : (σ.n_steps conf₀ t).state = stopState)
  (h_space : ∀ i, (conf₀.tape_space_n_steps σ i t) ≤ s)
  (h_first : ∀ i < t, (σ.n_steps conf₀ i).state ≠ stopState) :
  t ≤ Fintype.card S * ((Fintype.card Γ ^ s) * s) ^ k := by
  -- Get the minimum head position for each tape
  let min := fun i => Classical.choose (head_position_bounded_of_tape_space_n_steps σ conf₀ t i)
  have h_bounded : ∀ i, head_position_bounded
      conf₀ σ i t (min i) (conf₀.tape_space_n_steps σ i t) := by
    intro i
    exact Classical.choose_spec (head_position_bounded_of_tape_space_n_steps σ conf₀ t i)
  -- Strengthen the bound using h_space
  have h_bounded' : ∀ i, head_position_bounded conf₀ σ i t (min i) s := by
    intro i n' h_n'_le
    obtain ⟨h_min, h_max⟩ := h_bounded i n' h_n'_le
    constructor
    · exact h_min
    · calc head_position conf₀ σ i n'
        < min i + conf₀.tape_space_n_steps σ i t := h_max
      _ ≤ min i + s := by gcongr; exact h_space i
  -- Apply accepting_state_reached_in_bounded_steps
  classical
  let is_accepting := fun state => decide (state = stopState)
  have h_accepting : is_accepting (σ.n_steps conf₀ t).state = true := by
    simp [is_accepting, h_stops]
  have h_first' : ∀ i < t, is_accepting (σ.n_steps conf₀ i).state = false := by
    intro i hi
    simp only [decide_eq_false_iff_not, is_accepting]
    intro h_eq
    exact h_first i hi h_eq
  exact accepting_state_reached_in_bounded_steps
    σ conf₀ is_accepting min s t h_accepting h_bounded' h_first'

lemma tape_space_le_total_space
  {k : ℕ} {S} {Γ} [Inhabited Γ]
  (conf : Configuration k S Γ) (σ : Transition k S Γ) (n : ℕ) :
  ∀ i, conf.tape_space_n_steps σ i n ≤ conf.space_n_steps σ n := by
  intro i
  calc conf.tape_space_n_steps σ i n
      ≤ ∑ j, conf.tape_space_n_steps σ j n := by
        have : ∑ j ∈ ({i} : Finset (Fin k)),
            conf.tape_space_n_steps σ j n = conf.tape_space_n_steps σ i n := by
          simp [Finset.sum_singleton]
        rw [← this]
        apply Finset.sum_le_sum_of_subset
        intro x hx
        exact Finset.mem_univ x
    _ = conf.space_n_steps σ n := rfl

lemma accepting_state_reached_in_time_of_total_space
  {k : ℕ} {S} [Fintype S] {Γ} [Inhabited Γ] [Fintype Γ]
  (σ : Transition k S Γ)
  (conf₀ : Configuration k S Γ)
  (t : ℕ)
  (stopState : S)
  (h_stops : (σ.n_steps conf₀ t).state = stopState)
  (h_first : ∀ i < t, (σ.n_steps conf₀ i).state ≠ stopState) :
  t ≤ Fintype.card S *
    ((Fintype.card Γ ^ (conf₀.space_n_steps σ t)) * (conf₀.space_n_steps σ t)) ^ k := by
  apply accepting_state_reached_in_time_of_bounded_space
    σ conf₀ t (conf₀.space_n_steps σ t) stopState h_stops _ h_first
  exact tape_space_le_total_space conf₀ σ t

lemma TM.runs_in_exp_time_of_runs_in_time_and_space
  {k : ℕ} {S} [Fintype S] {Γ} [Inhabited Γ] [Fintype Γ]
  (tm : TM k.succ S (Option Γ)) (input output : List Γ)
  (t s : ℕ)
  (h_run : tm.runs_in_exact_time_and_space input output t s) :
  t ≤ (Fintype.card S * ((Fintype.card (Option Γ) ^ s) * s) ^ k.succ) := by
  obtain ⟨⟨⟨h_tape, h_stops⟩, h_first⟩, h_space⟩ := h_run
  simpa [h_space] using accepting_state_reached_in_time_of_total_space
      tm.transition (TM.initial_configuration tm input) t tm.stopState h_stops h_first

lemma TM.computes_in_exp_time_of_computes_in_time_and_space
  {k : ℕ} {S} [Fintype S] {Γ} [Inhabited Γ] [Fintype Γ]
  (tm : TM k.succ S (Option Γ)) (f : List Γ → List Γ)
  (t s : ℕ → ℕ)
  (h_comp : tm.computes_in_time_and_space f t s) :
  tm.computes_in_time f
    (fun n => Fintype.card S * ((Fintype.card (Option Γ) ^ (s n)) * (s n)) ^ k.succ) := by
  intro input
  specialize h_comp input
  obtain ⟨t', h_t'_le, s', h_s'_le, h_runs⟩ := h_comp
  let h_t'_bounded := tm.runs_in_exp_time_of_runs_in_time_and_space input (f input) t' s' h_runs
  use t'
  obtain ⟨h_time, h_space⟩ := h_runs
  constructor
  · calc t'
      ≤ Fintype.card S * ((Fintype.card (Option Γ) ^ s') * s') ^ k.succ := h_t'_bounded
    _ ≤ Fintype.card S *
          ((Fintype.card (Option Γ) ^ (s input.length)) * (s input.length)) ^ k.succ := by
        gcongr; simp
  · exact h_time

lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
    calc m.succ
      ≤ 2 ^ m + 2 ^ m := by linarith [ih, h1]
    _ = 2 ^ m.succ := by ring_nf; rfl

lemma exponential_bound {k : ℕ} {S} [Fintype S] {Γ} [Fintype Γ] [Inhabited Γ] (s : ℕ → ℕ) :
  ∃ c₁ c₂, ∀ n, Fintype.card S * (Fintype.card (Option Γ) ^ (s n) * (s n)) ^ k.succ ≤
    c₁ * 2^(c₂ * (s n)) + c₁ := by
  use Fintype.card S, Fintype.card (Option Γ) * k.succ + k.succ
  intro n
  by_cases h_s_zero : s n = 0
  · simp_all
  · have h_le : (Fintype.card (Option Γ) ^ s n * s n) ^ k.succ
        ≤ 2 ^ ((Fintype.card (Option Γ) * k.succ + k.succ) * s n) := by
      calc (Fintype.card (Option Γ) ^ s n * s n) ^ k.succ
          = Fintype.card (Option Γ) ^ (k.succ * s n) * (s n) ^ k.succ := by ring
        _ ≤ Fintype.card (Option Γ) ^ (k.succ * s n) * (2 ^ s n) ^ k.succ := by
            gcongr
            exact nat_le_two_pow (s n)
        _ = Fintype.card (Option Γ) ^ (k.succ * s n) * 2 ^ (k.succ * s n) := by
            rw [← Nat.pow_mul]; ring
        _ ≤ 2 ^ (Fintype.card (Option Γ) * k.succ * s n) * 2 ^ (k.succ * s n) := by
            apply Nat.mul_le_mul_right
            trans
            · exact Nat.pow_le_pow_left (nat_le_two_pow _) _
            · ring_nf; linarith
        _ = 2 ^ (Fintype.card (Option Γ) * k.succ * s n + k.succ * s n) := by
            rw [← Nat.pow_add]
        _ = 2 ^ ((Fintype.card (Option Γ) * k.succ + k.succ) * s n) := by
            congr 1; ring
    calc Fintype.card S * (Fintype.card (Option Γ) ^ s n * s n) ^ k.succ
        ≤ Fintype.card S * 2 ^ ((Fintype.card (Option Γ) * k.succ + k.succ) * s n) := by
          gcongr
      _ ≤ Fintype.card S * 2 ^ ((Fintype.card (Option Γ) * k.succ + k.succ) * s n) +
            Fintype.card S := by
          apply Nat.le_add_right

theorem dspace_in_exp_dtime {Γ} [Inhabited Γ] (s : ℕ → ℕ) (f : List Γ → List Γ)
  (h_dspace : dspace s f) :
  ∃ c : ℕ, dtime (fun n => 2^(c * (s n))) f := by
  obtain ⟨k, S, t, tm, h_fin_Γ, h_fin_S, h_comp⟩ := h_dspace
  obtain ⟨t', s', h_t_le, h_s_le, h_exact⟩ := h_comp
  have : Fintype S := Fintype.ofFinite S
  have : Fintype Γ := Fintype.ofFinite Γ
  obtain ⟨c₁, c₂, h_bound⟩ := exponential_bound (k := k) (S := S) (Γ := Γ) s'.to_fun
  obtain ⟨c_s, h_s_bound⟩ := h_s_le
  use c₂ * c_s, k, S, tm
  simp only [h_fin_Γ, h_fin_S, true_and]
  use ⟨fun n => c₁ * 2^(c₂ * (s'.to_fun n)) + c₁⟩
  constructor
  · calc ⟨fun n => c₁ * 2^(c₂ * s'.to_fun n) + c₁⟩
      ≼ ⟨fun n => 2^(c₂ * s'.to_fun n)⟩ := by
          trans ⟨fun n => c₁ * 2^(c₂ * s'.to_fun n)⟩
          · exact Bounds.add_le
          · exact Bounds.mul_le
    _ ≼ ⟨fun n => 2^(c₂ * c_s * s n)⟩ := by
          use 2^(c₂ * c_s)
          intro n
          have : s'.to_fun n ≤ c_s * s n + c_s := h_s_bound n
          calc 2^(c₂ * s'.to_fun n)
            ≤ 2^(c₂ * (c_s * s n + c_s)) := by
                apply Nat.pow_le_pow_right (by omega)
                gcongr
          _ = 2^(c₂ * c_s) * 2^(c₂ * c_s * s n) := by ring
          _ ≤ 2^(c₂ * c_s) * 2^(c₂ * c_s * s n) + 2^(c₂ * c_s) := Nat.le_add_right _ _
  · intro input
    have h_time := TM.computes_in_exp_time_of_computes_in_time_and_space tm f t' s' h_exact
    obtain ⟨t_actual, h_t_bound, h_exact_time⟩ := h_time input
    use t_actual
    constructor
    · calc t_actual
        ≤ Fintype.card S * ((Fintype.card (Option Γ) ^ s'.to_fun input.length) *
            (s'.to_fun input.length)) ^ k.succ := h_t_bound
      _ ≤ c₁ * 2^(c₂ * s'.to_fun input.length) + c₁ := h_bound input.length
    · exact h_exact_time

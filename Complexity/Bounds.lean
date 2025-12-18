import Mathlib

--- A resource bound in terms of a function from ℕ to ℕ
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
lemma Bound.le.refl (f : Bound) : f ≼ f := by
  use 1; simp

@[trans]
lemma Bound.le.trans (f g h : Bound)
  (h_fg : f ≼ g) (h_gh : g ≼ h) : f ≼ h := by
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
  exact Bound.le.trans _ _ _ h_le₁ h_le₂

lemma Bounds.mul_le {f : ℕ → ℕ} {c : ℕ} : ⟨c * f⟩ ≼ ⟨f⟩ := by
  use c
  simp

lemma Bounds.add_le {f : ℕ → ℕ} {c : ℕ} : ⟨f + c⟩ ≼ ⟨f⟩ := by
  use c + 1
  intro n
  simp only [Pi.add_apply, Pi.natCast_apply, Nat.cast_id, Nat.cast_add, Nat.cast_one, Pi.mul_apply,
    Pi.one_apply]
  have hf_le : f n ≤ (c + 1) * f n := by exact Nat.le_mul_of_pos_left _ (by omega)
  omega

lemma Bounds.le_add {f : ℕ → ℕ} {c : ℕ} : ⟨f⟩ ≼ ⟨f + c⟩ := by
  use 1
  intro n
  simp only [Pi.add_apply, Pi.natCast_apply, Nat.cast_id, Pi.mul_apply]
  omega

lemma Bounds.le_mul {f : ℕ → ℕ} {c : ℕ} (h : c ≠ 0) : ⟨f⟩ ≼ ⟨c * f⟩ := by
  use 1
  intro n
  dsimp
  calc f n ≤ c * f n := Nat.le_mul_of_pos_left (f n) (Nat.pos_of_ne_zero h)
    _ ≤ 1 * (c * f n) + 1 := by omega

instance : Trans (· ≼ ·) (· ≤ ·) (· ≼ ·) where
  trans := Bounds.trans_is_bounds_le

instance : Trans (· ≼ ·) (· ≼ ·) (· ≼ ·) where
  trans := Bounds.trans_is_bounds_le

def Bound.degree (f : ℕ → ℕ) : Set (ℕ → ℕ) :=
  { g : ℕ → ℕ | Bound.le ⟨g⟩ ⟨f⟩ }

@[simp]
lemma degree_add_eq_degree {f : ℕ → ℕ} {c₁ : ℕ} :
  Bound.degree (fun n ↦ (f n) + c₁) = Bound.degree f := by
  ext g
  simp only [Bound.degree, Set.mem_setOf_eq]
  constructor
  · intro hg
    exact Bound.le.trans ⟨g⟩ ⟨f + c₁⟩ ⟨f⟩ hg Bounds.add_le
  · intro hg
    exact Bound.le.trans ⟨g⟩ ⟨f⟩ ⟨f + c₁⟩ hg Bounds.le_add


@[simp]
lemma degree_mul_eq_degree {f : ℕ → ℕ} {c₁ : ℕ} {h_not_zero : c₁ ≠ 0} :
  Bound.degree (fun n ↦ c₁ * (f n)) = Bound.degree f := by
  ext g
  simp only [Bound.degree, Set.mem_setOf_eq]
  constructor
  · intro hg
    exact Bound.le.trans ⟨g⟩ ⟨c₁ * f⟩ ⟨f⟩ hg Bounds.mul_le
  · intro hg
    exact Bound.le.trans ⟨g⟩ ⟨f⟩ ⟨c₁ * f⟩ hg (Bounds.le_mul h_not_zero)


@[simp]
lemma Bound.le_iff_degree_subset_degree {f g : ℕ → ℕ} :
  ⟨f⟩ ≼ ⟨g⟩ ↔ Bound.degree f ⊆ Bound.degree g := by
  constructor
  · intro hfg h hhf
    exact Bound.le.trans ⟨h⟩ ⟨f⟩ ⟨g⟩ hhf hfg
  · intro h_subset
    apply h_subset
    use 1
    intro n
    dsimp
    omega

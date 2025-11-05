import Complexity.TuringMachine

--- Functions computable in deterministic time `t`.
def dtime {Γ} (t : ℕ → ℕ) (f : List Γ → List Γ) : Prop :=
  ∃ (k : ℕ) (S : Type) (tm : TM k.succ S (Option Γ)),
    Finite Γ ∧ Finite S ∧ tm.computes_in_o_time f ⟨t⟩

--- Functions computable in deterministic space `s`.
def dspace {Γ} (s : ℕ → ℕ) (f : List Γ → List Γ) : Prop :=
  ∃ (k : ℕ) (S : Type) (t : ℕ → ℕ) (tm : TM k.succ S (Option Γ)),
    Finite Γ ∧ Finite S ∧ tm.computes_in_o_time_and_space f ⟨t⟩ ⟨s⟩

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

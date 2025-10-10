
-- theorem id_is_computable_in_constant_time_and_space :
--   (nat_function_computable_in_time_and_space (fun x => x) (fun n => 1) (fun n => 1)) := by
--   let encoder : ℕ → List Bool := fun n =>
--     if n = 0 then [] else List.replicate (n - 1) true ++ [false]
--   sorry

-- --- TODO continue with defining:
-- -- computes function f in time t and space s
-- -- and then have a theorem for function composition
-- -- have a theorem for getting an accepting TM into a state where it clears all
-- -- tape cells
-- -- show that Nat.succ is computable in constant time and space
-- -- and then also have a theorem for writing the output into a work tape.



-- -- TODO time bound is probably better
-- -- TODO the parts with the empty symbol do not work.
-- theorem succ_is_in_constant_space :
--   (nat_function_computable_in_time_and_space Nat.succ (fun n => n) (fun n => 1)) := by
--   let encoder := dyadic_encoding -- actually use reverse dyadic coding
--   let decoder := dyadic_decoding -- actually use reverse dyadic coding
--   let k := 0
--   let st := 3
--   sorry
--   -- use encoder, decoder, hdec, k, st, S, tm
--   -- intro n
--   -- have hsteps : n + 2 ≤ n + 2 := by linarith
--   -- use n + 2, hsteps
--   -- simp [TM.runs_in_time_and_space]
--   -- constructor
--   -- · simp [tm.run]
--   --   induction n with
--   --   | zero => simp [encoder]
--   --   | succ m ih =>


-- inductive TM.reachable_in_time {k : Nat} {S} {Γ} [DecidableEq S] [Inhabited Γ]
--   (tm : TM k S Γ) : Configuration k S Γ → Configuration k S Γ → Nat → Prop where
--   | zero (σ : Configuration k S Γ) : TM.reachable_in_time tm σ σ 0
--   | succ (σ₁ σ₂ : Configuration k S Γ) (t : Nat) :
--       TM.reachable_in_time tm σ₁ σ₂ t →
--       TM.reachable_in_time tm σ₁ (tm.step σ₂).1 (t + 1)

-- -- TODO the input should be over a subset of Γ
-- def TM.accepts_in_exact_time_with_final_configuration { k: Nat } {S} {Γ} [ DecidableEq S ] (tm : TM k S Γ) (input : List Γ) (t : Nat) (conf : Configuration k S Γ) : Prop :=
--   let σ₀ := TM.initial_configuration tm input
--   conf.state = tm.acceptState ∧ TM.reachable_in_time tm σ₀ conf t

-- def TM.accepts_in_exact_time { k: Nat } {S} {Γ} [ DecidableEq S ] (tm : TM k S Γ) (input : List Γ) (t : Nat) : Prop :=
--   ∃ σ, TM.accepts_in_exact_time_with_final_configuration tm input t σ

-- def TM.accepts_in_time { k: Nat } {S} {Γ} [ DecidableEq S ] (tm : TM k S Γ) (input : List Γ) (t : Nat) : Prop :=
--   ∃ t' ≤ t, tm.accepts_in_exact_time input t'

-- def TM.accepts_language_in_time { k : Nat } {S} {Γ} [ DecidableEq S ] (tm : TM k S Γ) (L : List (List Γ)) (t : Nat → Nat) : Prop :=
--   ∀ w ∈ L, tm.accepts_in_time w (t w.length)

-- def DetTime {Γ} (t : Nat → Nat) (L : List (List Γ)) : Prop :=
--   ∃ (k : Nat) (s : Nat) (S : Finset (Fin s)) (tm : TM k S Γ),
--   tm.accepts_language_in_time L t

-- def TM.accepts_in_space_with_final_configuration {k : Nat} {S} {Γ} [DecidableEq S]
--   (tm : TM k S Γ) (input : List Γ) (s : Nat) (conf : Configuration k S Γ) : Prop :=
--   let σ₀ := TM.initial_configuration tm input
--   conf.state = tm.acceptState ∧ TM.reachable_in_time tm σ₀ conf s ∧ (conf.space ≤ s)

-- def TM.accepts_in_space {k : Nat} {S} {Γ} [DecidableEq S]
--   (tm : TM k S Γ) (input : List Γ) (s : Nat) : Prop :=
--   ∃ conf, TM.accepts_in_space_with_final_configuration tm input s conf

-- def DetSpace {Γ} (s : Nat → Nat) (L : List (List Γ)) : Prop :=
--   ∃ (k : Nat) (st : Nat) (S : Finset (Fin st)) (tm : TM k S Γ),
--     tm.accepts_language_in_time L s

-- theorem tm_move_each_at_most_1_space {k : Nat} {S} {Γ}
--   (tm : TM k S Γ) (conf : Configuration k S Γ) (m : Fin k → Movement) :
--   ∀ i, ((tm.move conf m).tapes i).size ≤ (conf.tapes i).size + 1 := by
--   intro i
--   simp [TM.move, move_at_most_one_space]

-- theorem tm_move_at_most_k_space {k : Nat} {S} {Γ}
--   (tm : TM k S Γ) (conf : Configuration k S Γ) (moves : Fin k → Movement) :
--   (tm.move conf moves).space ≤ conf.space + k := by
--   calc
--     (tm.move conf moves).space
--       = ∑ i, ((tm.move conf moves).tapes i).size := rfl
--     _ ≤ ∑ i, ((conf.tapes i).size + 1) := by simp [Finset.sum_le_sum, tm_move_each_at_most_1_space]
--     _ = (∑ i, (conf.tapes i).size) + ∑ i : Fin k, 1 := by simp [Finset.sum_add_distrib]
--     _ = conf.space + k := by simp [Configuration.space]

-- theorem tm_step_at_most_k_space {k : Nat} {S} {Γ} [DecidableEq S]
--   (tm : TM k S Γ) (conf : Configuration k S Γ) :
--   (tm.step conf).space ≤ conf.space + k := by
--   simp [TM.step]
--   by_cases hhalt : conf.state = tm.acceptState ∨ conf.state = tm.rejectState
--   · simp [hhalt]
--   · simp [hhalt]
--     apply tm_move_at_most_k_space

-- theorem reachable_space_at_most_time {k : Nat} {S} {Γ} [DecidableEq S]
--   (tm : TM k S Γ) (input : List Γ) (t : Nat) (conf : Configuration k S Γ)
--   (h : TM.reachable_in_time tm (TM.initial_configuration tm input) conf t) :
--   conf.space ≤ (max 1 input.length) + k + t * (k + 1) := by
--   induction h with
--   | zero => simp [tm_space_of_initial_configuration]
--   | succ σ t' hpref ih =>
--     calc
--       (tm.step σ).space
--       _ ≤ σ.space + k := by apply tm_step_at_most_k_space
--       _ ≤ max 1 input.length + k + t' * (k + 1) + k := by simp [ih]
--       _ ≤ (max 1 input.length) + k + (t' + 1) * (k + 1) := by linarith

-- theorem space_at_most_time {k : Nat} {S} {Γ} [DecidableEq S]
--   (tm : TM k S Γ) (input : List Γ) (t : Nat) (conf : Configuration k S Γ)
--   (h : TM.accepts_in_exact_time_with_final_configuration tm input t conf) :
--   conf.space ≤ (max 1 input.length) + k + t * (k + 1) := by
--   simp [reachable_space_at_most_time tm input t conf h.right]

-- -- Space compression:
-- -- start with a TM t with k tapes.
-- -- Add another tape which will be used to store the input in a compressed format.
-- -- Copy the input tape in a compressed way to the new tape.
-- -- Then simulate t, but whenever t wants to read or write the input tape,
-- -- we read or write the compressed tape instead.
-- -- Operations on the other tapes are also compressed.
-- -- Each symbol of the compressed symbol set represents a pair of symbols of the original tape.

-- def compressed_transition { k: Nat } {S} {Γ}
--   (transition : S → (Fin k → Γ) → (S × (Fin k → Γ) × (Fin k → Movement)))
--   (state : S) (symbols_read₁ symbols_read₂ : Fin k → Γ) :
--     (S × (Fin k → Γ) × (Fin k → Γ) × (Fin k → Movement)) :=



-- def compressed_tm { k: Nat } {S} {Γ}
--   (tm : TM k S Γ) : TM (k + 1) (Fin 2 × S) (Γ × Γ) :=
--   { blank := (tm.blank, tm.blank)
--     transition := fun state symbols_read => sorry
--       -- let inputSymbol := symbols 0
--       -- let symbols₁: Fin k → Γ := fun i => (symbols (i + 1)).1
--       -- let (newState, writeSymbols₁, moves₁) := tm.transition s symbols₁
--       -- let writeSymbols : Fin (k + 1) → (Γ × Γ) := fun i =>
--       --   if i.val = 0 then inputSymbol
--       --   else (writeSymbols₁ (i - 1), (symbols i).2)
--       -- let moves : Fin (k + 1) → Movement := fun i =>
--       --   if i.val = 0 then .stay
--       --   else moves₁ (i - 1)
--       -- (newState, writeSymbols, moves)
--     startState := tm.startState
--     acceptState := tm.acceptState
--     rejectState := tm.rejectState
--     k_nonzero := by simp
--   }


-- def doesNotModifyInputTape { k: Nat } {S} {Γ} [ DecidableEq S ] (tm : TM k S Γ) : Prop :=
--   ∀ s symbols,
--     let (_, writeSymbols, _) := tm.transition s symbols
--     symbols.take 1 = writeSymbols.take 1

-- -- -- TODO this is actually wrong because the tapes are different, because
-- -- -- the heads are at different positions.
-- -- theorem input_tape_not_modified_then_also_in_step
-- --   [ DecidableEq S ]
-- --   (tm : TM k S Γ)
-- --   (σ : Configuration k S Γ)
-- --   (nm : doesNotModifyInputTape tm) :
-- --   σ.tapes.take 1 = (tm.step σ).tapes.take 1 := by
-- --   unfold TM.step
-- --   by_cases hhalt : σ.state = tm.acceptState ∨ σ.state = tm.rejectState
-- --   · simp [hhalt, TM.step]
-- --   · simp [hhalt]
-- --     let (newState, writeSymbols, moves) := tm.transition σ.state (σ.tapes.map (·.head))
-- --     unfold doesNotModifyInputTape at nm
-- --     specialize nm σ.state (σ.tapes.map (·.head))
-- --     simpa [TM.move, nm] using rfl


-- def productTM { k₁ k₂: Nat } {S₁ S₂} {Γ}
--   (tm₁ : TM k₁ S₁ Γ) (tm₂ : TM k₂ S₂ Γ) : TM (k₁ + k₂ - 1) (S₁ × S₂) Γ :=
--   { blank := tm₁.blank -- TODO is that a problem?
--     transition := fun (s₁, s₂) symbols =>
--       -- first symbol is the input symbol
--       let input := symbols.take 1
--       let symbols₁: Vector Γ k₁ := (Vector.take symbols k₁).cast ( by
--           zify at *
--           have h1 : 0 ≤ ↑ k₂ - 1 := by simp
--           have h : k₁ ≤ k₁ + k₂ - 1 := by zify; linarith
--           exact Nat.min_eq_left h
--         )
--       let (newState₁, writeSymbols₁, moves₁) := tm₁.transition s₁ symbols₁
--       let symbols₂ : Vector Γ k₂ := #v[input] ++ (Vector.drop symbols k₁)
--       let (newState₂, writeSymbols₂, moves₂) := tm₂.transition s₂ symbols₂
--       ( (newState₁, newState₂),
--         writeSymbols₁ ++ writeSymbols₂,
--         moves₁ ++ moves₂ )
--     startState := (tm₁.startState, tm₂.startState)
--     acceptState := (tm₁.acceptState, tm₂.acceptState)
--     rejectState := (tm₁.rejectState, tm₂.rejectState)
--     k_nonzero := by simp
--   }


-- end Complexity

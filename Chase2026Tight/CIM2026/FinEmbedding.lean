/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.Embedding

/-!
# Embedding of the reduced setting into `Fin K` arms and `Fin N` experts

For Theorem 6.1, the reduced setting with `k` batches of `n` experts (`2k + 1` arms, `kn + 1`
experts) is embedded into the bandit with expert advice with arms `Fin K` and experts `Fin N`, as
soon as `2k + 1 ≤ K` and `kn + 1 ≤ N`: the reduction maps `σ : Fin K → Arm k`,
`τ : Fin N → Expert k n` of `strategyOn` are left inverses of injections `ρ`, `τ'`
(`exists_finEmbedding`). The losses of `strategyOn` are in `{0, 1}` (`strategyOn_feedbackIn`).

## Main statements

* `exists_finEmbedding`: the reduction maps and their sections.
* `strategyOn_feedbackIn`: the losses of the strategies are in `{0, 1}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning

namespace Chase2026Tight

variable {k n : ℕ}

/-- A nonempty finite type `β` with at most `m` elements is a retract of `Fin m`: there are maps
`σ : Fin m → β` and `ρ : β → Fin m` with `σ ∘ ρ = id`. -/
lemma exists_fin_retraction {β : Type*} [Fintype β] [Nonempty β] {m : ℕ}
    (h : Fintype.card β ≤ m) :
    ∃ (σ : Fin m → β) (ρ : β → Fin m), ∀ b, σ (ρ b) = b := by
  obtain ⟨ρ⟩ := Function.Embedding.nonempty_of_card_le (h.trans (Fintype.card_fin m).ge)
  exact ⟨Function.invFun ρ, ρ, Function.leftInverse_invFun ρ.injective⟩

/-- There are `2k + 1` arms in the reduced setting. -/
lemma card_arm (k : ℕ) : Fintype.card (Arm k) = 2 * k + 1 := by
  change Fintype.card (Option (Fin k × Bool)) = _
  simp [Fintype.card_option, Fintype.card_prod, mul_comm]

/-- There are `kn + 1` experts in the reduced setting. -/
lemma card_expert (k n : ℕ) : Fintype.card (Expert k n) = k * n + 1 := by
  change Fintype.card (Option (Fin k × Fin n)) = _
  simp [Fintype.card_option, Fintype.card_prod]

/-- **Embedding of the reduced setting** (`def:embedding`). If `2k + 1 ≤ K` and `kn + 1 ≤ N`,
there are reduction maps `σ : Fin K → Arm k`, `τ : Fin N → Expert k n` with sections `ρ`, `τ'`. -/
lemma exists_finEmbedding {K N : ℕ} (hK : 2 * k + 1 ≤ K) (hN : k * n + 1 ≤ N) :
    ∃ (σ : Fin K → Arm k) (ρ : Arm k → Fin K) (τ : Fin N → Expert k n)
      (τ' : Expert k n → Fin N), (∀ a, σ (ρ a) = a) ∧ ∀ j, τ (τ' j) = j := by
  have : Nonempty (Arm k) := ⟨Arm.zero⟩
  have : Nonempty (Expert k n) := ⟨Expert.zero⟩
  obtain ⟨σ, ρ, hσρ⟩ := exists_fin_retraction (β := Arm k) (m := K) (by rwa [card_arm])
  obtain ⟨τ, τ', hττ'⟩ := exists_fin_retraction (β := Expert k n) (m := N)
    (by rwa [card_expert])
  exact ⟨σ, ρ, τ, τ', hσρ, hττ'⟩

/-- The losses `lossOf θ e r` are in `{0, 1}`. -/
lemma lossOf_mem_zero_one (θ : Expert k n) (e : Expert k n → Arm k)
    (r : Bool × (Fin k → Bool) × Bool) (a : Arm k) : lossOf θ e r a ∈ ({0, 1} : Set ℝ) := by
  unfold lossOf
  rcases (a : Option (Fin k × Bool)) with _ | ⟨u, b⟩
  · dsimp only
    split_ifs <;> simp
  · dsimp only
    split_ifs <;> simp

variable {α ι : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Finite α]

/-- The losses of the strategies on general types are in `{0, 1}`. -/
lemma strategyOn_feedbackIn (σ : α → Arm k) (ρ : Arm k → α) (τ : ι → Expert k n)
    (τ' : Expert k n → ι) (ε : ℝ) (θ : Expert k n) :
    (strategyOn σ ρ τ τ' ε θ).FeedbackIn (Set.univ.pi fun _ ↦ {0, 1}) := by
  intro m p
  have hs : MeasurableSet {ℓ : α → ℝ | ℓ ∈ Set.univ.pi fun _ ↦ ({0, 1} : Set ℝ)} :=
    MeasurableSet.univ_pi fun _ ↦ (measurableSet_singleton 1).insert 0
  simp only [strategyOn]
  rw [Kernel.map_apply _ (by fun_prop), Kernel.comap_apply]
  change ∀ᵐ ℓ ∂(lossLaw ε θ (reduceAdvice σ τ' p.1.2)).map (fun ℓ ↦ ℓ ∘ σ), _
  rw [lossLaw, Measure.map_map (by fun_prop) (by fun_prop),
    ae_map_iff (p := fun ℓ ↦ ℓ ∈ Set.univ.pi fun _ ↦ ({0, 1} : Set ℝ)) (by fun_prop) hs]
  exact ae_of_all _ fun r a _ ↦ lossOf_mem_zero_one θ _ r (σ a)

end Chase2026Tight

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.FinEmbedding
public import Chase2026Tight.CIM2026.LowerBound
public import Chase2026Tight.CIM2026.Reduction
public import Chase2026Tight.LeanMachineLearning.Online.Bandit.ExpertAdviceLaw
public import Chase2026Tight.LeanMachineLearning.SequentialLearning.ExistsRun

/-!
# Theorem 6.1: the tight lower bound for non-stochastic bandits with expert advice

For `N ≥ 2K` experts and `T ≥ K ln(N / K)` rounds, every learner has pseudo-regret
`Ω(√(T K log(N / K)))` against some adaptive adversary with losses in `{0, 1}`, which matches the
upper bound of Kale (2014).

The advice is deterministic (each expert names an arm, `O t ω : Fin N → Fin K`); the
pseudo-regret is the library's `expertPseudoRegret` of the corresponding Dirac advice vectors
`diracAdvice (O t ω)`, that is `max_j E[∑_{t < T} (Y t (A t) - Y t (O t j))]`
(`expertPseudoRegret_diracAdvice`).

## Proof

Let `k = ⌊(K - 1) / 2⌋ ≥ 1` and `n = ⌊(N - 1) / k⌋ ≥ 1`: the reduced setting with `k` batches of
`n` experts embeds into `Fin K` arms and `Fin N` experts (`exists_finEmbedding`), and the adversary
is one of the strategies `strategyOn σ ρ τ τ' ε θ` of the pool, with `L = ln(1 + n/8)` and
`ε = √(k L / (50 T)) ≤ 0.1`. If the pseudo-regret of the learner were at most `r` under every
strategy of the pool, with `1000 r / ε ≤ T`, then the reduction
(`exists_isGoodOn_lintegral_stoppingTime_le`) would give a good SBI algorithm stopping after at most
`T` rounds in expectation, while a good SBI algorithm needs at least `k L / (8 ε²) = 50 T / 8`
rounds (`ofReal_le_lintegral_stoppingTime`): a contradiction
(`exists_lt_expertPseudoRegret_strategyOn`). The pseudo-regret does not depend on the run
(`expertPseudoRegret_eq_of_isAlgEnvSeq`), and the SBI algorithm has runs in every universe
(`IdentAlg.exists_isRun`). Finally `r = c √(T K ln(N/K))` satisfies `1000 r / ε ≤ T` for
`c = 10⁻⁵`, since `K ≤ 4k` and `ln(N/K) ≤ 4L` (`log_le_four_mul_log_one_add_div_eight`, `n ≥ N/K`).

## Main statements

* `exists_lt_expertPseudoRegret_strategyOn` (`lem:reduction_ext`): on general arm and expert types,
  some strategy of the pool gives pseudo-regret larger than `r` if `1000 r / ε ≤ T` and
  `T < k ln(1 + n/8) / (8 ε²)`.
* `exists_pseudoRegret_ge` (`thm:main`): Theorem 6.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Real

universe u v w

namespace Chase2026Tight

section General

variable {k n : ℕ} {α : Type v} {ι : Type w} [MeasurableSpace α] [DiscreteMeasurableSpace α]
  [Fintype α] [DecidableEq α] [Finite ι] {σ : α → Arm k} {ρ : Arm k → α} {τ : ι → Expert k n}
  {τ' : Expert k n → ι}

/-- **Reduction in the embedded setting** (`lem:reduction_ext`). On general arm and expert types,
let `ε ∈ (0, 0.1]`, `n ≥ 1` and `T ≥ 1` with `1000 r / ε ≤ T < k ln(1 + n/8) / (8 ε²)`. Then for
every learner, some strategy `strategyOn σ ρ τ τ' ε θ` of the pool gives pseudo-regret larger than
`r` after `T` rounds. -/
lemma exists_lt_expertPseudoRegret_strategyOn (hσρ : ∀ a, σ (ρ a) = a)
    (hττ' : ∀ j, τ (τ' j) = j) {ε : ℝ} (hε : ε ∈ Set.Ioc 0 0.1) (hn : 1 ≤ n) {T : ℕ}
    (hT1 : 1 ≤ T) {r : ℝ} (hr : 1000 * r / ε ≤ T)
    (hT : T < k * log (1 + n / 8) / (8 * ε ^ 2)) (alg : Algorithm (ι → α) α ℝ) :
    ∃ θ : Expert k n, ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (O : ℕ → Ω → ι → α) (A : ℕ → Ω → α) (Y : ℕ → Ω → α → ℝ),
      IsAlgEnvSeq O A Y alg.comapBanditFeedback (strategyOn σ ρ τ τ' ε θ) P →
        r < expertPseudoRegret P (fun t ω ↦ diracAdvice (O t ω)) A Y T := by
  by_contra! h
  -- Every run under every strategy of the pool has pseudo-regret at most `r`, since one does.
  have hr' : ∀ (θ : Expert k n) {Ω : Type max u v w} {_mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (O : ℕ → Ω → ι → α) (A : ℕ → Ω → α) (Y : ℕ → Ω → α → ℝ),
      IsAlgEnvSeq O A Y alg.comapBanditFeedback (strategyOn σ ρ τ τ' ε θ) P →
        expertPseudoRegret P (fun t ω ↦ diracAdvice (O t ω)) A Y T ≤ r := by
    intro θ Ω mΩ P _ O A Y hseq
    obtain ⟨Ω₀, mΩ₀, P₀, _, O₀, A₀, Y₀, hseq₀, hle⟩ := h θ
    rwa [expertPseudoRegret_eq_of_isAlgEnvSeq hseq hseq₀ measurable_diracAdvice]
  obtain ⟨A', hgood, hstop⟩ :=
    exists_isGoodOn_lintegral_stoppingTime_le.{max u v w} hσρ hττ' hε alg hT1 hr' hr
  obtain ⟨Ω, mΩ, P, hP, O, X, Y, out, hrun⟩ :=
    A'.comapBanditFeedback.exists_isRun.{u} (strategyOn σ ρ τ τ' ε Expert.zero)
  have h_le := (ofReal_le_lintegral_stoppingTime hσρ hττ' hε hn hgood hrun).trans
    (hstop Expert.zero P O X Y out hrun)
  rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h_le
  linarith

end General

/-- `ln x ≤ 4 ln(1 + x / 8)` for `x > 0`, since `x ≤ (1 + x / 8) ^ 4`. -/
lemma log_le_four_mul_log_one_add_div_eight {x : ℝ} (hx : 0 < x) :
    log x ≤ 4 * log (1 + x / 8) := by
  have h4 : log ((1 + x / 8) ^ 4) = 4 * log (1 + x / 8) := by
    rw [Real.log_pow]
    norm_num
  rw [← h4]
  refine Real.log_le_log hx ?_
  nlinarith [sq_nonneg (x / 8 - 1 / 3), pow_nonneg hx.le 3, pow_nonneg hx.le 4]

/-- **Theorem 6.1** (Chase, Ito, Mehalel 2026). There is a universal constant `c > 0` such that
for all numbers of arms `K ≥ 3` and experts `N ≥ 2K`, every horizon `T ≥ K ln(N / K)` and every
learner for the bandit with expert advice, there is an adaptive adversary (whose losses do not
depend on the arm pulled in the current round) with losses in `{0, 1}`
under which the pseudo-regret of the learner after `T` rounds is at least
`c √(T K log(N / K))`. The paper states it for positive `K`; it is false for `K = 1` (every learner
has pseudo-regret `0`) and the proof needs `K ≥ 3` (the reduced setting has
`k = ⌊(K - 1) / 2⌋ ≥ 1` batches). -/
theorem exists_pseudoRegret_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ (K N T : ℕ), 3 ≤ K → 2 * K ≤ N → K * log (N / K) ≤ T →
      ∀ alg : Algorithm (Fin N → Fin K) (Fin K) ℝ,
      ∃ adv : Environment (Fin N → Fin K) (Fin K) (Fin K → ℝ),
        adv.FeedbackIgnoresAction ∧ adv.FeedbackIn (Set.univ.pi fun _ ↦ {0, 1}) ∧
        ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
          (O : ℕ → Ω → Fin N → Fin K) (A : ℕ → Ω → Fin K) (Y : ℕ → Ω → Fin K → ℝ),
          IsAlgEnvSeq O A Y alg.comapBanditFeedback adv P →
            c * √(T * K * log (N / K)) ≤
              expertPseudoRegret P (fun t ω ↦ diracAdvice (O t ω)) A Y T := by
  refine ⟨1 / 10 ^ 5, by norm_num, fun K N T hK hN hT alg ↦ ?_⟩
  -- The reduced setting: `k` batches of `n` experts, embedded into `Fin K` and `Fin N`.
  set k := (K - 1) / 2 with hk
  set n := (N - 1) / k with hn
  have hk1 : 1 ≤ k := by omega
  have hkK : 2 * k + 1 ≤ K := by omega
  have hK4 : K ≤ 4 * k := by omega
  have hkn : k * n + 1 ≤ N := by
    have := Nat.div_mul_le_self (N - 1) k
    rw [← hn] at this
    rw [mul_comm]
    omega
  have hkn' : N ≤ k * (n + 1) := by
    have := Nat.lt_div_mul_add (a := N - 1) hk1
    rw [← hn] at this
    rw [mul_add, mul_one, mul_comm]
    omega
  have hn1 : 1 ≤ n := (Nat.le_div_iff_mul_le hk1).mpr (by omega)
  obtain ⟨σ, ρ, τ, τ', hσρ, hττ'⟩ := exists_finEmbedding hkK hkn
  -- Real arithmetic: `L = ln(1 + n/8)` is between `ln(N/K)/4` and `ln(N/K)`.
  have hKr : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have hNr : 2 * (K : ℝ) ≤ N := by exact_mod_cast hN
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkKr : 2 * (k : ℝ) + 1 ≤ K := by exact_mod_cast hkK
  have hK4r : (K : ℝ) ≤ 4 * k := by exact_mod_cast hK4
  have hknr : (k : ℝ) * n + 1 ≤ N := by exact_mod_cast hkn
  have hknr' : (N : ℝ) ≤ k * (n + 1) := by exact_mod_cast hkn'
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hK0 : (0 : ℝ) < K := by linarith
  set x : ℝ := N / K with hx
  have hx2 : 2 ≤ x := by rw [hx, le_div_iff₀ hK0]; linarith
  have hlogx : 0 < log x := Real.log_pos (by linarith)
  have hnx : x ≤ n := by
    rw [hx, div_le_iff₀ hK0]
    nlinarith [mul_le_mul_of_nonneg_left hkKr (by linarith : (0 : ℝ) ≤ n)]
  set L := log (1 + n / 8) with hL
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hLx : log x ≤ 4 * L :=
    (log_le_four_mul_log_one_add_div_eight (by linarith)).trans
      (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) (by norm_num))
  have hLx' : L ≤ log x := by
    refine Real.log_le_log (by positivity) ?_
    rw [hx, le_div_iff₀ hK0]
    nlinarith [mul_le_mul_of_nonneg_left hK4r (by linarith : (0 : ℝ) ≤ n)]
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hT
  have hT1 : 1 ≤ T := Nat.cast_pos.mp hT0
  have hkL : k * L ≤ T / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hLx' (by linarith : (0 : ℝ) ≤ k)]
  have hKlog : K * log x ≤ 16 * (k * L) := by
    nlinarith [mul_le_mul_of_nonneg_right hK4r hlogx.le,
      mul_le_mul_of_nonneg_left hLx (by linarith : (0 : ℝ) ≤ k)]
  -- The parameter `ε = √(k L / (50 T)) ∈ (0, 0.1]`.
  set ε := √(k * L / (50 * T)) with hε
  have hε2 : ε ^ 2 = k * L / (50 * T) := Real.sq_sqrt (by positivity)
  have hε0 : 0 < ε := Real.sqrt_pos.mpr (by positivity)
  have hε1 : ε ≤ 0.1 := by
    rw [hε, Real.sqrt_le_left (by norm_num), div_le_iff₀ (by positivity)]
    linarith
  -- `r = c √(T K ln(N/K))` satisfies `1000 r / ε ≤ T`, and `T < k L / (8 ε²) = 50 T / 8`.
  have hr : 1000 * (1 / 10 ^ 5 * √(T * K * log x)) / ε ≤ T := by
    rw [div_le_iff₀ hε0, ← sq_le_sq₀ (by positivity) (by positivity), mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (by positivity), hε2]
    have := mul_le_mul_of_nonneg_left hKlog hT0.le
    field_simp
    nlinarith
  have hTlt : (T : ℝ) < k * L / (8 * ε ^ 2) := by
    rw [hε2, show k * L / (8 * (k * L / (50 * T))) = 50 * T / 8 by field_simp]
    linarith
  obtain ⟨θ, hθ⟩ := exists_lt_expertPseudoRegret_strategyOn.{u} hσρ hττ' ⟨hε0, hε1⟩ hn1 hT1 hr
    hTlt alg
  exact ⟨strategyOn σ ρ τ τ' ε θ, strategyOn_feedbackIgnoresAction _ _ _ _ _ _,
    strategyOn_feedbackIn _ _ _ _ _ _, fun P _ O A Y h ↦ (hθ P O A Y h).le⟩

end Chase2026Tight

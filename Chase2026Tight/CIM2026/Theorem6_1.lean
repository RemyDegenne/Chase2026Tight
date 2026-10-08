/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.LeanMachineLearning.Online.Bandit.ExpertAdvice

/-!
# Theorem 6.1: the tight lower bound for non-stochastic bandits with expert advice

For `N ≥ 2K` experts and `T ≥ K ln(N / K)` rounds, every learner has pseudo-regret
`Ω(√(T K log(N / K)))` against some adaptive adversary with losses in `{0, 1}`, which matches the
upper bound of Kale (2014).

The advice is deterministic (each expert names an arm, `O t ω : Fin N → Fin K`); the
pseudo-regret is the library's `expertPseudoRegret` of the corresponding Dirac advice vectors
`diracAdvice (O t ω)`, that is `max_j E[∑_{t < T} (Y t (A t) - Y t (O t j))]`
(`expertPseudoRegret_diracAdvice`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Bandits Real

universe u

namespace Chase2026Tight

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
  sorry

end Chase2026Tight

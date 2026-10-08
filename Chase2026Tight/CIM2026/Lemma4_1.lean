/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Chase2026Tight.CIM2026.Setting
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Lemma 4.1: KL bound between the mixture and the null in the two-batch game

In the two-batch game (`k = 1`), the learner always pulls an arm of batch `1`, so that the advice
and losses of the rounds are i.i.d. with law `P_θ = roundLaw ε θ` under `S_θ`. The
Kullback–Leibler divergence between the uniform mixture over `v` of `P_(1, v)^T` and `P_0^T` is
at most `((1 + 4 ε²)^T - 1) / n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Bandits
open scoped ENNReal

namespace Chase2026Tight

/-- **Lemma 4.1** (Chase, Ito, Mehalel 2026; Ito et al. 2024). In the two-batch game (`k = 1`),
for `0 < ε ≤ 0.1`, `T ≥ 1` and `n ≥ 1`,
`KL((1/n) ∑_v P_(1, v)^T ‖ P_0^T) ≤ ((1 + 4 ε²)^T - 1) / n`. -/
theorem klDiv_mixture_pi_roundLaw_le {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : ε ∈ Set.Ioc 0 0.1)
    {T : ℕ} (hT : 1 ≤ T) :
    klDiv ((n : ℝ≥0∞)⁻¹ • ∑ v : Fin n, Measure.pi fun _ : Fin T ↦ roundLaw ε (Expert.mk 0 v))
        (Measure.pi fun _ : Fin T ↦ roundLaw (k := 1) ε Expert.zero) ≤
      ENNReal.ofReal (((1 + 4 * ε ^ 2) ^ T - 1) / n) := by
  sorry

end Chase2026Tight

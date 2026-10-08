/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.Restrict

/-!
# Pinsker's inequality for events

For probability measures `P`, `Q` and a measurable event `E`,
`2 (P(E) - Q(E))² ≤ KL(P ‖ Q)`. Splitting the divergence along `E` and `Eᶜ`
(`klDiv_restrict_add_restrict_compl`) and applying Jensen's inequality to each part
(`mul_log_le_klDiv`) bounds the divergence between the Bernoulli laws of parameters `P(E)` and
`Q(E)` by `KL(P ‖ Q)`, which reduces the statement to Pinsker's inequality for Bernoulli laws,
`kl(p, q) ≥ 2 (p - q)²`, proved by calculus in `q`.

## Main statements

* `InformationTheory.two_mul_sq_sub_le_mul_log_div_add_mul_log_div`: Pinsker's inequality for
  Bernoulli laws, `2 (p - q)² ≤ p log (p / q) + (1 - p) log ((1 - p) / (1 - q))` for `p ∈ [0, 1]`
  and `q ∈ (0, 1)`.
* `InformationTheory.ofReal_mul_log_div_add_mul_log_div_le_klDiv`: the divergence between the
  Bernoulli laws of parameters `P(E)` and `Q(E)` is at most `KL(P ‖ Q)`.
* `InformationTheory.ofReal_two_mul_sq_measureReal_sub_le_klDiv`: Pinsker's inequality for events.
-/

@[expose] public section

open MeasureTheory Real Set Filter
open scoped ENNReal Topology

namespace InformationTheory

/-- **Pinsker's inequality for Bernoulli laws**, case `p ≤ q`: for `0 ≤ p ≤ q < 1`,
`2 (p - q)² ≤ p log (p / q) + (1 - p) log ((1 - p) / (1 - q))`. -/
lemma two_mul_sq_sub_le_mul_log_div_add_mul_log_div_of_le {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (hq : q < 1) :
    2 * (p - q) ^ 2 ≤ p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := by
  set f : ℝ → ℝ := fun t ↦ p * log (p / t) + (1 - p) * log ((1 - p) / (1 - t)) - 2 * (p - t) ^ 2
    with hf
  have hp1 : 0 < 1 - p := by linarith
  have h_log_div (a : ℝ) {s : ℝ} (hs : s ≠ 0) : a * log (a / s) = a * log a - a * log s := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · rw [log_div ha hs]; ring
  -- `f` has derivative `-p / t + (1 - p) / (1 - t) + 4 (p - t)` on `(p, q)`
  have h_deriv : ∀ t ∈ Ioo p q,
      HasDerivAt f (-p / t + (1 - p) / (1 - t) + 4 * (p - t)) t := by
    intro t ht
    have ht0 : 0 < t := hp.trans_lt ht.1
    have ht1 : 0 < 1 - t := by linarith [ht.2]
    have h_eq : (fun s ↦ p * log p - p * log s + ((1 - p) * log (1 - p) - (1 - p) * log (1 - s))
        - 2 * (p - s) ^ 2) =ᶠ[𝓝 t] f := by
      filter_upwards [Ioo_mem_nhds ht0 (by linarith : t < 1)] with s hs
      dsimp only [f]
      rw [h_log_div p hs.1.ne', h_log_div (1 - p) (by linarith [hs.2] : 1 - s ≠ 0)]
    refine HasDerivAt.congr_of_eventuallyEq ?_ h_eq.symm
    have h1 := ((hasDerivAt_log ht0.ne').const_mul p).const_sub (p * log p)
    have h2 := ((((hasDerivAt_id' t).const_sub 1).log ht1.ne').const_mul (1 - p)).const_sub
      ((1 - p) * log (1 - p))
    have h3 := (((hasDerivAt_id' t).const_sub p).pow 2).const_mul 2
    convert (h1.add h2).sub h3 using 1
    have := ht1.ne'
    field_simp
    ring
  -- hence `f` is monotone on `[p, q]`, since `t (1 - t) ≤ 1 / 4`
  have h_mono : MonotoneOn f (Icc p q) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc p q) ?_ ?_ ?_
    · have h1 : ContinuousOn (fun t ↦ p * log (p / t)) (Icc p q) := by
        rcases hp.eq_or_lt with rfl | hp0
        · simp only [zero_mul]; exact continuousOn_const
        · refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
          · exact continuousOn_const.div continuousOn_id fun t ht ↦ (hp0.trans_le ht.1).ne'
          · exact fun t ht ↦ (div_pos hp0 (hp0.trans_le ht.1)).ne'
      have h2 : ContinuousOn (fun t ↦ (1 - p) * log ((1 - p) / (1 - t))) (Icc p q) := by
        refine continuousOn_const.mul (ContinuousOn.log ?_ ?_)
        · exact continuousOn_const.div (continuousOn_const.sub continuousOn_id)
            fun t ht ↦ (sub_pos.2 (ht.2.trans_lt hq)).ne'
        · exact fun t ht ↦ (div_pos hp1 (sub_pos.2 (ht.2.trans_lt hq))).ne'
      exact (h1.add h2).sub (by fun_prop)
    · rw [interior_Icc]
      exact fun t ht ↦ (h_deriv t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      have ht0 : 0 < t := hp.trans_lt ht.1
      have ht1 : 0 < 1 - t := by linarith [ht.2]
      rw [(h_deriv t ht).deriv]
      have : -p / t + (1 - p) / (1 - t) + 4 * (p - t)
          = (t - p) * (2 * t - 1) ^ 2 / (t * (1 - t)) := by
        field_simp
        ring
      rw [this]
      exact div_nonneg (mul_nonneg (by linarith [ht.1]) (sq_nonneg _)) (by positivity)
  have h := h_mono ⟨le_rfl, hpq⟩ ⟨hpq, le_rfl⟩ hpq
  have hfp : f p = 0 := by
    rcases eq_or_ne p 0 with rfl | hp0
    · simp [hf]
    · simp [hf, hp0, hp1.ne']
  rw [hfp] at h
  simp only [hf] at h
  linarith

/-- **Pinsker's inequality for Bernoulli laws**: for `p ∈ [0, 1]` and `q ∈ (0, 1)`,
`2 (p - q)² ≤ p log (p / q) + (1 - p) log ((1 - p) / (1 - q))`, the right-hand side being the
Kullback-Leibler divergence between the Bernoulli laws of parameters `p` and `q`. -/
lemma two_mul_sq_sub_le_mul_log_div_add_mul_log_div {p q : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    2 * (p - q) ^ 2 ≤ p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := by
  rcases le_total p q with hpq | hqp
  · exact two_mul_sq_sub_le_mul_log_div_add_mul_log_div_of_le hp₀ hpq hq₁
  · have h := two_mul_sq_sub_le_mul_log_div_add_mul_log_div_of_le (p := 1 - p) (q := 1 - q)
      (by linarith) (by linarith) (by linarith)
    simp only [sub_sub_cancel] at h
    linarith [show (1 - p - (1 - q)) ^ 2 = (p - q) ^ 2 by ring]

variable {β : Type*} {mβ : MeasurableSpace β} {P Q : Measure β}

/-- **Data processing for an event**: for probability measures `P`, `Q` and a measurable event
`E`, the Kullback-Leibler divergence between the Bernoulli laws of parameters `P(E)` and `Q(E)`
is at most `KL(P ‖ Q)`. -/
lemma ofReal_mul_log_div_add_mul_log_div_le_klDiv [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {E : Set β} (hE : MeasurableSet E) :
    ENNReal.ofReal (P.real E * log (P.real E / Q.real E)
      + (1 - P.real E) * log ((1 - P.real E) / (1 - Q.real E))) ≤ klDiv P Q := by
  rw [← klDiv_restrict_add_restrict_compl hE]
  refine le_trans ?_ (add_le_add (mul_log_le_klDiv _ _) (mul_log_le_klDiv _ _))
  refine le_trans (le_of_eq ?_) ENNReal.ofReal_add_le
  congr 1
  simp only [measureReal_restrict_apply_univ, probReal_compl_eq_one_sub hE]
  ring

/-- **Pinsker's inequality for events**: for probability measures `P`, `Q` and a measurable event
`E`, `2 (P(E) - Q(E))² ≤ KL(P ‖ Q)`. -/
lemma ofReal_two_mul_sq_measureReal_sub_le_klDiv [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {E : Set β} (hE : MeasurableSet E) :
    ENNReal.ofReal (2 * (P.real E - Q.real E) ^ 2) ≤ klDiv P Q := by
  by_cases hPQ : P ≪ Q
  swap; · simp [klDiv_of_not_ac hPQ]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ofReal_mul_log_div_add_mul_log_div_le_klDiv hE)
  -- if `Q(E) = 0`, then `P(E) = 0` and both sides vanish
  rcases (measureReal_nonneg (μ := Q) (s := E)).eq_or_lt with hQ0 | hQ0
  · have hP : P.real E = 0 := by
      rw [eq_comm, measureReal_eq_zero_iff] at hQ0
      rw [measureReal_eq_zero_iff]
      exact hPQ hQ0
    simp [hP, ← hQ0]
  -- if `Q(E) = 1`, then `P(E) = 1` and both sides vanish
  rcases (measureReal_le_one (μ := Q) (s := E)).eq_or_lt with hQ1 | hQ1
  · have hP : P.real E = 1 := by
      have hQ : Q E = 1 := by rwa [measureReal_def, ENNReal.toReal_eq_one_iff] at hQ1
      rw [← prob_compl_eq_zero_iff hE] at hQ
      have hPc := hPQ hQ
      rw [prob_compl_eq_zero_iff hE] at hPc
      simp [measureReal_def, hPc]
    simp [hP, hQ1]
  exact two_mul_sq_sub_le_mul_log_div_add_mul_log_div measureReal_nonneg measureReal_le_one hQ0
    hQ1

end InformationTheory

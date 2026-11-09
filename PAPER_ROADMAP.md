# Paper roadmap: A Tight Lower Bound for Non-stochastic Multi-armed Bandits with Expert Advice

Paper: RemyDegenne/Chase2026Tight · LMLExplore afd365492580 · LMLRoadmaps d01bdd6b89ce · Refreshed 2026-11-09

## Items

| Id | Item | Tag | Link | Status | Files |
|---|---|---|---|---|---|
| R1 | Pinsker's inequality for Bernoulli laws and for events | exists | `TauCeti.two_mul_sq_measureReal_sub_le_klDiv` | – | `ForLMLExplore/InformationTheory/KullbackLeibler/Pinsker.lean` |
| R2 | Tonelli's theorem for products of functions of distinct coordinates; products and images of measures with densities | exists | `TauCeti.pi_withDensity` | – | `ForLMLExplore/MeasureTheory/Integral/Pi.lean`, `ForLMLExplore/MeasureTheory/Measure/WithDensity.lean` |
| R3 | Kullback–Leibler divergence bounded by the χ² divergence, and divergence of finite mixtures of measures with densities | staged | S1 | proved | `ForLMLExplore/InformationTheory/KullbackLeibler/Mixture.lean`, `ForLMLExplore/MeasureTheory/Measure/WithDensity.lean` |
| R4 | Uniform laws on finite types: point masses, invariance under bijections, coordinates of uniform functions | exists | `Equiv.map_uniformOn_univ` | – | `ForLMLExplore/Probability/Distributions/Uniform.lean` |
| R5 | Probability simplex on `EuclideanSpace ℝ ι` | exists | `LMLExplore.simplex` | – | `ForLMLExplore/Analysis/Convex/Simplex.lean` |
| R6 | Regret notions of online learning: regret against a fixed comparator, cumulative and linear losses, regret against the best expert | target | OnlineLearning 0.1 | proved | `ForLMLExplore/OnlineLearning/Regret.lean` |
| R7 | Adversarial bandits on loss vectors: bandit feedback, expert advice, expert losses, the pseudo-regret and the expert pseudo-regret, which depend only on the law of the run | exists | `LMLExplore.Bandits.expertPseudoRegret` | – | `ForLMLExplore/Bandits/Adversarial.lean`, `ForLMLExplore/Bandits/ExpertAdvice.lean`, `ForLMLExplore/Bandits/ExpertAdviceLaw.lean`, `ForLMLExplore/MeasureTheory/MeasurableSpace/Constructions.lean` |
| R8 | Adversaries that move simultaneously with the learner: feedback that ignores the current action, and its conditional law along a run | staged | S2 | proved | `ForLMLExplore/SequentialLearning/Environments/ObliviousEnv.lean` |
| R9 | Canonical runs of identification algorithms, transport of runs along measure-preserving maps, measurability of stopped histories, output laws as integrals | exists | `LMLExplore.Identification.isRun_runMeasure` | – | `ForLMLExplore/Identification/IdentificationAlg.lean`, `ForLMLExplore/SequentialLearning/ExistsRun.lean`, `ForLMLExplore/Probability/HasCondDistrib.lean` |
| R10 | Partial feedback and relabelling: algorithms and identification algorithms transported along history maps, their runs and output laws, runs in a given universe | staged | S3 | proved | `ForLMLExplore/SequentialLearning/PartialFeedback.lean`, `ForLMLExplore/SequentialLearning/FactorsThrough.lean`, `ForLMLExplore/SequentialLearning/RunTransport.lean`, `ForLMLExplore/SequentialLearning/ExistsRun.lean`, `ForLMLExplore/Probability/HasCondDistrib.lean`, `ForLMLExplore/Probability/Kernel/Composition/MeasureComp.lean` |
| R11 | Law of a stopped history determined by the laws of the histories before stopping, for any measures on the sequences of rounds | refactor | `Learning.stoppedHistMeasure_congr` | proved | `ForLMLExplore/SequentialLearning/StoppedHistLaw.lean` |
| R12 | Mixture representation of the laws of histories and of stopped histories over a random environment | staged | S4 | proved | `ForLMLExplore/SequentialLearning/HistMixture.lean` |
| R13 | Complements on hitting times, `WithTop.untopA` and counting sums | staged | S5 | proved | `ForLMLExplore/Probability/Process/HittingTime.lean`, `ForLMLExplore/Order/WithBot.lean`, `ForLMLExplore/Topology/Algebra/InfiniteSum/ENNReal.lean` |
| R14 | The reduced setting of Sections 2–3 (arms and experts in batches, the advice process, the strategies `S_θ`, SBI algorithms) and its embedding in the bandit with `K` arms and `N` experts | paper | | proved | `CIM2026/Setting.lean`, `CIM2026/Embedding.lean`, `CIM2026/FinEmbedding.lean` |
| R15 | The reduction from SBI to regret minimization through the per-round regret of the strategies | paper | | proved | `CIM2026/PerRoundRegret.lean`, `CIM2026/Reduction.lean` |
| R16 | Representation of the runs by i.i.d. pull records, and the lower bounds on the number of rounds | paper | | proved | `CIM2026/RoundLaw.lean`, `CIM2026/ReducedRun.lean`, `CIM2026/StopAtPulls.lean`, `CIM2026/RecordTape.lean`, `CIM2026/Records.lean`, `CIM2026/LowerBound.lean` |

## Notes

- Frozen definitions. The comparator challenges copy these definitions of `ForLMLExplore/`, which
  are in the closure of the headline statements: `Learning.simplex` (R5); `banditFeedback`,
  `Algorithm.comapBanditFeedback`, `IdentAlg.comapBanditFeedback`, `Advice`, `diracAdvice`,
  `expertLoss`, `adviceRegret`, `expertPseudoRegret` (R7); `Environment.FeedbackIgnoresAction`,
  `Environment.FeedbackIn` (R8); `Round.partialFeedback`, `Hist.partialFeedback`,
  `Algorithm.comapPartialFeedback`, `IdentAlg.comap`, `IdentAlg.comapPartialFeedback` (R10).
  Replacing them with different LMLExplore definitions would change the frozen statements, so they
  stay in the paper unless a port keeps them unchanged; the bump keeps the local copies of R5 and
  R7.
- R1: the bump deletes the file. `ofReal_two_mul_sq_measureReal_sub_le_klDiv` is Tau Ceti's
  `TauCeti.two_mul_sq_measureReal_sub_le_klDiv`; Pinsker's inequality for Bernoulli laws is
  `LMLExplore.two_mul_sq_le_klBerReal` (`LMLExplore.ofReal_two_mul_sq_le_klBer` in `ℝ≥0∞`), up
  to unfolding `klBerReal`; the data processing inequality for an event is
  `LMLExplore.klBer_measureReal_le_klDiv`.
- R2: `lintegral_fintype_prod_eq_prod` is `TauCeti.lintegral_fintype_prod_eq_prod`,
  `Measure.pi_withDensity` is `TauCeti.pi_withDensity`, and `withDensity_map` is the case
  `jac = 1` of Tau Ceti's `MeasureTheory.Measure.map_withDensity_eq_withDensity`.
  `lintegral_fintype_prod_eq_pow` is the constant case and stays with its uses. In
  `WithDensity.lean`, `finsetSum_smul_withDensity` belongs to R3.
- R3: Mathlib, Tau Ceti, LML and LMLExplore have no χ² divergence and no divergence of mixtures
  (LMLExplore's `klBerReal_le_sq_sub_div` is the Bernoulli case of KL ≤ χ²). The paper's form,
  `klDiv μ ν ≤ ∫⁻ (dμ/dν - 1)² dν`, is the weak form of the bound that S1 asks for.
- R4: `uniformOn_univ_apply_eq_card_div` is Mathlib's `ProbabilityTheory.uniformOn_univ`,
  `uniformOn_univ_singleton` is `TauCeti.Probability.uniformOn_univ_apply_singleton`, and
  `lintegral_uniformOn_univ_comp_equiv` follows from `Equiv.map_uniformOn_univ`. The coordinate
  lemmas `uniformOn_univ_eval_eq` and `uniformOn_univ_singleton_eq_mul` are additional; they stay
  with the paper's files that use them.
- R5: LMLExplore's `simplex α` lives on `α → ℝ`, as the OnlineLearning conventions require; the
  paper's `Learning.simplex ι` on `EuclideanSpace ℝ ι` comes from LMLPapers. There is nothing to
  port. The paper keeps its copy (frozen definitions).
- R6: OnlineLearning 0.1 asks for the regret `∑_{t<n} (ℓ_t(x_t) - ℓ_t(u))` on an arbitrary type
  (`ocoRegret`, with its additivity in the losses and over consecutive intervals), together with
  the dynamic, interval, strongly adaptive and tracking regrets and the path length, which the
  paper does not need. The port lives in `LMLExplore.OnlineLearning`. Linear losses go in the dual
  `E →L[ℝ] ℝ` of a normed space (OnlineLearning conventions), so `linRegret` and `gradSeq`, which
  use an inner product, are restated. The expert regret, `LossesIn` and `IsBestCoord` move to
  `α → ℝ` with LMLExplore's `simplex α`. `ocoRegret_le_sum_of_hasSubgradientWithinAt` is
  LMLExplore's `LMLExplore.OnlineLearning.sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt`
  (Bandits 6.6).
- R7: Bandits 0.5 is merged. LMLExplore's `pseudoRegret`, `randomRegret`, `expertPseudoRegret` and
  `expertRandomRegret` are defined for runs against any `Environment 𝓞 α ℝ` with reward feedback,
  through LML's conditional means `env.means`, which is the roadmap's convention. The paper's
  `Bandits.pseudoRegret` and `Bandits.expertPseudoRegret` are the loss form of the same notions:
  the feedback is the whole loss vector `Y t : α → ℝ`, and the learner sees only
  `banditFeedback` through `Algorithm.comapBanditFeedback`. For adversaries whose loss vector does
  not depend on the current action (R8), the two forms agree, but not definitionally. A port would
  duplicate Bandits 0.5, so nothing is ported (frozen definitions). The bridge to LMLExplore's form
  is part of S2. The measurability helpers of `Constructions.lean` (`measurable_decide`,
  `measurable_eval_prod`, `Measurable.eval_prod`) serve only these files.
- R8: `Environment.ofSeq y` is LML's `Environment.evalSeq (fun n _ ↦ y n) _`, and
  `Environment.const μ` is LML's `Environment.bandit (Kernel.const 𝓐 μ)`. The port uses those,
  also because LMLExplore's `Learning.Environment.ofSeq o g hg` takes the name. A port keeps
  `FeedbackIgnoresAction` and `FeedbackIn` unchanged (frozen definitions).
- R9: `IdentAlg.measurable_stoppedHist` and `IdentAlg.outputMeasure_apply_eq_lintegral` have the
  same full names as LMLExplore's `Learning.IdentAlg.measurable_stoppedHist` and
  `Learning.IdentAlg.outputMeasure_apply_eq_lintegral` (`LMLExplore/Identification/Basic.lean`),
  and clash with them once that module is imported. `IdentAlg.measurableSet_lt_stoppingTime`
  follows from `Learning.IdentAlg.measurable_stoppingTime`.
  `IsAlgEnvSeq.comp_measurePreserving` and `IdentAlg.IsRun.comp_measurePreserving` are
  `Learning.IsAlgEnvSeq.comp_hasLaw` and `Learning.IdentAlg.IsRun.comp_hasLaw` applied to
  `MeasurePreserving.hasLaw`. `HasCondDistrib.comp_measurePreserving` is LML's
  `ProbabilityTheory.HasCondDistrib.comp_hasLaw`, and `hasCondDistrib_snd_fst_compProd` is the
  case `f = id` of LMLExplore's `ProbabilityTheory.hasCondDistrib_snd_compProd_comap`.
  `IdentAlg.exists_isRun` is the canonical run `isRun_runMeasure` (Identification 0.1) transported
  to a `ULift`. That universe transport goes with R10.
- R10: `Algorithm.comapPartialFeedback alg g` is LML's `Algorithm.comap` along
  `Hist.partialFeedback g`. LML's `Hist.mapFeedback` and `Algorithm.comapFeedback` are the case of
  maps that read the feedback alone (`Algorithm.comapPartialFeedback_feedback`). The relabelling of
  runs uses LML's `Algorithm.congr` and `Environment.congr`. LML has the transports of algorithms
  and environments, but no transport of identification algorithms and no transport of runs or of
  output laws. The helpers `HasCondDistrib.map_of_forall_eq` (in `HasCondDistrib.lean`) and
  `Measure.comap_comp` go with this item. No roadmap target uses transports along history maps,
  hence `staged`. A port keeps the definitions in the closure of the headline statements unchanged
  (frozen definitions).
- R11: the paper's `preStop S L` (no proper prefix of the history in `S`) is LMLExplore's private
  `notStoppedBeforeSet S L` in `LMLExplore/SequentialLearning/StoppedHistory.lean`. The proof of
  `stoppedHistMeasure_congr` passes through the paper's statement for the two trajectory measures,
  without stating it. The refactor makes `notStoppedBeforeSet` public with its API
  (`measurableSet_preStop`, the characterizations of the hitting time through it), states
  `map_stoppedHist_eq_of_forall_preStop` for any two finite measures on `ℕ → Round 𝓞 𝓐 𝓨`
  (with the canonical stopped history `IT.stoppedHist S`, of which LML's `stoppedHistMeasure` is
  the image), and derives `stoppedHistMeasure_congr` from it. R12 applies the statement to the
  mixture `trajKernel alg envT ∘ₘ ρ`, which is not a trajectory measure.
- R12: the paper's form is the countable case, through the one-step formula `trajMeasure_hist_snoc`
  and factorizations of the step probabilities along constraint sets on the parameter.
  `trajKernel` and `stoppedHistKernel` use `Kernel.ofFunOfCountable`. S4 asks for the general
  form. LMLExplore's `LMLExplore.Bandits.trajMeasure_bandit_eq_bind` (a stochastic bandit as a
  mixture of reward tables) is another instance.
- R13: Mathlib-shaped one-line complements, used only by the paper's proofs (`StopAtPulls.lean`,
  `LowerBound.lean`); they are also listed in `notes/upstreaming-candidates.md`.

## Proposed targets

### S1. The χ² divergence and the second-moment method for mixtures

For measures `μ ν` on a measurable space, define the χ² divergence `chiSqDiv μ ν : ℝ≥0∞`,
`∫⁻ (dμ/dν - 1)² dν` when `μ ≪ ν` and `∞` otherwise [Tsy09, Section 2.4; PW25, Chapter 7]. Prove:

- for probability measures, `klDiv μ ν ≤ log (1 + χ²(μ ‖ ν)) ≤ χ²(μ ‖ ν)` [Tsy09, Section 2.4],
  with the pointwise bound `klFun x ≤ (x - 1)²` on `[0, ∞)`;
- tensorization: `1 + χ²(⨂ i, μ i ‖ ⨂ i, ν i) = ∏ i, (1 + χ²(μ i ‖ ν i))` over a finite index type;
- the second-moment identity for mixtures [IS03; PW25, Chapter 7]: for a probability measure `ρ`
  on a parameter space and a measurable family of probability measures `P θ ≪ Q`,
  `1 + χ²(∫ P θ ∂ρ ‖ Q) = ∫∫ (∫ (dP θ/dQ) (dP θ'/dQ) dQ) ∂ρ(θ) ∂ρ(θ')`, with finite mixtures of
  measures with densities (`∑ i, w i • Q.withDensity (f i)`) as the elementary case;
- the Bernoulli case `χ²(Ber p ‖ Ber q) = (p - q)² / (q (1 - q))`, of which LMLExplore's
  `klBerReal_le_sq_sub_div` becomes a corollary.

The bound `KL(P_mix^T ‖ P_0^T) ≤ ((1 + 4ε²)^T - 1)/n` of [CIM26, Lemma 4.1], a uniform mixture of
product laws against a product law, is an instance of the last three items.

- [Tsy09] A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009.
- [PW25] Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge
  University Press, 2025.
- [IS03] Yu. I. Ingster and I. A. Suslina, *Nonparametric Goodness-of-Fit Testing Under Gaussian
  Models*, Springer, 2003.
- [CIM26] Z. Chase, S. Ito and I. Mehalel, *A Tight Lower Bound for Non-stochastic Multi-armed
  Bandits with Expert Advice*, COLT 2026, arXiv:2511.00257.

### S2. Adversaries that move simultaneously with the learner

In the non-oblivious adversarial bandit [BCB12, Section 3; CBL06, Section 4.1], the adversary
chooses the outcome of round `t` (for instance a loss vector `y_t : α → ℝ`) from the past, without
seeing the action of round `t`. For `env : Environment 𝓞 𝓐 𝓨`, define the property that the
feedback kernel of round `t` does not depend on the action of round `t`, and the properties that
the feedback and the observations take values in given sets. Prove:

- along every run, the feedback of round `t` has the conditional law `κ_t (h, o)`, where
  `env.feedback t = κ_t.comap Prod.fst _`, given the history and the observation of round `t`, and
  is conditionally independent of the action of round `t` given them;
- LML's `Environment.evalSeq` with tables that ignore the action and `Environment.bandit
  (Kernel.const 𝓐 μ)` are instances, and the values of the feedback and of the observations
  belong almost surely to the given sets;
- for outcomes `y_t : α → ℝ` seen through bandit feedback (the algorithm transported along
  `(o, a, y) ↦ y a`, S3), `max_a E[∑_{t<n} (y_t(A_t) - y_t(a))]` and its version against expert
  advice are LMLExplore's `pseudoRegret` and `expertPseudoRegret` of the environment that reports
  the reward `-y_t(A_t)`, so that lower bounds proved against such adversaries hold in the
  convention of the Bandits roadmap.

- [BCB12] S. Bubeck and N. Cesa-Bianchi, *Regret analysis of stochastic and nonstochastic
  multi-armed bandit problems*, Foundations and Trends in Machine Learning 5(1), 2012.
- [CBL06] N. Cesa-Bianchi and G. Lugosi, *Prediction, Learning, and Games*, Cambridge University
  Press, 2006.

### S3. Transport of algorithms, identification algorithms and runs along history maps

Partial-feedback games [LS, Chapter 37; CBL06, Chapter 6] observe a function of each round. For a
measurable round-wise map `g : Round 𝓞 𝓐 𝓨 → 𝓦` reading the observation, the action and the
feedback, define the history seen through `g`, the algorithm that applies the policy of
`alg : Algorithm 𝓞 𝓐 𝓦` to it (LML's `Algorithm.comap` along it; `Algorithm.comapFeedback` is the
case of maps of the feedback alone), the predicate that an algorithm factors through a statistic
of the history and the observation, and the transport of identification algorithms along history
maps (sampling, stopping and output rules). Prove, for any algorithm–environment pair:

- a run of the transported algorithm, seen through `g`, is a run of `alg` against every
  environment whose kernels read the past only through `g` and give the law of `g` of the round;
  hence the output laws of the transported and of the original identification algorithms agree;
- relabelling along measurable maps `fo : 𝓞' → 𝓞` and `fy : 𝓨' → 𝓨`, not necessarily injective,
  transports runs and output laws; relabelling along measurable equivalences (LML's
  `Algorithm.congr`, `Environment.congr`) transports runs both ways;
- every algorithm and every identification algorithm has a run in every environment on a
  probability space in any universe `Type u` in which the observation, action, feedback and
  output spaces have measurable copies (for instance finite spaces), so that hypotheses
  quantified over the runs in one universe apply to every run.

- [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.

### S4. Laws of runs against a random environment

For a measurable family of environments `envT : T → Environment 𝓞 𝓐 𝓨` (measurable step kernels
in `t`) and a probability measure `ρ` on `T`, define the mixture environment, whose kernels at
round `n` are the posterior predictive laws given the history, on standard Borel spaces [LS,
Chapter 34]. Prove that the law of the sequence of rounds of any algorithm against the mixture is
`∫ trajMeasure alg (envT t) ∂ρ`, that the same holds for `stoppedHistMeasure` and every stopping
rule, and the countable form: if, along the histories that are not yet stopped, the step
probabilities of `envT t` and of `env` factor through constraint sets on the parameter, then the
laws of the stopped histories of `env` are the `ρ`-mixture of those of the `envT t`. LMLExplore's
`trajMeasure_bandit_eq_bind` [LS, Section 4.6] is an instance, and so is the representation by
pull records through which this project proves Lemmas 4.2 and 5.1 of [CIM26].

### S5. Complements on hitting times

API complements to Mathlib's `hittingAfter`, `WithTop.untopA` and sums in `ℝ≥0∞`:
`hittingAfter u (s ∪ t) n ω = hittingAfter u s n ω` when `u i ω ∉ t` for every `i ≥ n` up to the
hitting time of `s`; `((t.untopA : α) : WithTop α) ≤ t`; and
`∑' i : ℕ, (if (i : ℕ∞) < t then 1 else 0 : ℝ≥0∞) = t` for `t : ℕ∞`, the pathwise form of
`E[τ] = ∑_i P(i < τ)`.

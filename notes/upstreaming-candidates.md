# Upstreaming candidates

Library material of this project meant for Mathlib or LML, with its intended destination.
Updated as phase 2 proceeds.

## Mathlib

* `Chase2026Tight/ForLMLExplore/Analysis/Convex/Simplex.lean`,
  `Chase2026Tight/ForLMLExplore/MeasureTheory/MeasurableSpace/Constructions.lean`
  (from `LMLPapers`).
* Done in phase 2 (Mathlib-shaped, namespaces `MeasureTheory`/`ProbabilityTheory`/`InformationTheory`):
  - `InformationTheory/KullbackLeibler/Pinsker.lean`: Pinsker's inequality for Bernoulli laws and
    for events (`ofReal_two_mul_sq_measureReal_sub_le_klDiv`); Mathlib has neither Pinsker's nor
    the Bretagnolle–Huber inequality;
  - `InformationTheory/KullbackLeibler/Mixture.lean`: `klFun x ≤ (x - 1)²`, KL bounded by the χ²
    divergence, the KL divergence of a finite mixture of measures with densities;
  - `MeasureTheory/Measure/WithDensity.lean` (`Measure.pi_withDensity`, `withDensity_map`),
    `MeasureTheory/Integral/Pi.lean` (lintegral of products over `Measure.pi`);
  - `Probability/HasCondDistrib.lean` (measure-preserving maps, composition-products, images
    `F X Y`), `Probability/Kernel/Composition/MeasureComp.lean` (`Measure.comap_comp`),
    `Probability/Distributions/Uniform.lean` (singletons, permutations, coordinates of uniform
    functions), `Probability/Process/HittingTime.lean`, `Order/WithBot.lean`
    (`WithTop.coe_untopA_le`), `Topology/Algebra/InfiniteSum/ENNReal.lean`.
  - Reviewed against the Mathlib style, naming and documentation guides (2026-10-08): files
    merged by topic, helpers private, measurability lemmas with measurability hypotheses only.

## LML

* From `LMLPapers`: the adversarial bandit protocol and pseudo-regret
  (`Bandits/Adversarial.lean`), the bandit with expert advice
  (`Bandits/ExpertAdvice.lean`), partial feedback for algorithms and identification
  algorithms (`SequentialLearning/PartialFeedback.lean`, `FactorsThrough.lean`), environments
  ignoring the current action (`SequentialLearning/Environments/ObliviousEnv.lean`), online
  convex regret (`OnlineLearning/Regret.lean`).
* Done in phase 2 (namespace `Learning` / `Bandits`):
  - `SequentialLearning/Environments/ObliviousEnv.lean`: conditional law of the feedback of
    environments that ignore the current action;
  - `SequentialLearning/ExistsRun.lean`: transport of runs along measure-preserving maps, runs of
    identification algorithms in a large universe, relabelling along measurable equivalences and
    runs in exactly `Type w` (`exists_isAlgEnvSeq_of_measurableEquiv`, `_of_finite`);
  - `SequentialLearning/RunTransport.lean` (partial feedback and relabelled runs, their output
    laws), `StoppedHistLaw.lean` (the law of the stopped history is determined by the histories
    before stopping), `HistMixture.lean` (trajectory laws that factor through a mixing measure),
    `IdentificationAlg.lean` (measurability of stopped histories, output laws as integrals);
  - `Bandits/ExpertAdviceLaw.lean`: the pseudo-regret depends only on the law of the run.

# Upstreaming candidates

Library material of this project meant for Mathlib or LML, with its intended destination.
Updated as phase 2 proceeds.

## Mathlib

* `Chase2026Tight/Mathlib/Analysis/Convex/Simplex.lean`,
  `Chase2026Tight/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean` (from `LMLPapers`).
* Done in phase 2 (Mathlib-shaped, namespaces `MeasureTheory`/`ProbabilityTheory`/`InformationTheory`):
  - `InformationTheory/KullbackLeibler/Pinsker.lean`: Pinsker's inequality for Bernoulli laws and
    for events (`ofReal_two_mul_sq_measureReal_sub_le_klDiv`); Mathlib has neither Pinsker's nor
    the Bretagnolle–Huber inequality;
  - `InformationTheory/KullbackLeibler/Mixture.lean`: `klFun x ≤ (x - 1)²`, KL bounded by the χ²
    divergence, the KL divergence of a finite mixture of measures with densities;
  - `MeasureTheory/Measure/WithDensity.lean` (`Measure.pi_withDensity`, `withDensity_map`),
    `MeasureTheory/Integral/Pi.lean` (lintegral of products over `Measure.pi`);
  - `Probability/HasCondDistrib.lean`, `Probability/HasCondDistribComp.lean` (two files from two
    packages, to be merged), `Probability/Distributions/Uniform.lean`, `UniformPi.lean` (idem),
    `Probability/Process/HittingTime.lean`, `Topology/Algebra/InfiniteSum/ENNReal.lean`.

## LML

* From `LMLPapers`: the adversarial bandit protocol and pseudo-regret
  (`Online/Bandit/Adversarial.lean`), the bandit with expert advice
  (`Online/Bandit/ExpertAdvice.lean`), partial feedback for algorithms and identification
  algorithms (`SequentialLearning/PartialFeedback.lean`, `FactorsThrough.lean`), environments
  ignoring the current action (`SequentialLearning/ObliviousEnv.lean`), online convex regret
  (`Online/Convex/Regret.lean`).
* Done in phase 2 (namespace `Learning` / `Bandits`):
  - `SequentialLearning/ObliviousEnv.lean`: conditional law of the feedback of environments that
    ignore the current action;
  - `SequentialLearning/ExistsRun.lean` (runs of identification algorithms in a large universe) and
    `CongrRun.lean` (runs in exactly `Type u` for finite spaces, relabelling along measurable
    equivalences): two packages proved overlapping existence results, to be unified;
  - `SequentialLearning/RunTransport.lean` (partial feedback and relabelled runs, their output
    laws), `StoppedHistLaw.lean` (the law of the stopped history is determined by the histories
    before stopping), `HistMixture.lean` (trajectory laws that factor through a mixing measure),
    `IdentificationAlg.lean` (measurability of stopped histories, output laws as integrals);
  - `Online/Bandit/ExpertAdviceLaw.lean`: the pseudo-regret depends only on the law of the run.

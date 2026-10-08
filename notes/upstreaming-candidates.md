# Upstreaming candidates

Library material of this project meant for Mathlib or LML, with its intended destination.
Updated as phase 2 proceeds.

## Mathlib

* `Chase2026Tight/Mathlib/Analysis/Convex/Simplex.lean`,
  `Chase2026Tight/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean` (from `LMLPapers`).
* Planned (blueprint Part II, `chap:prereq_information`): the KL divergence of a mixture
  (`lem:klDiv_mixture_le`), products of measures with densities (`lem:pi_withDensity`),
  Pinsker's inequality for Bernoulli laws and for events (`lem:pinsker_bernoulli`,
  `lem:pinsker_event`); Mathlib has neither Pinsker's nor the Bretagnolle–Huber inequality.

## LML

* From `LMLPapers`: the adversarial bandit protocol and pseudo-regret
  (`Online/Bandit/Adversarial.lean`), the bandit with expert advice
  (`Online/Bandit/ExpertAdvice.lean`), partial feedback for algorithms and identification
  algorithms (`SequentialLearning/PartialFeedback.lean`, `FactorsThrough.lean`), environments
  ignoring the current action (`SequentialLearning/ObliviousEnv.lean`), online convex regret
  (`Online/Convex/Regret.lean`).
* Planned (blueprint Part II, `chap:prereq_sequential`): the conditional law of the feedback of
  environments that ignore the current action, the pathwise realization of algorithms with finite
  action spaces, and the representation of runs by i.i.d. records for adversaries whose state is
  refreshed only by the learner's actions.

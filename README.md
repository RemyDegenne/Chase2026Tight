# Chase2026Tight

Lean 4 formalization of the paper

> Zachary Chase, Shinji Ito, Idan Mehalel, *A Tight Lower Bound for Non-stochastic Multi-armed
> Bandits with Expert Advice*, COLT 2026, [arXiv:2511.00257](https://arxiv.org/abs/2511.00257),

built on Mathlib and the [Lean Machine Learning](https://github.com/LeanMachineLearning/LML)
library (LML, branch `rename`). The development is blueprint-driven:
[blueprint](https://remydegenne.github.io/Chase2026Tight/blueprint/),
[dependency graph](https://remydegenne.github.io/Chase2026Tight/blueprint/dep_graph_document.html).

**Status: complete.** The five results of the paper are stated and proved in Lean, with no
`sorry`; they depend only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`. They
are listed in [`formalization.yaml`](formalization.yaml) and are standalone challenges for
[comparator](https://github.com/leanprover/comparator) in [`comparator/`](comparator/).

## Layout

* `Chase2026Tight/CIM2026/`: the paper, one file per result (`Lemma3_1.lean`, …,
  `Theorem6_1.lean`), namespace `Chase2026Tight`; the reduced setting of Sections 2–3
  (`Setting.lean`) and its version on general arm and expert types (`Embedding.lean`,
  `FinEmbedding.lean`); the reduction (`PerRoundRegret.lean`, `Reduction.lean`); the KL bound
  (`RoundLaw.lean`); the representation of runs by pull records (`ReducedRun.lean`,
  `RecordTape.lean`, `Records.lean`) and the lower bounds (`StopAtPulls.lean`, `LowerBound.lean`).
* `Chase2026Tight/LeanMachineLearning/`: material for LML: the protocol of the adversarial bandit
  and of the bandit with expert advice (`Online/Bandit/`), partial feedback and environments that
  ignore the current action (`SequentialLearning/`, from `LMLPapers`), and, new: existence and
  transport of runs, laws of stopped histories, mixtures of trajectory laws
  (`SequentialLearning/`), the pseudo-regret as a function of the law of a run.
* `Chase2026Tight/Mathlib/`: material for Mathlib: Pinsker's inequality for events and the KL
  divergence of a finite mixture (`InformationTheory/KullbackLeibler/`), products of measures with
  densities, products of integrals, conditional distributions, hitting times.
* `blueprint/src/`: the blueprint (Part I follows the paper, Part II the prerequisites);
  `notes/blueprint-outline.md`: the outline it was written from (labels, proof routes, modelling
  decisions); `source/`: the paper's LaTeX source.

## Results of the paper

| Result | Lean declaration | Notes |
|---|---|---|
| Lemma 3.1 (reduction from SBI to BwE) | `exists_isGood_expectedRounds_le` | `T⋆ ≥ 1` added (false for `T⋆ = 0`) |
| Lemma 4.1 (KL bound) | `klDiv_mixture_pi_roundLaw_le` | `T ≥ 1` not needed; proved through the χ² divergence |
| Lemma 4.2 (two-batch lower bound) | `expectedRounds_ge_of_isGood_one` | from a bound with `ln(1 + n/8)`, valid for all `n ≥ 1` |
| Lemma 5.1 (general SBI lower bound) | `expectedRounds_ge_of_isGood` | standing assumptions `0 < ε ≤ 0.1`, `n ≥ 10` explicit |
| Theorem 6.1 (main lower bound) | `exists_pseudoRegret_ge` | `K ≥ 3` (false for `K = 1`) |
| Table 1, Conjecture (Section 7) | — | not statements |

The deviations from the paper are explained in the blueprint and in `notes/blueprint-outline.md`
(section 3).

## Building and checking

```
lake exe cache get
lake build Chase2026Tight --wfail
lake exe runLinter Chase2026Tight
python3 scripts/check-blueprint.py && leanblueprint pdf && leanblueprint web
lake exe checkdecls blueprint/lean_decls
python3 scripts/make-challenges.py && lake build Comparator
```

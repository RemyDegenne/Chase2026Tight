# Chase, Ito, Mehalel — A Tight Lower Bound for Non-stochastic Multi-armed Bandits with Expert Advice

COLT 2026, paper #7 of the list. arXiv [2511.00257](https://arxiv.org/abs/2511.00257).
Zachary Chase, Shinji Ito, Idan Mehalel.

The paper proves the lower bound `Ω(√(T K log(N/K)))` on the minimax pseudo-regret of the
non-stochastic bandit with `K` arms and `N ≥ 2K` experts, matching the upper bound of Kale (2014).
The proof reduces a *special batch identification* (SBI) problem to the bandit with expert advice
on a structured pool of adversarial strategies, and lower-bounds SBI by a KL argument.

Results are numbered by section in the paper (`\newtheorem{theorem}{Theorem}[section]`, lemmas
share the counter): Lemma 3.1, Lemma 4.1, Lemma 4.2, Lemma 5.1, Theorem 6.1.

## Formalization choices

* **Protocol** (library, `Online/Bandit/Adversarial.lean` and `Online/Bandit/ExpertAdvice.lean` of
  `LMLPapers/LeanMachineLearning/`, namespace `Bandits`), with plain LML types. The advice
  `e_t : ι → α` of a round is its observation, the arm pulled `I_t` its action and the loss vector
  `ℓ_t : α → ℝ` its feedback (a `Round (ι → α) α (α → ℝ)`). A learner is an `Algorithm (ι → α) α ℝ`:
  it sees the advice and, of each past round, the loss of the pulled arm; `alg.comapBanditFeedback`
  is the same learner with feedback the loss vector, of which it sees
  `banditFeedback r = r.feedback r.action` (`Algorithm.comapPartialFeedback`,
  `LMLPapers/LeanMachineLearning/SequentialLearning/PartialFeedback.lean`). An adaptive adversary is
  an `Environment (ι → α) α (α → ℝ)` (observations the advice, feedbacks the loss vectors): it sees
  the arms pulled in the past rounds, and its losses do not depend on the arm pulled in the current
  round (`Environment.FeedbackIgnoresAction` of `SequentialLearning/ObliviousEnv.lean`: the learner
  and the adversary move simultaneously); its losses lie in `{0, 1}` a.s. if
  `adv.FeedbackIn (Set.univ.pi fun _ ↦ {0, 1})`. The library's protocol has advice *vectors*
  (`Advice ι α = ι → simplex α`); deterministic advice is the special case of the Dirac vectors
  `diracAdvice e`, so the pseudo-regret of the paper is
  `expertPseudoRegret P (fun t ω ↦ diracAdvice (O t ω)) A Y T`, which is
  `max_j E[∑_{t<T} (Y t (A t) - Y t (O t j))]` (`expertPseudoRegret_diracAdvice`); it is at most the
  expected regret against the best expert in hindsight
  (`expertPseudoRegret_le_integral_iSup_adviceRegret`).
* **Reduced setting** (`Setting.lean`). Arms `Arm k = Option (Fin k × Bool)` (arm `0` and the
  two arms of each batch), experts `Expert k n = Option (Fin k × Fin n)`, batches
  `Batch k = Option (Fin k)`; these are `def`s with the discrete σ-algebra. The advice process
  (batch bits redrawn after a pull of the batch, kept otherwise) is `adviceKernel`; the losses of
  a round under `S_θ` given the advice are `lossLaw ε θ e`, the pushforward of independent
  Bernoulli bits (loss of arm `0`, correct arm of each batch, and a `Ber(1/2 - ε)` bit deciding
  whether the special expert's advice is wrong). The pool of strategies is indexed by
  `θ : Expert k n` (`θ = 0` is `S_0`, `θ = (u, v)` is `S_(u, v)`); `strategy ε θ` is the adversary
  (observation kernels: the advice process; feedback kernels: `lossKernel ε θ` applied to the
  advice of the round; `strategy_feedbackIgnoresAction`).
  Bernoulli parameters are clamped to `[0, 1]` (`bern`), which is harmless for `0 < ε ≤ 0.1`.
* **SBI** (`Setting.lean`). An SBI algorithm is an identification algorithm
  (LML's `IdentAlg`, `SBIAlg k n`) with bandit feedback, outputting a batch; *good* = LML's
  `IdentAlg.IsPAC` at level `0.05` for the family `strategy ε θ` with badness "output ≠ special
  batch of `θ`" (a statement on the law of the output, which implies the bound for every run,
  `IdentAlg.IsPAC.measureReal_bad_of_isRun`);
  `T(A', S)` is `expectedRounds`, the Lebesgue integral of the (`ℕ∞`-valued) stopping time.
  The paper's simplifications "A' never pulls arm 0" and "A' pulls a batch rather than an arm"
  are without loss of generality and are not imposed.
* **Main theorem** is stated for arbitrary `Fin K`, `Fin N` (the reduction to `K = 2k + 1`,
  `N = kn + 1` is part of the proof), with a universal constant `c` and an adversary with losses
  in `{0, 1}` (a stronger statement than with losses in `[0, 1]`).

## Results

| Result | Status | File / declaration |
| --- | --- | --- |
| Table 1 (summary of known bounds) | not a statement | — |
| Lemma 3.1 (reduction from SBI to BwE) | formalized | `Lemma3_1.lean`, `exists_isGood_expectedRounds_le` |
| Lemma 4.1 (KL bound, from Ito et al. 2024) | formalized | `Lemma4_1.lean`, `klDiv_mixture_pi_roundLaw_le` |
| Lemma 4.2 (two-batch lower bound) | formalized | `Lemma4_2.lean`, `expectedRounds_ge_of_isGood_one` |
| Lemma 5.1 (general SBI lower bound) | formalized | `Lemma5_1.lean`, `expectedRounds_ge_of_isGood` |
| Theorem 6.1 (main lower bound) | formalized | `Theorem6_1.lean`, `exists_pseudoRegret_ge` |
| Conjecture (Section 7, oblivious adversary) | skipped | informal conjecture in the future-work section, not a numbered statement |

Notes on the statements:

* Lemma 3.1: `T⋆` is a natural number; the hypothesis on the learner is a pseudo-regret bound
  `r T` for every run under every strategy of the pool; the conclusion quantifies over runs of
  the SBI algorithm (all runs have the same law).
* Lemma 4.1: in the two-batch game the learner always pulls batch `1`, so the advice is redrawn
  every round and `P_θ` is the law of the first round, `roundLaw ε θ = (strategy ε θ).init`; the
  mixture is `(1/n) ∑_v P_(1, v)^T` with `P^T = Measure.pi`.
* Lemma 5.1: the paper's statement omits `0 < ε ≤ 0.1` and `n ≥ 10`, which are standing
  assumptions of Sections 2 and 4; they are included.
* Theorem 6.1: `T ≥ K ln(N/K)` is read with real division; `K ≥ 1` is added (positive naturals).

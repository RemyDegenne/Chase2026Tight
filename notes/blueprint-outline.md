# Blueprint outline — Chase, Ito, Mehalel, *A Tight Lower Bound for Non-stochastic Multi-armed Bandits with Expert Advice* (COLT 2026)

arXiv 2511.00257, source in `source/main.tex`. Library `Chase2026Tight`, paper directory
`Chase2026Tight/CIM2026/` (namespace `Chase2026Tight`), LML branch `rename`. The statements start
from the statement-only formalization in `LMLPapers` (COLT2026/Chase2026Tight, its README is
`notes/lmlpapers-README.md`), checked against the paper and corrected where they were false.

This file fixes the labels, the modelling and the proof routes before the blueprint and the Lean
proofs are written.

## 1. Results of the paper

Numbering `\newtheorem{theorem}{Theorem}[section]`, lemmas share the counter.

| Result | Label | Lean (`Chase2026Tight.`) | Status |
|---|---|---|---|
| Section 2 (reduced setting, strategies `S_0`, `S_(u,v)`) | `def:arm`, `def:advice`, `def:loss_law`, `def:strategy` | `Setting.lean` | definitions |
| Section 3 (pseudo-regret, SBI, good, `T(A', S)`) | `def:pseudo_regret`, `def:sbi`, `def:is_good`, `def:expected_rounds` | `Setting.lean`, LML | definitions |
| Lemma 3.1 (reduction SBI → BwE) | `lem:reduction` | `exists_isGood_expectedRounds_le` | headline |
| Lemma 4.1 (KL bound, Ito et al. 2024) | `lem:kl_bound` | `klDiv_mixture_pi_roundLaw_le` | headline |
| Lemma 4.2 (two-batch lower bound) | `lem:two_batch` | `expectedRounds_ge_of_isGood_one` | headline |
| Lemma 5.1 (general SBI lower bound) | `lem:many_batches` | `expectedRounds_ge_of_isGood` | headline |
| Theorem 6.1 (main lower bound) | `thm:main` | `exists_pseudoRegret_ge` | headline |
| Table 1, Conjecture (Section 7) | — | — | not statements |

## 2. Modelling decisions

* **Protocol** (LML `rename`): a learner for the bandit with expert advice (BwE) is an
  `Algorithm (ι → α) α ℝ`: observation = the advice of the round (each expert names an arm),
  action = the arm pulled, feedback = the loss of the pulled arm. It runs as
  `alg.comapBanditFeedback` against an adversary `Environment (ι → α) α (α → ℝ)` whose feedback is
  the whole loss vector. Adaptive adversary: the environment sees the past arms; its losses do not
  depend on the arm of the current round (`Environment.FeedbackIgnoresAction`, the learner and
  the adversary move simultaneously).
* **Pseudo-regret**: `expertPseudoRegret P (diracAdvice ∘ O) A Y T = max_j E[∑_{t<T} (ℓ_t(I_t) -
  ℓ_t(e_t(j)))]`, the paper's `R_T`.
* **Reduced setting** (`Setting.lean`): `Arm k = Option (Fin k × Bool)`, `Expert k n =
  Option (Fin k × Fin n)`, `Batch k = Option (Fin k)`; advice bits `Fin k → Fin n → Bool`, batch
  `u` redrawn uniformly after a pull of batch `u` (`adviceKernel`); losses from `lossRandomness`
  (a `Ber(1/2 - ε/2)` bit for arm `0`, a uniform bit per batch, a `Ber(1/2 - ε)` bit for the
  special expert) through `lossOf θ`; `strategy ε θ` for `θ : Expert k n` (`θ = 0` is `S_0`).
* **SBI**: an SBI algorithm is LML's `IdentAlg` with bandit feedback (`SBIAlg k n`); *good* is
  `IdentAlg.IsPAC` at level `0.05` (a statement on the law of the output, `outputMeasure`);
  `T(A', S)` is `expectedRounds`, the expectation of the `ℕ∞`-valued stopping time over a run.
  An algorithm that does not stop almost surely has `T(A', S) = ∞`.
* **Not imposed** (paper's "without loss of generality"): the SBI algorithm may pull arm `0` and
  may choose which arm of a batch it pulls; the lower bounds are proved for all algorithms.

## 3. Corrections to the statements

* **Theorem 6.1** is stated in the paper (and in LMLPapers) for all positive `K`. It is false for
  `K = 1` (one arm: every learner has pseudo-regret `0`), and the proof needs `K ≥ 3` (the
  reduced setting has `k = ⌊(K - 1)/2⌋ ≥ 1` batches). Headline statement: `3 ≤ K`, `2K ≤ N`,
  `T ≥ K ln(N/K)`.
* **Lemma 3.1** needs `T⋆ ≥ 1` (implicit in the paper, whose proof divides by `T⋆`): with
  `r(T) = T` and `T⋆ = 0` the hypotheses hold and no good algorithm stops after `0` rounds.
* **Gap in the proof of Theorem 6.1**: "assume without loss of generality that `n > 10`" fails
  when `N/K` is small (`2 ≤ N/K ≲ 20`). Route: prove Lemmas 4.2 and 5.1 with `ln(1 + n/8)` in place
  of `ln(n/10)`, valid for every `n ≥ 1` (`lem:two_batch_general`, `lem:many_batches_general`); the
  paper's versions follow since `ln(n/10) ≤ ln(1 + n/8)`, and `ln(1 + n/8) ≥ c ln(N/K)` for
  `N ≥ 2K`.

## 4. Proof routes

### Lemma 3.1 (`lem:reduction`)

1. `def:sbi_of_learner`: the SBI algorithm running the learner for `T⋆` rounds (stopping rule
   "history of length `T⋆`") and outputting the most pulled batch (deterministic output kernel,
   ties broken by a fixed order). Its runs are runs of the learner (`IdentAlg.IsRun.isAlgEnvSeq`).
2. `lem:loss_law_cond`: in a run against `strategy ε θ`, the loss vector of round `t` has
   conditional law `lossLaw ε θ e_t` given the history, the advice and the arm of round `t`.
3. `lem:per_round_regret`: let `u⋆` be the special batch of `θ` and `j⋆` the special expert
   (`θ`, or expert `0`). Then `E[ℓ_t(I_t) - ℓ_t(e_t(j⋆))] ≥ (ε/2) P(I_t ∉ u⋆)`: per arm, the
   expected loss given the advice is `1/2` (other batches), `1/2 - ε/2` (arm `0`),
   `1/2 ± ε` (batch `u⋆`), against `1/2 - ε` (resp. `1/2 - ε/2`) for `j⋆`.
4. `lem:regret_ge_pulls`: `R_T ≥ (ε/2) E[T - N_{u⋆}(T)]`, `N_u(T)` the number of pulls of batch
   `u` in the first `T` rounds.
5. Markov: `P(N_{u⋆}(T⋆) < 3T⋆/4) ≤ 4 E[T⋆ - N_{u⋆}]/T⋆ ≤ 8 r(T⋆)/(ε T⋆) ≤ 0.008`, and
   `N_{u⋆} ≥ 3T⋆/4 > T⋆/2` makes `u⋆` the unique most pulled batch.

### Lemma 4.1 (`lem:kl_bound`)

1. `lem:klDiv_mixture_le` (Mathlib-shaped): for probability measures `P_i ≪ Q`,
   `KL(∑ w_i P_i ‖ Q) ≤ ∑_i w_i log(∑_j w_j ∫ dP_j/dQ dP_i)` (Jensen, concavity of `log`).
2. `lem:roundLaw_withDensity`: `roundLaw ε (1, v) = (roundLaw ε 0).withDensity f_v` with
   `f_v(g) = 1 + (2 c_v(g) - 1) 2ε`, `c_v(g) = 1` iff the correct arm of the batch is the arm
   advised by `v`.
3. `lem:pi_withDensity`: `(Q.withDensity f)^T = Q^T.withDensity (∏_t f ∘ eval t)`.
4. `lem:integral_ratio`: `∫ ∏_t f_v(g_t) dP_{v⋆}^T` is `1` for `v ≠ v⋆` (the bit of `v` is uniform
   and independent of the correct arm) and `(1 + 4ε²)^T` for `v = v⋆`.
5. Conclude: `KL ≤ log(1 + ((1 + 4ε²)^T - 1)/n) ≤ ((1 + 4ε²)^T - 1)/n`.

### Lemmas 4.2 and 5.1 (`lem:two_batch`, `lem:many_batches`)

The core is a representation of the runs by i.i.d. *pull records*.

1. `def:record`: the record of a pull of batch `u` is the advice bits of batch `u` and the
   correct arm of batch `u` in that round; its law `recordLaw ε θ u` is uniform bits and a uniform
   correct arm if `θ` is not in batch `u`, and correct arm = bit of `v` xor `Ber(1/2 - ε)` if
   `θ = (u, v)`. Batch `u`'s advice is redrawn only after a pull of batch `u`, so the records of
   the successive pulls of batch `u` are i.i.d., whatever the learner does between pulls.
2. `lem:record_representation`: for every learner and `θ`, a run against `strategy ε θ` can be
   built on a product space carrying independent i.i.d. record sequences `(R^u_j)_j` (law
   `recordLaw ε θ u`), the losses of arm `0`, the unobserved losses, and the learner's
   randomness, all with `θ`-independent laws except the records; the observed history (advice,
   arms, observed losses) is a `θ`-independent measurable function of these. By LML's uniqueness
   of the law of a run (`isAlgEnvSeq_unique`), every run has this law. (Realizing the learner's
   kernels pathwise: finite action and output spaces, inverse-CDF construction.)
3. `lem:events_before_pulls`: an event of the observed history up to the stopping time, intersected
   with `{N_u(τ) ≤ T⋆}`, is determined by the first `T⋆` records of batch `u`, the advice part of
   record `T⋆ + 1` (uniform under every `θ`) and variables independent of batch `u`'s records.
4. `lem:pinsker_event` (Mathlib-shaped): `|P(E) - Q(E)| ≤ √(KL(P ‖ Q)/2)`, from Pinsker's
   inequality for Bernoulli laws (`lem:pinsker_bernoulli`, `kl(p, q) ≥ 2(p - q)²`) and the data
   processing inequality (Mathlib's `klDiv_map_le`).
5. `lem:two_batch_general` (for one batch `u` of a game with `k` batches, `θ ∈ {0} ∪ {(u,v)}`):
   with `T⋆ = ⌊ln(1 + n/8)/(4ε²)⌋`, `((1 + 4ε²)^{T⋆} - 1)/n ≤ 1/8`, so for
   `E = {N_u(τ) ≤ T⋆, output = 0}`: `|P_0(E) - P_mix(E)| ≤ 1/4` (Lemma 4.1, data processing through
   step 3), `P_mix(E) ≤ 0.05` (goodness under every `(u, v)`), `P_0(N_u(τ) ≤ T⋆, output ≠ 0) ≤ 0.05`
   (goodness under `S_0`), hence `P_0(N_u(τ) > T⋆) ≥ 0.65` and `E_0[N_u(τ)] ≥ 0.65 (T⋆ + 1) ≥
   ln(1 + n/8)/(8ε²)`.
6. `lem:two_batch` (`k = 1`): `τ ≥ N_1(τ)`, and `ln(n/10) ≤ ln(1 + n/8)`.
7. `lem:many_batches_general`: `τ ≥ ∑_u N_u(τ)`, so `E_0[τ] ≥ k ln(1 + n/8)/(8ε²)`;
   `lem:many_batches` follows (the paper's constant `20` has slack). This replaces the paper's
   simulation of `A'` by a two-batch algorithm `B'` by the same record argument applied to each
   batch.

### Theorem 6.1 (`thm:main`)

1. `def:embedding`: given `K ≥ 3`, `N ≥ 2K`, take `k = ⌊(K - 1)/2⌋ ≥ 1`, `n = ⌊(N - 1)/k⌋ ≥ 1`,
   embed `Arm k ↪ Fin K`, `Expert k n ↪ Fin N`; the extra arms have loss `1`, the extra experts
   advise arm `0`. The adversary is the transported `strategy ε θ`.
2. `lem:reduction_ext`: Lemma 3.1 in the embedded setting (an extra arm has per-round regret at
   least `ε/2`); the SBI algorithm obtained pulls arms of `Fin K`, and the record argument of
   Lemma 5.1 holds verbatim for it (extra arms carry no information).
3. Choose `ε = √(k ln(1 + n/8)/(50 T)) ≤ 0.1` (using `T ≥ K ln(N/K)` and `ln(1 + n/8) ≤ ln(N/K)`),
   `r(T) = √(T k ln(1 + n/8))/C`: Lemma 3.1 at `T⋆ = T` and Lemma 5.1 contradict each other for
   `C` large, so for every learner some `θ` gives `R_T > r(T) ≥ c √(T K ln(N/K))`
   (`k ≥ K/4`, and `ln(1 + n/8) ≥ ln(N/K)/4` since `n ≥ N/K ≥ 2`).

## 5. Prerequisites (Part II of the blueprint)

* Information theory (Mathlib-shaped): `lem:klDiv_mixture_le`, `lem:pi_withDensity`,
  `lem:pinsker_bernoulli`, `lem:pinsker_event`.
* Sequential learning (LML-shaped): `lem:loss_law_cond` for environments with
  `FeedbackIgnoresAction`, pull counts and their expectations, the pathwise realization of
  algorithms with finite action spaces, the record representation.
* Already available: LML's `IdentAlg`, `IsPAC`, `stoppingTime`, `isAlgEnvSeq_unique`,
  `trajMeasure`, the stopped-history laws; Mathlib's `klDiv`, `klDiv_map_le`,
  `klDiv_compProd_eq_add`.

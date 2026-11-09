# Errata of A Tight Lower Bound for Non-stochastic Multi-armed Bandits with Expert Advice

Errors found in the paper while formalizing it, with their corrections. Each entry gives where the
error is (the revision of the paper, the result, the page or equation), the error, the correction,
the declarations that state the corrected form, the kind of error and when it was found. Entries
are numbered `E1`, `E2`, … and never renumbered.

## E1. Theorem 6.1: false for `K = 1`, and the proof needs `K ≥ 3`

- **Where:** arXiv:2511.00257v1, Theorem 6.1, Section 6 (Step 4).
- **Error:** the theorem is stated for all positive `N`, `K` with `N ≥ 2K`. With one arm, every
  learner has pseudo-regret `0`, so the lower bound fails for `K = 1`. The proof works in the
  reduced setting of Section 2, with `k = (K - 1)/2` batches of two arms, which needs `k ≥ 1`,
  that is `K ≥ 3`.
- **Correction:** assume `K ≥ 3`. The general `K ≥ 3` reduces to the reduced setting with
  `k = ⌊(K - 1)/2⌋` batches and `n = ⌊(N - 1)/k⌋` experts per batch, the extra arms having loss `1`
  and the extra experts advising arm `0`.
- **Lean:** `Chase2026Tight.exists_pseudoRegret_ge` assumes `3 ≤ K`, `2K ≤ N` and
  `K ln(N/K) ≤ T`.
- **Kind:** false statement (missing hypothesis).
- **Found:** phase-1 statement check, 2026-10-08 (`notes/blueprint-outline.md`, section 3).

## E2. Lemma 3.1: false for `T⋆ = 0`

- **Where:** arXiv:2511.00257v1, Lemma 3.1, Section 3 (Step 1).
- **Error:** the lemma assumes only `T⋆ ≥ 1000 r(T⋆)/ε`. For `T⋆ = 0` this holds whenever
  `r(0) = 0` (the pseudo-regret after `0` rounds is `0`), but no good SBI algorithm stops after `0`
  rounds: without any observation, its output cannot be the special batch with probability at
  least `0.95` under every strategy of the pool. The proof divides by `T⋆`.
- **Correction:** assume `T⋆ ≥ 1`, which the proof uses implicitly.
- **Lean:** `Chase2026Tight.exists_isGood_expectedRounds_le` assumes `1 ≤ T⋆`.
- **Kind:** false statement (missing hypothesis).
- **Found:** phase-1 statement check, 2026-10-08 (`notes/blueprint-outline.md`, section 3).

## E3. Proof of Theorem 6.1: `n > 10` is not without loss of generality

- **Where:** arXiv:2511.00257v1, proof of Theorem 6.1, first sentence ("Assume without loss of
  generality that … `n > 10`").
- **Error:** the theorem assumes only `N ≥ 2K`, so `n = (N - 1)/k` can be as small as `2` or `3`
  when `N/K` is small (`2 ≤ N/K ≲ 20`): `n > 10` cannot be assumed, and Lemmas 4.2 and 5.1, whose
  bounds are in `ln(n/10)`, then give nothing.
- **Correction:** Lemmas 4.2 and 5.1 hold with `ln(1 + n/8)` in place of `ln(n/10)`, for every
  `n ≥ 1`, by the same argument with `T⋆ = ⌊ln(1 + n/8)/(4ε²)⌋`; the paper's versions follow from
  `ln(n/10) ≤ ln(1 + n/8)`, and `ln(1 + n/8) ≥ c ln(N/K)` for `N ≥ 2K` concludes the proof of the
  theorem for every `n ≥ 1`.
- **Lean:** `Chase2026Tight.ofReal_le_lintegral_pullsBefore` (the bound with `ln(1 + n/8)` for
  one batch) and `Chase2026Tight.ofReal_le_lintegral_stoppingTime` (for `k` batches), used by
  `Chase2026Tight.exists_pseudoRegret_ge`.
- **Kind:** gap in the proof.
- **Found:** phase-1 statement check, 2026-10-08 (`notes/blueprint-outline.md`, section 3).

## E4. Proof of Lemma 4.2: the learner of the two-batch game is not passive

- **Where:** arXiv:2511.00257v1, Section 4 (Step 2), the paragraph before Lemma 4.1 ("the learner
  is completely passive throughout the game") and the proof of Lemma 4.2, which takes the rounds
  to be i.i.d. draws from `P_θ`.
- **Error:** with `k = 1`, a learner may also pull arm `0`, which does not redraw the advice of
  batch `1`: it can look at the advice of its next pull of batch `1` before deciding whether to
  stop. Its rounds are then not i.i.d. draws from `P_θ`, and the stopping time is not a stopping
  time of such a sequence.
- **Correction:** represent the stopped history by i.i.d. records of the pulls of batch `1` (the
  advice and the losses of each pull) and variables independent of them; the advice of the next
  pull is uniform under every strategy, so it carries no information on `θ`, and the argument of
  the paper goes through for the records. The same argument, applied to each batch of the game
  with `k` batches, proves Lemma 5.1 without the paper's simulation of the big game by a
  two-batch algorithm.
- **Lean:** `Chase2026Tight.stoppedHistMeasure_redStrategy_eq_comp` (the representation by
  records), used by `Chase2026Tight.ofReal_le_lintegral_pullsBefore`.
- **Kind:** gap in the proof.
- **Found:** phase 2, 2026-10-08 (`blueprint/src/chapters/two_batch.tex`, remark after Lemma 4.2).

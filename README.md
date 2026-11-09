# Chase2026Tight

A Lean 4 formalization of *A Tight Lower Bound for Non-stochastic Multi-armed Bandits with Expert
Advice* (Zachary Chase, Shinji Ito and Idan Mehalel, COLT 2026,
[arXiv:2511.00257](https://arxiv.org/abs/2511.00257)), on top of
[LMLExplore](https://github.com/LeanMachineLearning/LMLExplore), and so of
[LML](https://github.com/LeanMachineLearning/LML), [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
and [Mathlib](https://github.com/leanprover-community/mathlib4). It follows the layout of
[lml-paper-template](https://github.com/LeanMachineLearning/lml-paper-template).

It formalizes the `Ω(√(T K log(N/K)))` lower bound on the minimax pseudo-regret of the
non-stochastic bandit with `K` arms and `N ≥ 2K` experts against an adaptive adversary
(Theorem 6.1), through the reduction of special batch identification to regret minimization
(Lemma 3.1), a Kullback–Leibler bound between a mixture of product laws and a product law
(Lemma 4.1), and lower bounds on the number of rounds of good special batch identification
algorithms (Lemmas 4.2 and 5.1). Two results are stated in a corrected form, Lemma 3.1 and
Theorem 6.1, and two steps of the proofs are done differently: see the errata. Every headline
result is proved, with no `sorry`.

- Website: https://RemyDegenne.github.io/Chase2026Tight/, with the blueprint, the referee site and
  the literature links (which declarations formalize which results of the paper). CI builds it on
  each push to `main`. `scripts/formalize.sh` also commits the literature links, as
  `literature/annotations.jsonl`, when the paper is formalized and after the final bump.
- The paper: `source/`. Errors found in it, with their corrections: `notes/paper-errata.md`.
- The paper's results: `Chase2026Tight/CIM2026/`, one file per result, listed with their status in
  `formalization.yaml`; comparator challenges in `comparator/`.
- Library-shaped material: `Chase2026Tight/ForLMLExplore/`, which Tau Ceti workers port to
  LMLExplore; `PAPER_ROADMAP.md` says where each item goes.
- The blueprint outline, the plan of phase 2 and the upstreaming candidates: `notes/`.

## Results of the paper

| Result | Lean declaration | Notes |
|---|---|---|
| Lemma 3.1 (reduction from SBI to BwE) | `exists_isGood_expectedRounds_le` | `T⋆ ≥ 1` added (false for `T⋆ = 0`) |
| Lemma 4.1 (KL bound) | `klDiv_mixture_pi_roundLaw_le` | the paper's `T ≥ 1` is dropped; proved through the χ² divergence |
| Lemma 4.2 (two-batch lower bound) | `expectedRounds_ge_of_isGood_one` | from a bound with `ln(1 + n/8)`, valid for all `n ≥ 1` |
| Lemma 5.1 (general SBI lower bound) | `expectedRounds_ge_of_isGood` | standing assumptions `0 < ε ≤ 0.1`, `n ≥ 10` explicit |
| Theorem 6.1 (main lower bound) | `exists_pseudoRegret_ge` | `K ≥ 3` (false for `K = 1`) |
| Table 1, Conjecture (Section 7) | — | not statements |

## Building

```bash
scripts/build.sh
```

The script fetches Mathlib's and Tau Ceti's prebuilt files, then runs `lake build`; its arguments go
to `lake build`.

## Working on it

The workflow is the `formalize-paper` skill of the `lml` Claude Code plugin
([lml-claude](https://github.com/LeanMachineLearning/lml-claude)). The paper is formalized; what is
left is to contribute its library-shaped part. `scripts/formalize.sh`, in a terminal or tmux, tags
`PAPER_ROADMAP.md`, sends the reusable parts to LMLExplore, and once they are merged moves the paper
to the current LMLExplore.

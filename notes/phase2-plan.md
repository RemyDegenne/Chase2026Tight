# Phase 2 plan: work packages and briefs

Every package proves the lemmas of one blueprint area against interfaces that are already stated
(with `sorry`) in the repository, so that all packages can run in parallel: a package that uses
another one's interface relies on its statement only.

Interface files (statements fixed; their owner replaces the `sorry`):

| File | Declarations | Owner |
|---|---|---|
| `Chase2026Tight/CIM2026/Embedding.lean` | `liftAdvice`, `reduceAdvice`, `strategyOn`, `IsGoodOn`, `pullCount`, `strategyOn_id`, `isGoodOn_id`, `strategyOn_feedbackIgnoresAction` | coordinator (done, no `sorry`) |
| `Chase2026Tight/Mathlib/InformationTheory/KullbackLeibler/Pinsker.lean` | `ofReal_two_mul_sq_measureReal_sub_le_klDiv` | I |
| `Chase2026Tight/CIM2026/Lemma4_1.lean` (frozen) | `klDiv_mixture_pi_roundLaw_le` | K |
| `Chase2026Tight/CIM2026/Reduction.lean` | `exists_isGoodOn_lintegral_stoppingTime_le` | L |
| `Chase2026Tight/CIM2026/Lemma3_1.lean` (frozen) | `exists_isGood_expectedRounds_le` | L |
| `Chase2026Tight/CIM2026/Records.lean` | `klDiv_outputMeasure_le_klDiv_pi` | R |
| `Chase2026Tight/CIM2026/LowerBound.lean` | `pullsBefore`, `ofReal_le_lintegral_pullsBefore`, `ofReal_le_lintegral_stoppingTime` | S |
| `Chase2026Tight/CIM2026/Lemma4_2.lean`, `Lemma5_1.lean` (frozen) | `expectedRounds_ge_of_isGood_one`, `expectedRounds_ge_of_isGood` | S |
| `Chase2026Tight/CIM2026/Theorem6_1.lean` (frozen) | `exists_pseudoRegret_ge` | M |

The general setting (`Embedding.lean`): arms `α` and experts `ι` with reduction maps
`σ : α → Arm k`, `τ : ι → Expert k n` and sections `ρ`, `τ'` (`hσρ : ∀ a, σ (ρ a) = a`,
`hττ' : ∀ j, τ (τ' j) = j`); `strategyOn σ ρ τ τ' ε θ` is `S_θ` on these types and
`strategyOn id id id id ε θ = strategy ε θ`. Every lemma of the proof is stated in this
generality, so that it applies both to the paper's statements (reduced types, identity maps) and to
Theorem 6.1 (`α = Fin K`, `ι = Fin N`).

## Rules for every package

* Read `notes/blueprint-outline.md`, the blueprint chapters of your package
  (`blueprint/src/chapters/*.tex`), `Chase2026Tight/CIM2026/Setting.lean`, `Embedding.lean` and the
  files you build on. Lean conventions: every file `module` + `public import …` + module docstring
  + `@[expose] public section`, copyright header `Rémy Degenne` (as the existing files), every
  declaration with a docstring, `lemma` (never `theorem`, except the headline results already
  stated), Mathlib naming, lines ≤ 100 chars, no `sorry` left in your files at the end.
* **Never change** the statements of the headline theorems in `Chase2026Tight/CIM2026/` (frozen by
  the comparator challenges), the definitions in `Setting.lean` and `Embedding.lean`, the
  definitions and statements of the library files from LMLPapers
  (`Chase2026Tight/LeanMachineLearning/`, `Chase2026Tight/Mathlib/Analysis/`,
  `Chase2026Tight/Mathlib/MeasureTheory/`), nor the statements of the interface lemmas above. You
  replace the `sorry` of the interfaces you own; for anything else, add new files (you may add
  lemmas to `Chase2026Tight/LeanMachineLearning/SequentialLearning/ObliviousEnv.lean` and
  `PartialFeedback.lean` if the brief says so). If an interface statement looks false or
  unprovable, stop and report instead of changing it.
* Prove the general statement and derive the specialization; drop hypotheses the proof does not
  use from *new* lemmas. New library-shaped material goes to `Chase2026Tight/Mathlib/` (Mathlib
  path, namespaces `MeasureTheory`/`ProbabilityTheory`/`InformationTheory`) or
  `Chase2026Tight/LeanMachineLearning/` (LML path, namespace `Learning`); paper-specific material
  to `Chase2026Tight/CIM2026/` (namespace `Chase2026Tight`).
* Only edit your own files and, in the blueprint, the environments of your package. Re-read a
  blueprint chapter right before editing it (other packages edit other environments of the same
  chapters). After adding a Lean file run `lake exe mk_all --lib Chase2026Tight` (concurrent runs
  are harmless). Do not run `leanblueprint`, do not commit.
* Blueprint: add `\lean{Full.Name}` and `\leanok` to each statement the moment its declaration
  compiles (without `sorry`), and `\leanok` inside the `proof` environment when its proof is
  complete; keep labels unchanged; add a lemma (label, `\uses`) for any new intermediate step that
  deserves one. Run `python3 scripts/check-blueprint.py`.
* Check before reporting: `lake build Chase2026Tight` with no warnings in your files other than
  `declaration uses 'sorry'` coming from *other* packages' interfaces, `lake exe runLinter
  Chase2026Tight` (fix what it reports in your files), `grep -n sorry` on your files. Concurrent
  `lake build` calls in this checkout are fine.
* Look up APIs by grepping `.lake/packages/mathlib/Mathlib` and
  `.lake/packages/LeanMachineLearning/LeanMachineLearning`; test in scratch files with
  `lake env lean File.lean` in your scratchpad directory.
* Report: what was proved (names, files), any deviation from the plan, anything left.

## I. Pinsker's inequality (`lem:pinsker_bernoulli`, `lem:pinsker_event`)

Prove `InformationTheory.ofReal_two_mul_sq_measureReal_sub_le_klDiv` in `Pinsker.lean`: data
processing (Mathlib's `klDiv_map_le`) for the indicator of `E` into `Bool` (or `Prop`), then the
divergence between two laws on `Bool` in closed form, then `kl(p, q) ≥ 2 (p - q)²` by calculus
(derivative in `q`, `q (1 - q) ≤ 1/4`). Mind the cases `q ∈ {0, 1}` (`klDiv = ⊤` unless
`p = q`). State the Bernoulli version as its own lemma. Blueprint: `prereq_information.tex`.

## K. Lemma 4.1 (`lem:kl_bound`, `lem:klDiv_mixture_le`, `lem:pi_withDensity`, `lem:roundLaw_withDensity`, `lem:integral_ratio`)

Prove the frozen `klDiv_mixture_pi_roundLaw_le` (`Lemma4_1.lean`). Route (blueprint
`two_batch.tex`, `prereq_information.tex`): (1) a Mathlib-shaped bound on the divergence of a
finite mixture (`Chase2026Tight/Mathlib/InformationTheory/KullbackLeibler/Mixture.lean`):
`KL(∑ w_i P_i ‖ Q) ≤ ∑_i w_i log(∑_j w_j ∫ dP_j/dQ dP_i)` for `P_i ≪ Q` (Jensen for the concave
`log`; a uniform-weights version is enough if simpler); (2) products of measures with densities
(`Measure.pi` of `withDensity`, check Mathlib first); (3) `roundLaw ε (Expert.mk 0 v) =
(roundLaw ε Expert.zero).withDensity f_v` with `f_v = 1 + (2 c_v - 1) 2ε` (helpers in a new
`Chase2026Tight/CIM2026/RoundLaw.lean`); (4) the integrals `∫ ∏_t f_v(g_t) dP_{(1, v⋆)}^T` are `1`
or `(1 + 4ε²)^T`; (5) conclude with `log(1 + x) ≤ x`. The measures live on
`(Expert 1 n → Arm 1) × (Arm 1 → ℝ)`, supported on finitely many points: work with the explicit
definitions in `Setting.lean` (`initAdvice`, `lossLaw`, `lossRandomness`, `bern`).

## L. Lemma 3.1 (`lem:reduction`, `lem:loss_law_cond`, `lem:per_round_regret`, `lem:regret_ge_pulls`, `def:sbi_of_learner`, `lem:feedback_ignores_action_cond`)

Prove `exists_isGoodOn_lintegral_stoppingTime_le` (`Reduction.lean`) and derive the frozen
`exists_isGood_expectedRounds_le` (`Lemma3_1.lean`) with `strategyOn_id`, `isGoodOn_id` (its
hypothesis `hr` is for all `T`; use it at `T`). Route (blueprint `reduction.tex`):
`lem:feedback_ignores_action_cond` (LML-shaped, may go to `ObliviousEnv.lean`): in a run against
an environment with `FeedbackIgnoresAction`, the feedback's conditional law given (history,
observation, action) is the kernel applied to (history, observation); `lem:per_round_regret` for
`strategyOn` (the special expert of `θ` is `τ' θ`; expected losses per arm given the advice);
`lem:regret_ge_pulls`; the SBI algorithm `sbiOfLearner` (sampling rule `alg`, stopping rule
"histories of length `T`", deterministic output: the most pulled batch, ties broken by a fixed
order on `Batch k`); Markov's inequality. `IsGoodOn` is a statement on `outputMeasure` (LML's
`IdentAlg.IsPAC`): build a run of `sbiOfLearner` in `Type u` (LML's `trajMeasure` /
`isAlgEnvSeq_trajMeasure`, transported to a `ULift` if needed) with the deterministic output, and
use `IsRun.hasLaw_output`; the pseudo-regret hypothesis is about runs in `Type u`.

## R. Record representation (`def:record`, `lem:algorithm_realization`, `lem:record_representation`, `lem:events_before_pulls`)

Prove `klDiv_outputMeasure_le_klDiv_pi` (`Records.lean`). This is the core of the proof; read
`notes/blueprint-outline.md` (section 4, Lemmas 4.2 and 5.1) and `prereq_sequential.tex`. Idea:
under `S_θ`, the advice of batch `u` is redrawn only after a pull of batch `u`, so the successive
(advice of batch `u`, correct arm of batch `u`) at the pulls of batch `u` — the *records* — are
i.i.d., whatever the algorithm does between the pulls; all the other variables of a run (other
batches, arm-`0` losses, unobserved losses, the algorithm's randomness) have laws that do not
depend on `θ ∈ {0} ∪ {(u, v) : v}`. A run of `B` stopped by its `M`-th pull of batch `u` (`hB`)
only uses the first `M` records, so the output law under `S_θ` is the image of
`(law of M records under θ) ⊗ μ` by a map not depending on `θ`, and the mixture over `v` commutes
with the image; conclude with the data processing inequality (Mathlib's `klDiv_map_le`) and the
projection of a round of the two-batch game (`roundLaw`, `k = 1`) onto a record.
You choose the formal route: a pathwise construction of a run (realize the algorithm's kernels
with independent uniform variables, finite action and output spaces; prove the constructed
processes form an `IsAlgEnvSeq` and use LML's `isAlgEnvSeq_unique` / `IsRun.hasLaw_output`), or a
kernel-level computation of `stoppedHistMeasure` / `outputMeasure` (Ionescu-Tulcea, LML's
`trajMeasure`). Put generic material (realization of algorithms, laws of records of
"state refreshed by the action" environments) in `Chase2026Tight/LeanMachineLearning/` with
Mathlib/LML-quality statements, and the paper-specific part in `Chase2026Tight/CIM2026/`. Expect
this package to be long; report progress precisely if you cannot finish (which sublemmas are
proved, which are stated with `sorry` and their statements).

## S. Lemmas 4.2 and 5.1 (`lem:two_batch_general`, `lem:two_batch`, `lem:many_batches_general`, `lem:many_batches`)

Prove `ofReal_le_lintegral_pullsBefore` and `ofReal_le_lintegral_stoppingTime` (`LowerBound.lean`)
and derive the frozen `expectedRounds_ge_of_isGood_one`, `expectedRounds_ge_of_isGood`
(`Lemma4_2.lean`, `Lemma5_1.lean`) with `strategyOn_id`, `isGoodOn_id` and
`ln(n/10) ≤ ln(1 + n/8)`. Use the interfaces `klDiv_outputMeasure_le_klDiv_pi` (R),
`ofReal_two_mul_sq_measureReal_sub_le_klDiv` (I) and `klDiv_mixture_pi_roundLaw_le` (K) by their
statements (they are `sorry` until their packages finish). Route (blueprint `two_batch.tex`,
`many_batches.tex`): if `τ = ∞` with positive probability the bounds are trivial; with
`T⋆ = ⌊ln(1 + n/8)/(4ε²)⌋` and `M = T⋆ + 1`, build from `A'` the identification algorithm `B`
that stops when `A'` stops or at its `M`-th pull of batch `u`, with Boolean output "`A'` stopped
and output batch `0`" (output kernel by cases on the stopped history); relate the output laws of
`B` to runs of `A'` (same sampling rule; `B`'s stopping time is the minimum); then Pinsker, Lemma
4.1 (`((1 + 4ε²)^{T⋆} - 1)/n ≤ 1/8`, so the gap is `≤ 1/4`), goodness of `A'` under `S_0` and
`S_(u, v)`, `P_0(N_u(τ) > T⋆) ≥ 0.65`, `E_0[N_u(τ)] ≥ 0.65 (T⋆ + 1)`. The second lemma: the
stopping time is at least the sum over `u` of the pulls of batch `u` before it.

## M. Theorem 6.1 (`thm:main`, `def:embedding`, `lem:reduction_ext`)

Prove the frozen `exists_pseudoRegret_ge` (`Theorem6_1.lean`) from the interfaces
`exists_isGoodOn_lintegral_stoppingTime_le` (L) and `ofReal_le_lintegral_stoppingTime` (S) by
their statements. Route (blueprint `main.tex`): for `K ≥ 3`, `N ≥ 2K`, `k = (K - 1)/2`,
`n = (N - 1)/k`, build `σ : Fin K → Arm k`, `ρ`, `τ : Fin N → Expert k n`, `τ'` with `hσρ`, `hττ'`
(a new file `Chase2026Tight/CIM2026/FinEmbedding.lean`, e.g. through `Fintype.equivFin` and
`Fin.castLE`; extra arms and experts go to arm and expert `0`); the adversary is
`strategyOn σ ρ τ τ' ε θ` (`strategyOn_feedbackIgnoresAction`; losses in `{0, 1}`: prove
`FeedbackIn`); `ε = √(k L / (50 T))`, `L = ln(1 + n/8)`; argue by contradiction: if every `θ` has a
run with pseudo-regret `< b`, then all runs do (the pseudo-regret only depends on the law of the
run: LML's `isAlgEnvSeq_unique`), so the reduction gives a good SBI algorithm with at most `T`
rounds, contradicting the lower bound `k L/(8ε²) = 50T/8`. Arithmetic: `k ≥ K/4`, `n ≥ N/K`,
`n ≤ 4N/K`, `ln(1 + x/8) ≥ ln(x)/4` for `x ≥ 2`, `ln(1 + n/8) ≤ ln(N/K)`, `ε ≤ 0.1`; pick an
explicit `c` (e.g. `c = 1/(10⁵)` or smaller, whatever the inequalities give).

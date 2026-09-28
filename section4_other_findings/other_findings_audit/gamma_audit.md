# Independent mathematical audit: the sharp logarithmic coefficient

Date: 2026-09-25. Reviewer: independent Codex subagent. This is an AI-assisted mathematical review, not a Lean certificate or human expert review.

## Scope and verdict

Reviewed the entire archived chapter `archive_v1/other_findings_source/02_gamma.tex` (474 lines), including all proofs, the two exact minimax examples, and the NP-completeness reduction. Source SHA-256:

`8bd707abc3ffe14517e6a33ee4ccf8b3fbb76af511b95206c2aa2f701510a47f`

**Verdict: no material mathematical defect found in the chapter under its explicitly stated semantic model.** The arguments establish the claimed coefficient, upper and lower bounds, exact examples, and complexity results. This audit was performed directly from the chapter; the earlier audit conclusions cited in the chapter were not used as evidence.

No correction to a theorem statement or proof is required by this review. Two optional wording clarifications are recorded below. The semantic assumptions and limits are essential: a fixed finite target family, finitely many binary groups, distinct positive inputs, no target-dependent correctness feedback, freshness relative to observed inputs, and semantic access to target/profile information. This is not an audit of an executable online algorithm or an end-to-end formalization.

## Proof checks

### 1. Coefficient, attainment, and positivity — source lines 91–125

The coefficient is a maximum of positive-part sums over a finite union of rational polyhedra. For each fixed anchor and selected subset E, the objective is linear, the feasible region is nonempty (a = 0 with any prior), and each selected profile potential is at most one. The objective is therefore bounded above. Standard finite LP attainment gives an optimum, and a rational optimum exists even if the feasible region has lineality. The finite maximum over target subfamilies, anchors, and selected subsets is consequently attained and rational. No compactness of the original feasible potential region is being assumed.

The binary exposing direction in the positivity proof is correct: for b_j = 2v_j − 1, b·(v − w) is the Hamming distance from v to w. Since v is a finite-cell profile, it cannot be an infinite-cell anchor. Maximizing b·u over infinite profiles gives strictly positive d = b·(v − u), infinite-profile potentials at most zero, and all profile potentials at most 1/|F| after normalization. Every outside point misses at least one member of F, so the uniform prior gives outside error at least 1/|F|. Thus the proposed pair is feasible, and Γ_F ≥ c_v/|F|. This also verifies the zero-coefficient characterization.

### 2. Tangent program, strong duality, and mass — source lines 127–183

The listed output types correctly represent all relevant feature/error choices. An unexhausted finite core cell has a safe fresh representative; an exhausted cell has only observed representatives and costs one for every consistent target. Outside-core points have never been observed because the entire sample lies in the core. Removing zero-displacement types is valid because the separate fresh anchor has the same profile and no error.

The primal is feasible by assigning s_v units to the corresponding finite-profile type. Its crucial bound is exact: because the anchor is binary, all displacements have the same sign in each coordinate. Therefore the L1 norm of their nonnegative combination equals the sum of their L1 norms. Every retained displacement has norm at least one. This proves total flow mass ≤ ||h||_1 ≤ m b, including h = 0 (where every retained flow must vanish).

The feasible q-set is closed and bounded; minimizing the continuous maximum of the target costs gives a primal optimum. The displayed Lagrangian has the right signs. Free D forces the prior multipliers to sum to one, and nonnegative flow forces precisely the displayed dual inequalities. Finite LP strong duality applies because the primal is feasible with finite optimum.

A tangent dual pair satisfies the coefficient constraints, with the stronger zero upper bound at unexhausted finite cells. Positive finite-profile potential is thus possible only at exhausted cells. The resulting objective bound by Γ_F is valid even when some potentials are negative. Conversely, exhausting exactly the positive-potential cells of a coefficient maximizer gives a valid sample-count vector; every remaining finite cell has nonpositive potential and is compatible with its fresh type. The resulting dual objective is exactly Γ_F. These checks prove both directions of the tangent characterization, rather than only the upper bound.

### 3. Adaptive upper bound and summation — source lines 185–214

At t ≥ T_0, a version-space core containing t distinct points cannot be finite because t > B_fin. Its finite-profile sample count b is at most B_inf. The tangent mass bound and t ≥ m B_inf make every proposed normalized flow a probability submeasure. Filling the remainder with fresh anchor mass gives the displayed mean and simultaneously bounds error for every consistent target.

Mixing over observed infinite-cell anchors exactly recovers the empirical feature mean. The t = b branch is also valid: the anchor term vanishes from the mean, and any anchor may be used. The fresh-anchor mixture differs from the empirical mean coordinatewise by at most b/t, including that branch. The proposed interpolation therefore meets the representation tolerance and gives the pointwise error bound Γ(1/t − α/B_inf)_+.

This reasoning is conditional on each realized history, so it remains valid when subsequent observations depend on earlier draws. The asserted conditional sum bound implies the expectation bound by the tower property and Tonelli's theorem.

The decreasing-sum estimate is correct for the integer B = B_inf ≥ 1:

sum from t = B of (1/t − α/B)_+
≤ (1 − α)/B + integral from B to B/α of (1/x − α/B) dx
= ln(1/α) − (1 − α)(1 − 1/B)
≤ ln(1/α).

The B_inf = 0 case is explicitly separated and gives error-free generation after the finite burn-in. No division by zero or implicit positivity assumption remains.

### 4. Fixed-target lower bound and presentation quantifiers — source lines 216–236

The chosen positive finite cells contain exactly W points and have total potential Γ. Presenting them first and then using an infinite anchor cell gives empirical potential Γ/t at every later prefix. The pointwise domination of potential by prior-averaged error covers all cases: observed points, fresh core points, and outside points. Representation changes the expected potential by at most α||a||_1.

The common prefix is deterministic and valid for every target in the chosen subfamily. Along it, the learner's entire distribution of internal states and outputs is independent of which of those targets is fixed, because no correctness feedback is supplied. Averaging cumulative expected errors over the prior therefore yields some single fixed target with at least the claimed expectation. That target can depend on the learner and on α, as the minimax supremum permits, but it is not selected after observing the learner's private random outcomes.

Only a finite common prefix is required: through floor(Γ/(αA)). Under α < Γ/(AW), this includes all W initial points and every positive summand. Completing that prefix separately to each infinite target cannot remove earlier errors. Thus the proof works for complete injective presentations as well as unrestricted injective streams. The decreasing-sum/integral direction and the displayed constant are correct. The auxiliary inequality Γ ≤ AW follows from |a·(v − u)| ≤ ||a||_1 for binary profiles.

### 5. Exact examples — source lines 238–291

**Private tails.** Before a private observation, the only possible sample points are in the shared finite group G and shared infinite set R. Before G is exhausted, each observed profile has a fresh common representative. After exhaustion, uniform randomization over private tails gives error 1 − 1/N per unit of necessary group mass. A private observation identifies the target. The uniform-prior lower bound charges every fresh group point by exactly that factor and every stale group point by one; a shared finite prefix forces the entire positive series. In the coefficient calculation, constraints from tails outside a chosen subfamily only add a ≤ 1 and do not invalidate the stated optimum. Singleton subfamilies indeed have no finite cells.

**Parity.** Distinct odd profiles differ in a positive even number of coordinates. Flipping one differing coordinate in both turns them into two even profiles with the same midpoint. Averaging over all unordered pairs reproduces the mean of any set of at least two observed odd profiles. Thus exact fresh matching in that case is valid. With one observed odd profile, moving its mass equally to its m even neighbors changes each coordinate by precisely the moved mass divided by m. The affine potential 1 − Hamming(v,w) is at most the stale-output indicator at every point and has linear L1 norm m, proving the matching lower bound. The same potential gives the stated fresh-discrepancy lower bound. The cases m = 1 and mα ≥ 1 are explicitly and correctly handled. Inferring Γ = 1 from the exact series and the already-proved asymptotic theorem is noncircular.

### 6. Complexity, reduction, and certificate size — source lines 294–448

The special known-target coefficient is obtained correctly by taking the zero profile as the only infinite anchor and having no outside points. Negative coordinates must remain allowed; the reduction uses c = −1.

All listed reduction profiles are distinct for a simple loop-free graph, have weight at most three, and have the stated counts. A cut produces a feasible potential with value M(n+3) + n + cut size. For an arbitrary feasible potential:

- Singleton positive parts sum to at most one per vertex, because each coordinate and each pair sum is at most one.
- If the total heavy deficit σ ≥ 1, the heavy penalty M = 2e+1 strictly dominates the maximum possible 2e edge contribution.
- If σ < 1, all heavy potentials are positive, so writing their exact deficits δ is legitimate. Clipping x_i below at zero preserves x_i ≤ clipped x_i ≤ 1 and gives y_i ≤ 1 − clipped x_i. The two edge positive parts are at most the clipped coordinate difference in absolute value plus 2(δ_d+δ_f). The threshold/coarea identity bounds the sum of absolute differences by MaxCut(G). Since δ_d+δ_f ≤ σ and M > 2e, no positive heavy deficit improves the cut objective.

This proves the exact identity for all feasible potentials, including arbitrarily negative coordinates. It also justifies the stronger statement that every maximizer has zero heavy deficit. The proof covers e = 0 as well.

The construction has 3n+3+2e listed finite profiles, dimension 2n+3, maximum count 2e+1, and polynomial total expanded finite population. Hence it is a polynomial many-one reduction from ordinary unweighted MaxCut threshold decision. Its integer-valued identity supports exact hardness and additive error strictly below 1/2 by rounding. It does not establish a multiplicative approximation barrier, as the chapter correctly says.

For NP membership, a selected subset of profiles linearizes the positive-part objective in the correct direction. At an attaining potential, selecting precisely its positive profiles gives the converse. The resulting rational feasibility system has polynomially many variables and constraints and polynomial coefficient bit length. The standard small rational witness theorem for rational polyhedra gives a certificate of polynomial bit length; free potential variables do not obstruct that theorem. Equivalently, a deterministic polynomial-time LP feasibility test can be used after the nondeterministic subset guess.

For the general explicit signature, guessing F and an infinite anchor requires only polynomially many bits. Scanning the listed joint rows and aggregating finite cardinalities computes the core and outside types in polynomial time. Summing binary-encoded counts increases bit length by at most the logarithm of the number of rows. Guessing the selected finite-profile subset then gives a rational LP of polynomial size. The proof therefore establishes general NP membership without enumerating all target subfamilies in the verifier. Appending a universal group cancels in every displacement, so the stated covered-group variant is also valid.

## Independent computational diagnostics

Reproducible script: `gamma_lp_checks.py` in this directory. Full results: `gamma_lp_checks.json`. Run:

```text
python3 output/pdf/other_findings_audit/gamma_lp_checks.py
```

Environment: Python 3.11, SciPy 1.11.4, HiGHS through `scipy.optimize.linprog`. The script constructs the coefficient LPs and tangent primal separately. All tests passed, using 3,450 LP solves:

- 30 seeded random joint signatures with two groups and two targets; 86 infinite-core subfamilies. Exhaustive finite-count/anchor enumeration gave 432 tangent cases. The maximum tangent value equaled the separately computed Γ_F with maximum reported residual 0.0. Mass bounds, positivity, and the zero case also passed.
- Private tails for N = 2,3,4,5 and B = 1,2,5 matched B(1−1/N).
- Parity profiles for m = 1,2,3 gave Γ = 1.
- Exhaustive enumeration of all positive-objective subsets for MaxCut gadgets on zero vertices, one isolated vertex, two isolated vertices, and a single edge gave Γ = 3, 5, 7, and 18, respectively, exactly matching the reduction identity numerically.

These finite floating-point checks are supplementary diagnostics, not exact certificates or a substitute for the proofs. In particular, the one-edge gadget does not numerically validate every graph; the general graph claim rests on the independent deficit/coarea argument above.

## Optional clarifications and limitations

1. At source line 151, write `s_v ∈ {0,...,c_v}` rather than only `0 ≤ s_v ≤ c_v` to make the integer sample-count domain explicit. The existing prose already calls them counts, and the maximizing vector uses only 0 and c_v, so this does not change the result.
2. At source line 444, the phrase “high-dimensional target intersections” is imprecise. “The hardness already holds for one known target, with no outside-target points” states the proved restriction directly.
3. The source's statement that earlier audits found no substantive gap was not used in this review. Mathematical status should continue to distinguish written proofs from formal verification. No Lean code was inspected, compiled, or claimed to certify these results.
4. This audit checks the new combined model as written. It does not independently certify source-paper priority, the exact conventions of P09/P29, or the bibliography; those should be checked separately against the original papers. The standard NP-completeness of unweighted MaxCut is used as the reduction's external starting theorem.
5. No manuscript source was modified. This verdict is tied to the archived file and hash above; substantive changes to a theorem or proof require checking the changed passage again.

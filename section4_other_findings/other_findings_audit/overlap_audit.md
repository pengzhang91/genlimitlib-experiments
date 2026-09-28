# Independent audit of the overlap chapter

Reviewed source: `output/pdf/archive_v1/other_findings_source/01_overlap.tex`.
SHA-256: 5f8d0a667dc346a1a9733dd5f69c942fe15a11cbb08cca649c066fa745e0786f.

This is a fresh mathematical audit of the full written argument, not a reuse of the archived pass verdict. I did not author this chapter and made no changes to the source. Every stated lemma, both main theorems, the exact bottleneck identity, and the sharpness construction were checked. Standard Hahn–Banach, Riesz representation, and elementary finite probability facts are used as established results with their hypotheses checked here. This is an AI-assisted written-proof review, not human expert review or formal verification.

## Verdict

**No material mathematical error or missing proof obligation found under the stated hypotheses.** The completed-cell characterization and the two-block bottleneck/rate proofs are valid as written. The finite LP stress tests also agree with the exact formula. A small wording repair is recommended: in `ov:bottleneck`, replace “Every positive value of this supremum is attained” by “If the supremum is positive, it is attained.” The proof establishes attainment of the optimal positive value, not the existence of a witness at every smaller positive real value.

The scope must remain: countably infinite target, countably additive laws, finite forbidden set, finite dual VC dimension for finite signed-witness reduction, and a union of two dual-VC-at-most-one blocks for the exact formula. For the square-root bound, the linear capacity assumption concerns completed cells of every arity, and the displayed simple rate requires n >= 2 C_0. The infimum over fresh laws need not be attained.

## 1. Model, completion, and dimension — `ov:completion`

- Countability of L gives a compact metrizable test closure K inside {0,1}^L. Adjoining the empty test has no effect on discrepancy, dual VC dimension, the Boolean costs, or finite-cell capacities. It supplies a harmless nonempty test family when needed.
- An element of K has original-test approximants agreeing on successive finite prefixes of L. Dominated convergence for each of P and Q proves preservation of the discrepancy supremum. Countable additivity matters here.
- To transfer dual shattering of k completed tests, choose one witness point for each of the 2^k patterns and approximate each test simultaneously on this finite witness set. The approximating original tests remain distinct because their columns are distinguished by these witnesses. Inclusion gives the reverse dimension inequality.
- Truncation of a probability law on the countable fresh set, followed by moving the remaining mass to a fixed fresh point, changes every test probability by at most the truncated mass. The fresh set is nonempty because L is infinite and F finite. Thus finite-support laws have the same infimum.
- The empty forbidden-set case creates no counterexample: there is no probability law supported on it, so the quantified statement is vacuous.

## 2. Functional-analytic distance — `ov:separation`

The norm-closed convex hull H of fresh evaluations is nonempty. Its finite convex combinations are exactly finite-support fresh profiles. The previous lemma makes distance from f_mu to H equal to e_F(mu), even if the infimum over laws is not attained. All profile functions are continuous: evaluations are clopen indicators, and the weighted sum for a countably additive probability converges uniformly.

The real Banach-space distance formula for a nonempty closed convex set is
`dist(f,H) = sup_{||ell||<=1} (ell(f) - sup_{g in H} ell(g))`.
Zero is included among the functionals, so the zero-distance case is correct. Here H is bounded, hence its functional supremum is finite. Riesz representation applies to compact Hausdorff K and identifies the dual norm with signed-measure total variation. Continuity of ell and linearity justify replacing the closed-convex-hull supremum by the supremum over individual fresh evaluations. No compactness or weak compactness of fresh output laws is needed.

## 3. VC approximation and signed sparsification — `ov:vc`, `ov:finite-witness`

- The finite-trace recurrence used for Sauer's bound is correct, including VC dimension zero and zero coordinates. For clarity in a rewrite, take v explicitly to be a nonnegative integer upper bound.
- Countability of the measurable range family makes the bad-sample supremum measurable and permits a measurable “first bad range” choice.
- Conditional on the original sample and that range, the independent ghost sample has variance at most 1/(4m). The assumption m eta^2 >= 2 makes the probability of ghost error exceeding eta/2 at most 1/2. The symmetrization factor two is therefore valid.
- Independent swaps preserve the joint sample law. Conditional on the pooled points, each trace difference is a signed sum with coefficients bounded by one. The exponential estimate gives the stated two-sided bound 2 exp(-m eta^2/8), and Sauer plus the union bound yields 4 Pi_v(2m) exp(-m eta^2/8).
- The evaluation ranges R_x on K are clopen and countably indexed by L. Their VC dimension is exactly the dual dimension being assumed. Jordan parts of mass zero may be skipped. Multiplying approximants by their original masses gives total variation at most one, support size at most 2m, and uniform potential error at most eta.
- Uniform potential error eta changes each of the mean and fresh supremum by at most eta, so the separator gap changes by at most 2 eta. This proves the equality with the supremum over finite potentials, including zero discrepancy and repeated atoms whose coefficients must be combined.

## 4. Completed-cell theorem — `ov:criterion`, `ov:quantitative`

Necessity does not require VC dimension. On an exhausted finite cell, each fresh point violates at least one prescribed literal, so the sum of marginal discrepancies is at least one. Arity at most r therefore forces discrepancy at least 1/r. Unbounded finite-cell sizes yield such samples above every n.

For sufficiency, at most Pi_v(r) realized cells partition L on the r selected completed tests. Every infinite cell has a fresh representative. Finite cells together contribute at most Pi_v(r) Bbar_r observed points. Between any two points a unit-l1 test potential changes by at most one, not two: every indicator difference lies in {-1,0,1}. Moving the finite-cell empirical mass arbitrarily therefore gives the stated bound. Adding the two eta sparsification losses and taking the sample supremum proves the quantitative inequality. Choosing eta before n proves convergence. No uniform growth bound in r is tacitly required for this qualitative implication.

## 5. Laminar trees and Boolean integral cost — `ov:tree`, `ov:cost`

For finitely many tests in one block, complementing those containing a fixed z forces all oriented sets to exclude z. If two such sets overlap and neither contains the other, the points in their intersection and two differences, together with z, give all four patterns, contradicting dual VC dimension one. Removing empty sets and duplicates leaves a finite laminar tree rooted at L.

The residual atoms partition L. Empty residual atoms must be retained as vertices; the chapter does so. Path telescoping represents arbitrary atom values with coefficient cost equal to edge variation. Complementing back affects only signs and the free constant. Every Boolean combination of the selected tests has a binary atom labeling.

For the reverse inequality, an arbitrary real representation can first be oriented and combined without increasing l1 norm. Root-path sums realize the same function and have edge variation at most that norm. Clamping to [0,1] preserves every actual Boolean value and cannot increase variation. Threshold coarea then gives some binary labeling with integer boundary cost no larger than the original norm. The nonempty collection of all such integer costs has a least member. Since every real representation bounds that least integer from below and that integer is itself realizable, it is exactly the infimum in `ov:cost`. This establishes attainment across all finite representations, without an unjustified compactness argument over an infinite test family. Zero cost gives only the two constant sets.

## 6. Exact two-block bottleneck — `ov:bottleneck`, `ov:exact`

The union of the two completed blocks is the completion of their union. A shattered collection with at least three tests would assign at least two tests to the same block; those two would realize all four patterns. Thus the union has dual VC dimension at most two and the finite-witness corollary applies.

The easy direction is sound: U cap V subseteq F implies Q(U)+Q(V)<=1 for every fresh law. Attained Boolean representations bound each Boolean discrepancy by its test discrepancy times its cost. Costs zero are handled separately when the denominator is zero.

For the difficult direction:

1. Assign each finite separator test to one block; orientations and duplicate merging produce two trees with combined variation <=1.
2. The maxima u=max f, v=max g, and M=max_fresh(f+g) exist because the potentials take finitely many values. Delta=u+v-M>=0. Delta=0 makes the separator gap nonpositive.
3. For Delta>0, clamp the affine transforms on every tree vertex, including virtual vertices. Lipschitz contraction gives combined variation <=1/Delta. On actual points the unclamped values are <=1, so clipping can only increase them. The gap inequality follows exactly from M=u+v-Delta.
4. At every fresh point, alpha+beta<=1, including the cases where one unclamped value is negative. The complementary strict/weak level sets therefore have exhausted intersection.
5. The bottleneck inequality also holds at zero total cost, since both sets are constant and cannot both be L when F is finite. Threshold boundary counts dominate the minimal Boolean costs. Coarea integrates these counts to <=1/Delta; endpoint conventions affect only finitely many thresholds. Integrating gives G(h)<=D.
6. Finite signed witnesses then imply the full upper bound, without asserting attainment of a primal law.

For dual attainment, F has finitely many trace pairs, each fixing its numerator even when mu has zero masses. For each admissible trace pair, the achievable positive integer denominators have an attained minimum. The maximum over finitely many resulting ratios is attained whenever it is positive. Admissibility must continue to mean the entire U cap V is contained in F, not merely that its observed trace lies there.

## 7. Component counting and the sharp rate — `ov:sharp`, `ov:sqrt`

For positive costs p,q, each 1-labeled component has at least one cut boundary edge. Each crossing edge belongs to exactly one 1-component, so their boundary sizes sum to p (respectively q), and their numbers are at most p and q. Virtual/empty components do not invalidate these inequalities.

A component equals its highest-node set minus the subtrees at downward exit edges, with the entering literal omitted for a root component. It is therefore a completed cell of arity at most its boundary size. The cells for 1-components are disjoint. Pairwise intersections of the two collections partition U cap V; nonempty ones are finite because that intersection is in F. If the component boundary sizes are b_j,c_k, cell growth gives total size at most
`C_0 sum_{j,k}(b_j+c_k) <= 2 C_0 p q`.
Duplicated literals or inconsistent pairs only decrease the true arity or give empty cells, so they cannot spoil the upper bound.

The positive numerator is at most both one and mu(U cap V), the latter bounded by rho times cardinality. With a=C_0 rho and s=p+q, the ratio is bounded by `min(1/s,a*s/2)<=sqrt(a/2)`. If one cost is zero, its set must be L to give positive numerator; the other set is finite and its component bound gives ratio <=a. This establishes the stated general bound and then the square-root result when a<=1/2. The zero-cost branch is essential; removing the restriction n>=2C_0 would make the simple square-root assertion false in general.

## 8. Fixed-target sharpness

The reservoirs, pair cells, gadgets, and background are pairwise disjoint as required. Each point occurs in at most two tests. A sequence of distinct tests converges pointwise to the empty set. If a convergent sequence has an infinitely recurring test, that constant subsequence fixes its limit. Consequently completion adds only the empty test; no extra finite cells have been overlooked.

A nonempty cell with no positive nonconstant test contains background; one with exactly one positive test retains that test's infinite private reservoir unless inconsistent. Compatible row/column positives isolate exactly a two-point pair cell; other positive combinations are empty. Thus Bbar_1=0 and Bbar_r=2 for r>=2, giving C_0=1 across the whole fixed target.

For S_k, the sum of empirical masses over the local 2k tests is two, while every fresh point belongs to at most one local test. A discrepancy of at least 1/(2k) follows. The uniform law on one point from each private reservoir attains that discrepancy, including zero discrepancies for all other gadgets' tests. Since |S_k|=2k^2, the asserted coefficient is exactly attained along infinitely many sample sizes in one target.

## 9. Counterexample attempts and independent finite checks

Analytic edge checks:

- Constant-only blocks have zero discrepancy and zero bottleneck; the zero-denominator convention is consistent.
- Let one block contain the singleton {z}, let F={z}, and mu be its point mass. The discrepancy is one. The constant second block gives a bottleneck with costs (1,0). This confirms the necessity of handling the one-zero-cost branch; the unrestricted square-root formula at n=C_0=1 would incorrectly give 1/sqrt(2).
- Primal nonattainment is real: let L={0,1,2,...}, F={0}, mu=delta_0, and tests A_n=L minus {n} for n>=1 in one block. The discrepancy of any fresh law is sup_n Q{n}>0, but uniform laws on larger finite fresh sets make it tend to zero. The bottleneck gives zero, consistent with the theorem's careful distinction between dual positive attainment and primal attainment.
- Additional forbidden zero-mass points must remain excluded. The proof uses U cap V subseteq F throughout and the finite tests below explicitly include this case.

Reproducible numerical stress test: `overlap_finite_lp_check.py` with seed 20260926. It generates 160 finite two-laminar point-type models, independently computes the primal fresh-discrepancy LP, and compares with exhaustive Boolean bottlenecks. For every Boolean trace in each model it also compares the minimum integer tree boundary with a separate real-coefficient l1 representation LP. Models include missing/virtual tree vertices, sample mass on types that still have fresh copies, exhausted types, and exhausted types of zero mu-mass. An infinite fresh reservoir can realize each finite model on a countably infinite target.

Result: PASS in all 160 models; maximum primal/bottleneck absolute difference 3.3306690738754696e-16. There were 61 models with empty tree vertices and 42 with zero-mass forbidden types. Full output is in `overlap_finite_lp_check.json`.

These are floating-point LP checks, not exact certificates and not substitutes for the mathematical argument. They do not validate the infinite completion, Hahn–Banach, or VC passages; those were reviewed separately above. No literature-priority conclusion, Lean verification, or human expert certification follows from this audit.

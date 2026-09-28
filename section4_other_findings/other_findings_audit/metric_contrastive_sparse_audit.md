# Independent mathematical audit of Chapters 3–5

Audit date: 2026-09-25. Sources: the archived first-version files `03_metric.tex`, `04_contrastive.tex`, and `05_sparse_holes.tex` in `output/pdf/archive_v1/other_findings_source`. This review reads their statements and proofs directly; it does not treat earlier audit notes or compilation claims as evidence of correctness. No source file was edited.

**Verdict:** I found no counterexample or material proof gap in the stated results. The hypotheses that restrict the conclusions are doing real work and should survive the revision. In particular, the metric claims are semantic and concern unbounded targets and countable classes; contrastive threshold success quantifies over finite crossing histories, whereas eventual success uses complete presentations; the sparse-hole diagonal fixes its target before the algorithm tape; and the deterministic envelope lower bound assumes success on every full presentation, not only the increasing presentation. The probability-one success event in the envelope upper bound may depend on the target.

This is a mathematical proof audit, not a new Lean certification or a literature-priority assessment. I did not independently verify the chapter's descriptions of particular source papers or historical compilation logs.

## Chapter 3: metric generation and proper completion

### Model and preliminary obligations — pass

Locations: lines 37–100 and Lemma `mt:packing`, lines 104–135.

- Cover centers are in the ambient space (X), not necessarily in the covered set. This convention is maintained in the proofs. The internal-net construction explicitly starts with radius (b/2) and obtains radius (b); it does not incorrectly transfer centers at unchanged radius.
- Closed-ball conventions are consistent: pairwise distances strictly greater than (a) force distinct covering balls of radius (a/2), and chosen outputs at distance strictly greater than (b) avoid closed forbidden balls.
- For finite samples, (N_m(a;S)\le |S|\le t), including histories with repeated observations. This is the key link between a covering threshold and scheduler time.
- Every finite positive history extends separately to a complete presentation. An unbounded target supplies arbitrarily large sets separated by more than (2a), so its complete presentations eventually cross every finite radius-(a) covering threshold. Thus the model avoids a vacuous threshold guarantee.
- Empty samples have cover number zero and cannot meet a positive threshold. Empty target classes are expressly vacuous. Empty finite intersections are totally bounded and cause no obstruction.

The finite-union-of-bounded-balls observation is valid in an arbitrary metric space: choose any one of the finitely many centers and use the triangle inequality. For an empty union, the conclusion of the escape lemma follows because an unbounded set is nonempty.

### Lemma `mt:obstruction` — pass

Location: lines 144–166.

Obligation: a single positive finite history must simultaneously meet all finitely many target-dependent thresholds and leave no legal common output.

The proof satisfies this. A bounded non-totally-bounded intersection (A) has (N_m(a;A)=\infty) for some (a>0). It is nonempty. Taking the maximum of finitely many thresholds yields (D), and (D) points separated by more than (a) force cover number at least (D) at input scale (a/2). Adding (c\in A) preserves that lower bound. Boundedness allows (A\subseteq B(c,b)) for a positive (b), even if the original boundedness witness had its center outside (A). All targets force the same output into (A), while the observed (c) makes every such output forbidden.

The finite history extends to each possible target separately. A shared complete text is neither asserted nor needed.

### Theorem `mt:intersection` — pass

Location: lines 170–249.

Finite-class obligation: all bounded version-space cores must have a common finite covering bound at a fixed scale. There are finitely many nonempty subfamilies, so taking the maximum of their finite covering numbers is legitimate. A sample above that bound has an unbounded consistent core. Selecting a point outside the finite forbidden union yields one legal output for all consistent targets. The fallback makes the generator total.

Countable-class and all-scale obligations:

1. Enumerate the class, repeating members in the finite case. At time (t), inspect only indices (j\le t). The largest eligible index therefore exists whenever any is eligible.
2. Fix a true target with first index (z), and a scale pair ((a,b)). Only intersections of subfamilies of the first (z) targets enter (E_{z,a}), so this maximum is finite.
3. Choose (D_{L_z}>\max(E_{z,a},z,b)). A positive history above the threshold has (t\ge N_m(a;S)\ge D_{L_z}>z,b).
4. The core at index (z) contains (S) and cannot be bounded, since that would imply (N_m(a;S)\le E_{z,a}). Thus (z) is eligible.
5. The selected index is at least (z). The true target remains in that version space, so its core lies inside the true target. The selected point is more than (t>b) from every observation.

The constructed generator depends on neither input scale nor output scale. Only its correctness thresholds do. It does not take a maximum over infinitely many target thresholds. Arbitrary real scales cause no issue, since an integer threshold can dominate (b). At (t=0), or at an unrealizable history, the explicit fallback suffices. Repeated targets in an enumeration and repeated observations do not affect the argument.

No extension to uncountable target classes follows from this scheduler; the chapter correctly does not claim one.

### Lemma `mt:tails` — pass

Location: lines 267–282.

Each successive choice excludes a bounded set: the bounded obstruction, a finite previously selected set, and a finite-radius ball about a fixed point. Unboundedness of (X) guarantees another point. Taking the two choices successively ensures disjoint tails; requiring distance greater than the stage number ensures that each tail is unbounded. This also works when (A) is empty. The resulting targets are distinct and intersect exactly in (A).

### Theorem `mt:proper` — pass

Location: lines 285–347.

The implications from the bounded-set condition to the generation conditions, and back via the two-tail obstruction, are valid.

The completion step keeps track of legal covering centers:

- If the completion is proper, the closure of a bounded (A\subseteq X) is compact. Finitely many open radius-(a/3) balls cover it. Moving their centers into (X) by less than (a/3) gives an ambient-(X) cover at radius (a).
- Conversely, approximate each point of a bounded (B\subseteq\widehat X) by a point of (X) within (a/3). The approximating set is bounded in (X), hence has a finite radius-(a/3) cover. This covers (B) at radius (2a/3), proving total boundedness at every scale.
- For a closed bounded (B\subseteq\widehat X), the nested closed-set argument correctly proves compactness from completeness and total boundedness. At each stage the chosen closed subset still lacks a finite subcover and has vanishing diameter. Its Cauchy limit belongs to every chosen subset. An open-cover neighborhood of that limit eventually contains a whole chosen subset, giving the contradiction.

The empty bounded set is trivially compact and totally bounded; the contradiction proof automatically addresses only a nonempty set. Completion is essential: the rational-line example correctly distinguishes the result from properness of (X) itself. The row-obstruction example is a valid metric and gives the stated failure at input radius (1/3) and output radius (1).

## Chapter 4: contrastive realization, widths, and coloring

### Theorem `thm:ca:realization` — pass

Location: lines 13–46, with the model at lines 10–11.

For countable (V), the collection of its finite subsets is countable, so the face-indexed block universe is countable. Each support is infinite because it contains (C), proper because it excludes its singleton block, and distinct from every other support by the singleton-block witnesses.

Necessity of (F\in K): coverage of even one (c\in C) forces a common negative endpoint. Its block face contains (F), so downward closure supplies (F\in K).

Sufficiency: for (x\in B_\sigma) positive for at least one target in a nonempty face (F), the face (\tau=F\setminus\sigma) is nonempty. A point in (B_\tau) has exactly complementary membership on (F). The blocks are distinct because (\tau\ne\varnothing) and (\tau\cap\sigma=\varnothing), so the unordered edge has distinct endpoints. Enumerating the union of all positive supports gives coverage for every target. This proof handles singleton faces and arbitrary finite nonfaces, rather than merely pairwise confusability.

### Identity `eq:ca:symdiff` — pass

Location: lines 50–61.

The direction from symmetric-difference size to union size is immediate. For the reverse direction, downward closure supplies (\tau\setminus\sigma\in K), and

\[
\sigma\mathbin\triangle(\tau\setminus\sigma)=\sigma\cup\tau.
\]

This proves equality of the suprema even when they are infinite. A finite bound that fails is witnessed by an actual pair of finite faces; no attainment of an infinite supremum is assumed.

### Theorem `thm:ca:widths` — pass

Location: lines 64–82.

**Eventual width:** if a face has (k+1) vertices, its one complete shared presentation must eventually include all those names in each output, since the maximum of their finitely many success times is finite. Conversely, every complete presentation eventually contains an edge incident with (C). Its other endpoint's block face is the exact finite candidate set, which includes the true target and has size at most (r(K)). Keeping that list proves the stronger whole-list stabilization assertion.

**Distinct-edge threshold width:** an edge between blocks (B_\sigma,B_\tau) has candidate set (\sigma\triangle\tau), giving the upper bound after one edge. For the lower bound, choose such a finite candidate set (D) with (|D|>k). It is nonempty, so the two blocks are distinct. Their infinitude supplies as many distinct common crossing edges as any finite maximum of the thresholds (d_v), (v\in D), requires. That *one finite history* forces all those targets into the same output list. Every such history extends separately to a full presentation for each target, using a negative singleton-block point. No common full presentation for (D) is required, and the proof does not conflate the two lower bounds.

**Other conclusions:** the least-consistent-target learner succeeds on full positive texts because only finitely many targets precede the true one in the enumeration and each preceding false target has an explicit positive witness against it. This conclusion is not justified for arbitrary partial positive streams; the chapter correctly says full texts. Fresh generation uses the known infinite common core and works even after excluding earlier generator outputs.

All learners here are deterministic functions of finite histories. No randomized list-learning claim is proved or needed.

### Corollary `cor:ca:two` — pass

Location: lines 84–89.

Take (V=A\cup B) for the two facets in the proof. Then (r(K)=r) and (b(K)=|A\cup B|=b), including (A=B). Replacing finitely many infinite blocks by distinct residue classes preserves every block-membership calculation. Each support is a finite union of residue classes, so the unary-regular-language claim follows. The case (r=b=1) is valid, with one proper infinite support and widths one.

### Theorem `thm:ca:coloring` — pass

Location: lines 91–101.

For a subclass indexed by (W\subseteq V), the first-core-edge learner can output (\sigma\cap W). Downward closure makes this a face contained in (W). Thus the subclass admits an eventual (j)-list learner exactly when it contains no ((j+1))-face. This gives precisely the independent sets of the stated hypergraph. A color partition yields a cover; from any finite or countable cover, assigning the least covering index yields a coloring. Since countably many singleton subclasses suffice, no larger cardinal is relevant. Empty subclasses can use the constantly empty list and can be discarded from a cover.

The complete-graph examples are correct: rank two limits the eventual list width to two, while every one-identifiable subclass has at most one vertex. Finite graphs give arbitrarily large finite cover size and the countable complete graph gives countably infinite cover size.

### Independent finite counterexample search — passed

In addition to the proofs, I enumerated every simplicial complex containing all vertices on vertex sets of sizes one through four: respectively 1, 2, 9, and 114 complexes. For each, a finite membership-profile calculation checked that common crossing edges cover all positive block profiles exactly for faces, that the two-face union and symmetric-difference maxima agree, and that the subclass bound is equivalent to avoiding a monochromatic ((j+1))-face. There were 9,310 joint-realization/subclass checks, all passing. This is a finite sanity check, not a substitute for the countable proofs.

## Chapter 5: sparse holes and randomization

### Thinness and target geometry — pass

Location: lines 8–15.

For every (q), all but finitely many consecutive gaps are at least (q). Any interval therefore contains at most the fixed exceptional count plus (n/q+1) points. Taking the supremum over intervals, then the large-(n) limit, and finally letting (q\to\infty), gives upper Banach density zero. The complement has lower Banach density one and is infinite. This is stronger than mere asymptotic density one.

### Theorem `sh:element-diagonal` — pass

Location: lines 19–63.

The crucial obligations are satisfied:

1. **Cutoff existence:** for every fixed finite history, a natural-valued measurable output has tail probability tending to zero. Thus the least cutoff (B_k\ge M_k+k) exists.
2. **No dependence on the realized algorithm tape:** (h_k,M_k,B_k) depend only on previous construction residues and the generator's probability law. They do not depend on the realized ω. Conditional on those residues, the chosen history is fixed and the quantile bound applies to the original algorithm-tape law.
3. **A fixed legitimate increasing text:** all newly declared holes lie above the current maximum observation. The nested histories cover precisely the eventual complement, since the cutoffs tend to infinity and later holes cannot change membership below an earlier cutoff. Their lengths strictly increase; thus infinitely many stage errors occur at distinct actual times.
4. **Thin infinite holes:** every interval ((M_k,B_k]) has length at least (k), so every residue choice contributes a nonempty finite hole block. Internal gaps equal (k); the gaps between blocks grow because (M_k=B_{k-1}+k). Every finite set of early blocks is finite, so the ordered holes' gaps tend to infinity.
5. **Escape control without round independence:** summability of (\Pr(E_k^c)\le2^{-k}) implies eventual (E_k) by the first Borel–Cantelli lemma, which needs no independence.
6. **Repeated residue hits:** condition on the entire algorithm tape and the past construction residues. The requested residue is then fixed, while the new independent (R_k) is uniform. Iterated conditioning gives exactly the displayed telescoping product for avoidance over any finite interval. It tends to zero, so the (Z_k) occur infinitely often. The actual error events are not assumed independent.
7. **A hit is an error:** on (E_k\cap Z_k), an output below or at (M_k) is either observed or an earlier hole, while an output above (M_k) is placed into the new hole block. Since (E_k) eventually holds, the infinitely many (Z_k) yield infinitely many errors.
8. **Measurability and fixed-target extraction:** finite residue prefixes range over a countable tree. The histories and cutoffs are measurable functions of these prefixes; the variable-history generator output is a countable piecewise combination of measurable maps. Events involving infinitely many stages are countable unions/intersections. Fubini/Tonelli therefore fixes a construction tape whose algorithm-tape section has probability one. The resulting target and its unique increasing enumeration are deterministic and selected before the algorithm tape is realized.

An arbitrary algorithm probability space causes no problem: conditional probabilities can be read as conditional expectations relative to the sigma-algebra generated by ω and the past residues. A regular conditional distribution on individual tape points is unnecessary. The proof is expressly for no-feedback generation; adding target-dependent feedback would require a new argument.

### Theorem `sh:vanishing-error` — pass

Location: lines 69–90.

The candidate set has size at least (t^2+1-t>0), so uniform sampling is defined and novelty holds for every tape. Asymptotic density zero of the complement makes the stated error-probability bound tend to zero. For any fixed input stream, independently supplied per-time random coordinates make the error indicators independent, even if the stream repeats observations. The variance bound and Chebyshev at square times give summable deviation probabilities. Countably many rational deviation tolerances yield convergence along squares almost surely; monotonicity of the nonnegative partial error counts extends it to all times because consecutive squares have ratio tending to one.

The stream need not be complete. It does need to be fixed for this independence proof, as the statement says. No simultaneous-over-all-streams event is claimed here. Applying the preceding diagonal to this one generator then gives both infinitely many errors and frequency zero on one fixed thin-complement target; their probability-one events may be intersected because only finitely many events are involved.

### Lemma `sh:inner` — pass

Location: lines 101–108.

The locking argument is valid for the stated full-presentation success requirement. If no finite positive history is safe under every finite positive extension, append the next enumeration point and then a finite extension witnessing an error, repeatedly. The enumeration insertions ensure completeness and increasing history lengths even if a witnessing bad extension can be empty. The resulting full presentation has infinitely many errors.

From a safe history, deterministic self-feeding stays inside the target and is fresh by induction, since each earlier output is immediately appended to the input history. Its output range is therefore infinite and lies in the target. There are only countably many finite histories; ranges from other histories may be inadmissible, but that does not matter. Retaining all infinite ranges gives a countable family with at least one inner subset for every target.

The argument allows repeated observations in general full presentations. It does not prove the same necessity under an increasing-presentation-only requirement, and the following theorem explicitly acknowledges that restriction. For an empty target class an empty family is a valid vacuous inner cover; for a nonempty class the construction necessarily retains at least one infinite range.

### Theorem `sh:envelope-separation` — pass

Location: lines 94–132.

**Deterministic impossibility:** for any countable proposed family of infinite inner sets, choose increasingly large witnesses, revisiting each set infinitely often. An infinite subset of the natural numbers is unbounded. Monotonicity and unboundedness of (a) therefore allow (a(d_m+1)\ge m) at every stage. If ([0,n)) contains (m) selected points, then (n\ge d_m+1), hence (a(n)\ge m). This is exactly the required envelope, including (n) before the first selected point. The selected holes meet every proposed inner set, so the complementary target contains none. Finite nonempty candidate families can be enumerated with repetition; an empty candidate family cannot cover the nonempty class, which contains (\mathbb N).

**Randomized upper bound:** sublinearity yields (a(2N)/N\to0), so one can successively choose the required disjoint intervals with increasing endpoints. Their sampled points are pairwise distinct. Every tail contains infinitely many points, and deleting a finite sample preserves infinitude and freshness for every history. For any fixed target the envelope bounds each sampled point's hole probability by (2^{-j}). The union bound gives exactly (1-2^{1-T}) for safety of the whole tail from index (T). On this same event, all output sets at times (t\ge T) are safe for *every* presentation, since the input can only remove points from the fixed safe tail. There is no uncountable intersection of presentation-specific probability-one events. Borel–Cantelli gives eventual safety almost surely.

The random sets are measurable coordinatewise on the countable universe. Their least elements are also measurable: the event that (n) is the least element is membership of (n) intersected with finitely many nonmembership events below (n). Thus the final element-valued conclusion follows within the original measurable-map model. This does not require an explicit finite representation of an infinite output set.

The successful-tape event is uniform over presentations for a *fixed* target and may depend on that target. It is not simultaneous over the entire target class. The known common envelope is also essential to this construction: its interval schedule uses (a), and the unrestricted sparse-hole diagonal does not promise compliance with that chosen envelope.

## Small expository clarifications; none changes a theorem

1. Declare once that (\mathbb N=\{0,1,2,\ldots\}). Both the metric row example and sparse-hole formulas use zero.
2. State explicitly that the contrastive learners are deterministic, and that empty lists are permitted. The existing definition as a history-to-list rule already implies the former and “at most (k)” permits the latter.
3. In the contrastive full-positive-text learner, specify an arbitrary fallback or the empty list when no target is consistent. This only completes its definition on unrealizable histories. For an empty subclass, use the constantly empty list.
4. In the sharp-factor-two construction, explicitly write (V=A\cup B). This is already the intended vertex set.
5. For maximum proof readability, expand the sparse-hole variance paragraph by displaying the centered sum, its square-time deviation bound, and the monotone interpolation inequalities. The present argument is complete at standard research-paper detail, but these two lines would make the probability proof easier to verify.
6. In the inner-cover proof, say that “finite extension” includes the empty extension and give the order “append the next enumeration point, then append an error-witnessing extension.” This makes the increasing-time point explicit.
7. Retain all model qualifiers when shortening prose: ambient centers; unbounded metric targets; countable class; full versus partial positive texts; distinct-edge finite-prefix guarantees; fixed input stream in the frequency theorem; every full presentation in the deterministic separation; known envelope; and target-dependent almost-sure events.

## Source fingerprints

SHA-256 of the files audited:

- `03_metric.tex`: `a10f1a162c5f4405fe43643276c3320a7e6d1d67fc8db16c0bb2281b5e2c0174`
- `04_contrastive.tex`: `4b4a385b2f6362b060685a944d1fabc7c7f198ce177354221de89b2919489ede`
- `05_sparse_holes.tex`: `36fa84f64ecc27ba90a57dd53c6386177fd50c5d3d9157fa2f23ab92ad17bf6d`

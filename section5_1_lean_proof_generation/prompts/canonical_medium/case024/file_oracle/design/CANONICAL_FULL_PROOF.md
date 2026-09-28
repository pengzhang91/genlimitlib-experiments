# Case_024 — canonical proof

## 1. A common stream fixed in advance

Take \(U=\mathbb Z_{>0}\) with its natural order, and define
\[
E=\{2^j:j\ge0\},\qquad K_0=E,\qquad K_1=U.
\tag{1}
\]
Both languages are infinite, and the inclusion is strict. The complement \(U\setminus E\) is also infinite; for example, \(2^j+1\) is not a power of two for every \(j\ge1\).

At a time \(t\in\{1,2,4,8,\ldots\}\), present the smallest element of \(U\setminus E\) not previously presented. At every other time, present the smallest element of \(E\) not previously presented. Neither choice refers to the generator, its outputs, or its random seed. Both choices exist at every finite time because the selected set is infinite and only finitely many values have been presented. This defines one fixed, oblivious sequence \(x\), common to every generator under consideration.

The two branches select from disjoint sets, and each avoids earlier input values. Hence the stream is injective. Each branch is used infinitely often: there are infinitely many powers-of-two times, and there are infinitely many other times. Within either branch, the least not-previously-presented rule visits the branch's elements in their natural order. Thus every member of each branch is eventually presented, and
\[
R(x)=U.
\tag{2}
\]
In particular, the stream covers both targets completely. It is important that previous *outputs* do not cause a value to be skipped in this coverage argument.

Among the first \(t\ge1\) inputs there are exactly
\[
a(t)=1+\lfloor\log_2 t\rfloor
\]
values outside \(E\). Thus
\[
\frac{|S_t\setminus K_0|}{t}=
\frac{1+\lfloor\log_2 t\rfloor}{t}\longrightarrow0,
\qquad
\frac{|S_t\setminus K_1|}{t}=0.
\tag{3}
\]
For completeness, if \(m=\lfloor\log_2 t\rfloor\), the first ratio is at most \((m+1)/2^m\), which tends to zero; successive values of this last sequence have ratio at most \(3/4\) once \(m\ge1\). This verifies the vanishing distinct-value rate, not a bound on the total number of contaminants. It is the injective instance of the noise-rate convention in P17 Definitions 6–7, PDF page 20.

## 2. A pathwise upper-density obstruction

Fix any randomized generator satisfying the candidate's premise for both targets. Couple its two target interpretations by using the same internal random choices \(\omega\). The known family, input stream, and any target-independent family-oracle answers are the same. By induction on rounds, its internal states and output values are therefore the same. This argument would not hold with target-membership feedback, which is not part of the model.

Let \(W(\omega)\) be the distinct set of all output values, and let \(D(\omega)\) be the values first announced by the generator. Almost-sure eventual validity for \(K_0=E\) supplies an event \(\Omega_0\) of probability one such that, for every \(\omega\in\Omega_0\), only finitely many outputs are outside \(E\). Consequently
\[
b(\omega):=|W(\omega)\setminus E|<\infty
\quad(\omega\in\Omega_0).
\tag{4}
\]
No expectation of \(b(\omega)\), or of the last invalid round, is assumed to be finite.

For every \(n\ge1\), exactly \(1+\lfloor\log_2 n\rfloor\) powers of two lie in \(\{1,\ldots,n\}\). Since \(D\subseteq W\), (4) gives, for each fixed \(\omega\in\Omega_0\),
\[
0\le\frac{|D(\omega)\cap K_1[n]|}{n}
\le\frac{1+\lfloor\log_2 n\rfloor+b(\omega)}{n}
\longrightarrow0.
\tag{5}
\]
Thus
\[
\overline d_{K_1}(D(\omega))=0
\quad\text{almost surely}.
\tag{6}
\]
For every \(\omega\), the other target density satisfies
\[
0\le\overline d_{K_0}(D(\omega))\le1,
\tag{7}
\]
simply because its numerator counts a subset of an \(n\)-element target prefix. The argument actually proves zero upper density for the entire raw output set on \(K_1\), which is stronger than (6) for first announcements.

## 3. The stated expectation inequality

For each value \(z\), membership in \(D(\omega)\) is a measurable event described by its first output time and its fixed first input time. A prefix count is a finite sum of such indicators; its upper limit is measurable and lies in \([0,1]\). Both expected densities are therefore well defined.

Take expectations of (6) and (7). Because (6) was proved after taking the limit separately on each trajectory in a probability-one event, this step exchanges neither an expectation and a limit nor an expectation and a supremum. We obtain
\[
\mathbb E[\overline d_{K_1}(D)]=0,
\qquad
\mathbb E[\overline d_{K_0}(D)]\le1,
\]
and hence exactly
\[
\mathbb E[\overline d_{K_0}(D)]
+\mathbb E[\overline d_{K_1}(D)]\le1.
\tag{8}
\]
In particular, both expectations cannot be strictly greater than \(1/2\). In this construction the stronger assertion that their minimum is zero holds for every generator satisfying the premise.

## 4. The many-target objective

Enumerate \(U\setminus E\) increasingly as \(c_1,c_2,\ldots\). For each \(r\ge2\), take the following family of exactly \(r\) targets:
\[
K^{(r)}_0=E,\qquad
K^{(r)}_j=E\cup\{c_1,\ldots,c_j\}\ (1\le j\le r-2),
\qquad K^{(r)}_{r-1}=U.
\tag{9}
\]
For \(r=2\) the middle portion is empty. Every set is infinite; each middle step adds a new point, and the last step is strict because infinitely many complement points remain. Thus (9) is strictly nested.

The same stream from Section 1 covers every target by (2). A middle target contains \(E\), so its number of off-target values in any input prefix is at most the count for \(E\). Equation (3) therefore proves vanishing contamination for all \(r\) interpretations, on the same oblivious injective stream.

Any randomized generator valid almost surely for every target in (9) is in particular valid almost surely for \(E\). The argument in (4)–(6) again forces expected upper density zero on the final target \(U\). All densities are nonnegative, so its minimum expected upper density over this family is exactly zero.

This conclusion is not vacuous. A deterministic generator that at every round outputs the smallest power of two not already presented or output is always fresh and belongs to every target in (9), on every input stream. Such a power exists because the common core is infinite. Thus the feasible class of simultaneously valid generators is nonempty. The supremum over this class of the minimum expected upper density is zero for every finite \(r\ge2\). Requiring validity on every legal stream, and allowing minimization also over those streams, leaves the same value: the common stream proves the upper bound zero and nonnegativity plus the common-core generator proves the matching lower bound zero.

## 5. Source and quantifier check

The sparse-nested-language and sparse-time idea is present in P17 Theorem 6.21, PDF page 52. Here the recurrence explicitly skips only prior input values, establishing both obliviousness and coverage. The random-generator assertion is proved trajectory by trajectory, not imported from that deterministic source statement. P39 Section 2, PDF page 9, supplies the first-announcement metric; its randomized density in Definition 4.1, PDF page 21, places expectation inside a lower-limit expression and is not substituted for (8).

The fixed pair and stream precede the universal choice of generator. The random threshold may depend on the seed. The optional families use the same stream and already have zero minimax value. No bounded-displacement or unknown-target-feedback variant is asserted.

Overall proof status: COMPLETE

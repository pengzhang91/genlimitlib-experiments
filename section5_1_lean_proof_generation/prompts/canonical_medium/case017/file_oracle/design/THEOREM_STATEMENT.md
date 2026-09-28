# Case_017 — exact theorem and clause inventory

## Original target

Let \(\mathcal H=\{L_1,\ldots,L_m\}\) be a finite indexed family of infinite subsets of a countable universe equipped with a fixed order, with membership access to each \(L_j\). On an injective presentation with infinite range \(E\subseteq K\in\mathcal H\), define
\[
I(E)=\bigcap\{L\in\mathcal H:E\subseteq L\}.
\]
There is one deterministic online generator such that, whenever \(I(E)\) is infinite, it is eventually fresh and target-valid for every compatible target and its first-announced target set \(D\) satisfies
\[
\underline d_K(D)\ge \max\!\left\{\frac12\underline d_K(I(E)),\;\underline d_K(I(E)\setminus E)\right\}.
\]
No computable-runtime or sample-complexity claim is made; membership access and the finite representation are part of the model.

## Normalized quantifiers

Fix an enumeration order \(U=(u_1,u_2,\ldots)\), as used for the first-element density in P39, and a nonempty finite indexed family \(\mathcal H\) of infinite subsets of \(U\). There exists a deterministic generator \(G_{\mathcal H}\), chosen once for this family and not for a target or a presentation, with the following property.

For every injective sequence \(x=(x_t)_{t\ge1}\) whose range \(E\) is infinite and is contained in at least one family member, and for every \(K\in\mathcal H\) satisfying \(E\subseteq K\), if \(I(E)\) is infinite, there is a finite \(T\) such that the output \(y_t\) of \(G_{\mathcal H}\) satisfies
\[
y_t\in K\setminus\bigl(\{x_1,\ldots,x_t\}\cup\{y_1,\ldots,y_{t-1}\}\bigr)
\quad(t>T).
\]
Writing \(\tau_x(z),\tau_y(z)\) for first presentation and output times, respectively, and taking a missing time to be infinity, put
\[
D_K=\{z\in K:\tau_y(z)<\tau_x(z)\},\qquad
\underline d_K(S)=\liminf_{n\to\infty}\frac{|S\cap K[n]|}{n},
\]
where \(K[n]\) is the first \(n\) members of \(K\) in the common order. Then
\[
\underline d_K(D_K)\ge
\max\left\{\tfrac12\underline d_K(I(E)),
\underline d_K(I(E)\setminus E)\right\}.
\]
The same output trajectory works for all compatible targets. The displayed infinitude hypothesis is retained, although \(E\subseteq I(E)\) makes it automatic here. There is no completeness requirement \(E=K\).

## Lean realization

The exact Lean target uses the existing library declarations
`GenLimit.Generic.InfinitePartialPresentation`,
`GenLimit.Generic.StreamIn`, `GenLimit.NovelGeneratesInLimit`,
`GenLimit.GeneratorFirst`, and
`GenLimit.PatientScope.relativeLowerDensity`. The finite-family information
core and the within-round online interface remain case-specific because the
library has no exact definitions with those signatures.

## Original clauses to be checked

C01 is the finite indexed family, infinite languages, common order, membership access, injective infinite partial presentation, and the definition of \(I(E)\). C02 is one generator for the whole family and eventual fresh validity for every compatible target. C03 is the half-core lower-density term. C04 is the never-presented-core lower-density term. C05 is the maximum of the two bounds and the stated absence of a computational complexity guarantee. These refine, without replacing, rows C01–C05 of the input ledger; input C06 records inherited proof steps rather than an additional theorem claim.

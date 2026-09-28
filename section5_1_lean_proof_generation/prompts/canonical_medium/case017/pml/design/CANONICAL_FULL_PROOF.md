# Case_017 — canonical proof

## 1. Definitions and a total generator

Identify the ordered universe with a fixed sequence \(u_1,u_2,\ldots\). For an infinite set \(J\), let \(J[r]\) denote its first \(r\) elements. Let
\[
S_t=\{x_1,\ldots,x_t\},\qquad Y_{t-1}=\{y_1,\ldots,y_{t-1}\}.
\]
An output is fresh when it is outside \(S_t\cup Y_{t-1}\). An input is announced before the output in the same round. Define \(D_K\) using first times as in the theorem statement. These are the first-announcement conventions of P39, Section 2, PDF page 9; the proof below does not assume full coverage of \(K\).

For each nonempty \(J\subseteq\{1,\ldots,m\}\), write
\[
Q_J=\bigcap_{j\in J}L_j.
\]
There are finitely many such intersections. Hence
\[
M=\max\bigl(\{0\}\cup\{|Q_J|:Q_J\text{ is finite},\ J\ne\varnothing\}\bigr)
\tag{1}
\]
is a well-defined finite integer. Choose this constant once for the fixed family. Its choice is independent of the target, the presented range, and the order of presentation. We do not claim to compute it from arbitrary membership black boxes.

At round \(t\), form
\[
V_t=\{j\in\{1,\ldots,m\}:S_t\subseteq L_j\},
\qquad C_t=\bigcap_{j\in V_t}L_j.
\tag{2}
\]
If \(t\le M\), output the least element of \(U\setminus(S_t\cup Y_{t-1})\). If \(t>M\) and \(V_t\ne\varnothing\), output the least element of
\[
C_t\setminus(S_t\cup Y_{t-1}).
\tag{3}
\]
For a finite input outside the specified model, use the same arbitrary fresh fallback whenever \(V_t\) is empty or the input is not injective. This makes the rule a total function on finite inputs; in the injective nonempty-version-space branch, (3) always exists by the next paragraph.

For an injective prefix, \(|S_t|=t\). Every language indexed by \(V_t\) contains \(S_t\), so \(|C_t|\ge t\). If \(t>M\), this intersection cannot be finite by (1). Thus (3) is nonempty even after removing the finitely many previous announcements. Computing \(V_t\) uses at most \(mt\) membership tests. Testing membership in its intersection uses a finite conjunction, and scanning the universe for the least available member terminates. The fallback also terminates because the universe is infinite. Thus the generator is total and online without adding an online infinitude test.

For any compatible target \(K\), its index belongs to \(V_t\) at every round. Consequently \(C_t\subseteq K\). All outputs after round \(M\) are target-valid, and every output, including a fallback, is fresh. This establishes validity simultaneously for all compatible targets.

## 2. Stabilization of the finite version space

Put
\[
V_\infty=\{j:E\subseteq L_j\},\qquad I=\bigcap_{j\in V_\infty}L_j.
\]
For each \(j\notin V_\infty\), choose a witness \(e_j\in E\setminus L_j\). Since \(E\) is the range of the presentation, this witness occurs at a finite round. There are only finitely many excluded indices, so the maximum of these witness times is finite. An index in \(V_\infty\) is never excluded; every other index is excluded by that maximum time and cannot return. It follows that
\[
V_t=V_\infty,\qquad C_t=I
\tag{4}
\]
for all sufficiently large \(t\).

Every compatible language contains \(E\), so \(E\subseteq I\), and \(I\) is infinite. Fix a finite \(T\ge M\) after which (4) holds. At each round \(t>T\), the generator outputs the least not-yet-announced element of the same infinite set \(I\). No assertion here is made that an early \(C_t\) contains future samples or is infinite before the rule (1) becomes applicable.

## 3. A finite-prefix counting inequality

Fix \(r\ge1\), and let \(P=I[r]\). At the end of round \(T\), at most \(2T\) elements of \(P\) have been announced by either party. Until all elements of \(P\) have been announced, each later round removes at least one previously unannounced element of \(P\): either the input removes its last such element, or at least one remains after the input and the least-available rule outputs a member of \(P\). Thus this finite prefix is completely announced after finitely many rounds, regardless of whether its points belong to \(E\).

Let \(c\) be the number of its elements already announced by round \(T\), and let \(a,d\) be the numbers first announced afterwards by the presenter and the generator, respectively. Then
\[
r=c+a+d,\qquad c\le2T.
\]
Whenever a presenter-first point in \(P\) arrives and does not finish the prefix, the output in that same round is a new point in \(P\). Different such rounds have different outputs. The only possible presenter-first point with no such same-round partner is the point that finishes the prefix. Therefore
\[
a\le d+1,
\qquad
|D_K\cap I[r]|\ge d\ge\frac{r-2T-1}{2}.
\tag{5}
\]
All these output points belong to \(K\), since \(I\subseteq K\). This argument counts first announcements, not sample occurrences or output multiplicities.

For any \(n\), put \(r_n=|I\cap K[n]|\). The common order and the inclusion \(I\subseteq K\) imply that \(I\cap K[n]=I[r_n]\). Applying (5), with the same harmless bound when \(r_n=0\), yields
\[
\frac{|D_K\cap K[n]|}{n}
\ge \frac12\frac{|I\cap K[n]|}{n}-\frac{2T+1}{2n}.
\tag{6}
\]
The final term tends to zero. Taking lower limits proves
\[
\underline d_K(D_K)\ge\tfrac12\underline d_K(I).
\tag{7}
\]
This is an all-prefix bound, not merely a statement along favorable presentation times.

## 4. Every never-presented core point is generated first

Take \(z\in I\setminus E\). It lies in some finite prefix \(I[r]\). Section 3 proves that every member of that prefix is eventually announced. The presenter never announces \(z\), so the first announcement of \(z\) must be an output. Since \(z\in I\subseteq K\),
\[
I\setminus E\subseteq D_K.
\tag{8}
\]
This also covers a point output during the early fallback period: such a point, if it belongs to \(I\setminus E\), was already first announced by the generator. From (8), for every \(n\),
\[
|D_K\cap K[n]|\ge|(I\setminus E)\cap K[n]|.
\]
Taking lower limits gives the second required bound.

## 5. Assembly and quantifiers

The family-dependent constant (1) and the rule (2)–(3) define one generator before the target and the presentation are chosen. The finite stabilization argument uses only the range of that presentation and the fixed family. Its output trajectory has no dependence on which compatible family member is declared to be the target. Thus Sections 1–4 apply to every such target on that same trajectory.

Combining (7) and (8) gives exactly
\[
\underline d_K(D_K)\ge
\max\left\{\tfrac12\underline d_K(I(E)),
\underline d_K(I(E)\setminus E)\right\}.
\]
The infinitude premise is retained and is automatic because the presented range is infinite. Arbitrary omissions remain allowed. The existence of the hard-coded finite constant is not a uniform method for computing it from a family oracle, and no runtime or sample-complexity bound is asserted. The finite-family reasoning is supplied in full rather than inferred from P39's different countable partial-enumeration theorem (PDF pages 19–21).

Overall proof status: COMPLETE

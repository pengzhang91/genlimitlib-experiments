# Case 025 — presentation-dependent half density

## Complete natural-language statement

The ordered universe is the natural numbers.  Let
\(\mathcal L=(L_i)_{i\in\mathbb N}\) be any indexed countable family of
infinite languages.  Repeated languages and repeated input observations are
allowed.

There is one deterministic semantic online generator \(G_{\mathcal L}\),
chosen from the whole indexed family but before the target index and input
presentation, with the following property.  For every \(i\) and every input
stream \(x=(x_t)_{t\ge0}\) such that

1. every element of \(L_i\) occurs somewhere in \(x\); and
2. only finitely many time indices \(t\) satisfy \(x_t\notin L_i\),

the trajectory \(y\) of the generator is eventually fresh and target-valid:
there is a presentation-dependent finite time \(T\) such that for all
\(t\ge T\),

\[
y_t\in L_i,\qquad
y_t\notin\{x_0,\ldots,x_t\},\qquad
y_t\notin\{y_0,\ldots,y_{t-1}\}.
\]

The presenter moves first in each round.  At round \(t\), the generator sees
\(x_0,\ldots,x_t\) and its own outputs \(y_0,\ldots,y_{t-1}\), but it receives
neither the unknown target index nor target-membership feedback.

Let

\[
D(x,y)=\{z:\text{the generator announces }z\text{ before the presenter}
\text{ has announced }z\text{ through the same round}\}.
\]

Thus a same-round presenter/generator tie belongs to the presenter, not the
generator.  For \(A,K\subseteq\mathbb N\), define ambient-prefix relative lower
density by

\[
\underline d_K(A)=
\liminf_{n\to\infty}
\frac{|A\cap K\cap\{0,\ldots,n-1\}|}
     {|K\cap\{0,\ldots,n-1\}|}.
\]

Then the same generator satisfies

\[
\underline d_{L_i}(D(x,y))\ge \frac12
\]

for every admissible target and presentation above.  The theorem makes no
uniform bound on \(T\), no computability or complexity claim, and no bound on
the number or last position of corrupt input occurrences.

The exact endpoint is
`stage3_result : Stage3Case025.MainClaim`, with `MainClaim` definitionally
equal to `PresentationDependentHalfDensity`.

## Lean correspondence and faithfulness

The Lean statement uses existing library vocabulary wherever the semantics
are exact:

- `GenLimit.Language` and `GenLimit.Generic.Stream ℕ` are the languages and
  streams;
- `GenLimit.Presents` is an exact positive presentation and allows repeats;
- `GenLimit.Generic.FinitelyManyViolations input (fun x => x ∈ K)` counts bad
  **time indices**, exactly matching finite occurrence noise;
- `GenLimit.NovelGeneratesInLimit` is eventual target validity, avoidance of
  the input through the current round, and non-repetition of outputs;
- `GenLimit.GeneratorFirst` implements the presenter-first tie convention;
- `GenLimit.PatientScope.relativeLowerDensity` uses ambient natural-number
  prefixes.  The numerator is explicitly intersected with the target.

Only `OnlineGenerator` and `Follows` remain local because the library's generic
generator sees the input strictly before the current round, whereas this
theorem lets the presenter move first and exposes the current input.  These
local definitions add no target identity or membership feedback.


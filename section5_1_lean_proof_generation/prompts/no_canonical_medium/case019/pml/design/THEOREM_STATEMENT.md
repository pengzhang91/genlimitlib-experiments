# Case 019 — half density and an adjacent finite-noise separation

## Complete question

Let a **language** be an infinite subset of a countable universe equipped with
a fixed enumeration order. A level-$q$ presentation of a language $K$ is an
injective infinite sequence $x=(x_t)_{t\ge 0}$ such that

\[
K\subseteq R(x):=\{x_t:t\ge 0\},
\qquad |R(x)\setminus K|\le q.
\]

Thus the presentation covers every target value and contains at most $q$
**distinct off-target values**.  This is not the occurrence-counted noise
model: injectivity is required and the bound is on the set of contaminating
values.

A deterministic semantic generator is a map from each finite ordered input
history to its next output. At round $t$, the presenter supplies $x_t$
before the generator outputs $y_t$. The generator may depend on the fixed
family under study, but it receives no target index, target-membership
feedback, future input, or stabilization oracle.

Write

\[
S_t=\{x_0,\ldots,x_t\},\qquad
Y_{t-1}=\{y_0,\ldots,y_{t-1}\}.
\]

An output is valid and novel at round $t$ when

\[
y_t\in K\setminus(S_t\cup Y_{t-1}).
\]

The presenter wins a same-round tie.  Accordingly, the set of target values
first announced by the generator is

\[
D_K=K\cap\{z:\exists t\,[y_t=z\text{ and }
          (\forall s\le t)\ x_s\ne z]\}.
\]

If $K[n]$ denotes the first $n$ elements of $K$ in the fixed universe
order, define its target-relative lower density by

\[
\underline d_K(D_K)
  =\liminf_{n\to\infty}\frac{|D_K\cap K[n]|}{n}.
\]

Prove both of the following assertions.

### 1. Countable-family half density

For every $q\in\mathbb N_0$ and every indexed countable family
$\mathcal L=(L_i)_{i\in\mathbb N}$ of infinite subsets of $\mathbb N$, there
is one deterministic semantic generator $G$ such that, for every target index
$i$ and every level-$q$ presentation of $L_i$, there is a presentation-
dependent time $T$ after which every output is valid and novel, and

\[
\underline d_{L_i}(D_{L_i})\ge \frac12.
\]

The order on $\mathbb N$ is its usual order. Finite nonempty families can
be represented by repeating indices.  No stabilization time uniform in the
target or presentation is required.

### 2. An uncountable adjacent-level separation

For every $q\in\mathbb N_0$, construct an uncountable extensional family
$\mathcal C_q\subseteq\mathcal P(\mathbb Z)$ of infinite languages such that:

1. one deterministic semantic generator works for every target in
   $\mathcal C_q$ and every level-$q$ presentation, eventually outputs valid and
   novel values, and satisfies
   $\underline d_K(D_K)\ge 1/4$; but
2. no deterministic semantic generator succeeds eventually at level $q+1$
   on the same family.  More precisely, for every generator there are a fixed
   $K\in\mathcal C_q$ and a level-$(q+1)$ presentation of $K$ on which the
   generator fails infinitely often to output a member of $K\setminus S_t$.

For this clause the fixed order on $\mathbb Z$ is

\[
0,-1,1,-2,2,-3,3,\ldots .
\]

The value $1/4$ is a proved witness constant, not an optimality claim.

## Quantifier summary

The countable clause has the order

\[
\forall q\ \forall (L_i)_i\ \exists G\ \forall i\ \forall x\
  \exists T\ \forall t\ge T.
\]

The separation clause has the order

\[
\forall q\ \exists \mathcal C_q\ \exists G_q\
  \forall K\in\mathcal C_q\ \forall x\ \exists T\ \forall t\ge T
\]

for the positive part, while its negative part is

\[
\forall G\ \exists K\in\mathcal C_q\ \exists x\ \forall T\ \exists t\ge T
\]

with $x$ a legal level-$(q+1)$ presentation. The target and presentation
may depend on the challenged generator, but they are fixed throughout the
resulting counterexample run.

## Correspondence with `Stage3Model.lean`

The Lean statement preserves these choices as follows.

- `GenLimit.Generic.LanguageFamily ℕ` is the indexed countable family, and
  `GenLimit.Generic.LanguageClass ℤ` is the extensional, potentially
  uncountable family.
- `GenLimit.Generic.InjectiveValueContaminatedPresentationAtMost` states
  exactly injectivity, full target coverage, and at most $q$ distinct range
  values outside the target.
- `GenLimit.Generic.Generator` is a deterministic function of a finite ordered
  input history. `outputAfterInput` evaluates it on the first $t+1$ inputs,
  implementing the current-input-first round convention.
- The natural-number clause uses the library predicates
  `GenLimit.NovelGeneratesInLimit`, `GenLimit.GeneratorFirst`, and
  `GenLimit.PatientScope.relativeLowerDensity` directly.
- The integer clause uses polymorphic analogues of novelty and first
  announcement because those two library declarations are specialized to
  natural numbers.  Its density pulls integer sets back along the explicit
  `balanced` rank map and then uses the same library relative-density
  definition.
- `¬family.Countable` is extensional uncountability.  The negative clause
  intentionally omits output-versus-output novelty and therefore refutes the
  weaker eventual guarantee required in the question.

No occurrence-counted P06 presentation, omission model, target-dependent
uniform threshold, computability claim, runtime bound, or optimality claim is
silently added.

# Canonical question: feedback-resistant density boundary

Let
\[
E=\{2^k:k\ge0\},\qquad O=\mathbb N\setminus E,\qquad
\mathcal U=\{E\cup A:A\subseteq O\}.
\]

Strategies are deterministic semantic set-theoretic functions over `Nat`. The
target is fixed before the realized interaction and is unknown to the
generator. At round \(t\):

1. the presenter supplies \(x_t\), using only the public transcript through
   round \(t-1\);
2. the generator sees \(x_0,\ldots,x_t\) and earlier answers, then makes zero
   or one membership query \(q_t\in\mathbb N\);
3. it receives the exact membership answer for the fixed target;
4. it emits one output \(y_t\).

The realized presentation must be clean, injective, and complete: every
presented value is in the target, no value repeats, and its range is exactly the
target.

For a value \(z\), let \(T_x(z)\) and \(T_y(z)\) be its first presentation and
output times, with infinity if absent. The distinct first-announced target set
is
\[
D_K(y,x)=\{z\in K:T_y(z)<T_x(z)\}.
\]
An output at round \(t\) is fresh when it is absent from
\(x_0,\ldots,x_t\); repeated outputs receive no additional credit.

If \(K[0:n]\) denotes the first \(n\) elements of \(K\) in increasing order,
define
\[
\overline d_K(D)=\limsup_{n\to\infty}
  \frac{|D\cap K[0:n]|}{n}.
\]

Prove both claims:

1. The extensional class \(\mathcal U\) is uncountable and is uniformly
   generatable without samples by one injective output sequence with a
   class-wide stabilization threshold.
2. Every deterministic generator that is eventually valid and fresh for every
   target in \(\mathcal U\) and every legal presentation admits a target
   \(K\in\mathcal U\) and a causal clean injective complete presentation for
   which
   \[
   \overline d_K(D_K(y,x))=0.
   \]

Queries may range over the whole universe. No randomized,
oblivious-presentation, computability, runtime, or sample-complexity extension
is asserted.

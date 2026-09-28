# Case_024 — exact theorem and clause inventory

## Original target

There exist nested infinite languages \(K_0\subset K_1\) and a single oblivious injective stream that covers each target and has vanishing distinct-value contamination under each interpretation such that every randomized fresh-element generator that is eventually valid almost surely for both satisfies
\[
\mathbb E[\overline d_{K_0}(D)]+\mathbb E[\overline d_{K_1}(D)]\le1.
\]
Consequently no such generator guarantees expected upper density greater than \(1/2\) on both targets. A stronger objective is a many-target construction driving the minimax value to zero.

## Normalized quantifiers and random variables

There exist an enumeration-ordered countable universe \(U\), infinite languages \(K_0\subsetneq K_1\subseteq U\), and one deterministic sequence \(x=(x_t)_{t\ge1}\), chosen before any generator or random seed, such that \(x\) is injective and, for \(i=0,1\),
\[
K_i\subseteq R(x),\qquad
\lim_{t\to\infty}\frac{|\{x_1,\ldots,x_t\}\setminus K_i|}{t}=0.
\]
For every randomized online generator with no access to the unknown target identity or target-membership feedback, if on this stream it is eventually fresh and target-valid with probability one under each target interpretation, then the inequality in the original target holds.

More precisely, let \(\omega\) contain the generator's internal randomness and let \(y_t(\omega)\) be its output after seeing \(x_t\). Define the common first-announced set
\[
D(\omega)=\{z:\tau_y(z,\omega)<\tau_x(z)\},
\quad
\overline d_K(D(\omega))=
\limsup_{n\to\infty}\frac{|D(\omega)\cap K[n]|}{n}.
\]
The premise for each \(i\) is that with probability one there is a finite, possibly seed-dependent \(T_i\) after which
\[
y_t(\omega)\in K_i\setminus(S_t\cup Y_{t-1}(\omega)).
\]
The expectations are outside the upper limits, exactly as in the candidate. No uniform almost-sure threshold and no integrability of a last-error time is assumed.

## Optional stronger objective, also proved

For each integer \(r\ge2\), there is a strictly nested family \(\mathcal K_r\) of exactly \(r\) infinite languages, with the same fixed stream legal for all of them, for which
\[
\sup_{G\in\mathfrak G_r}\ \min_{K\in\mathcal K_r}
\mathbb E[\overline d_K(D_G)]=0.
\]
Here \(\mathfrak G_r\) consists of the randomized generators eventually fresh and valid almost surely for all members on the common stream. This set of generators is nonempty. The result also holds when validity is required on every legal presentation and the adversary may choose a legal presentation as part of its minimization. Thus zero is obtained already at finite \(r\), not just in a limit as the number of targets grows.

## Clause inventory

C01 is strict nesting, infinitude, a common oblivious injective stream, coverage, and vanishing distinct-value contamination under both interpretations. C02 is the universal random-generator statement with expectation outside upper density. C03 is the strict-half impossibility consequence. C04 is the optional many-target zero-minimax objective. These match input ledger C01–C04; C05 records proof provenance rather than a new target claim.

## Lean correspondence

The shared Lean target keeps all of these quantifiers and uses existing library
vocabulary wherever its semantics are exact:

- `GenLimit.InfiniteContamination.VanishingNoiseEnumeration` is injectivity,
  full target coverage, and vanishing empirical contamination;
- `GenLimit.NovelGeneratesInLimit` is eventual target validity, avoidance of
  the input through the current round, and no repeated generator output;
- `GenLimit.GeneratorFirst` is the common first-announced set with the
  presenter winning same-round ties;
- `GenLimit.PatientScope.prefixCount` counts members in ambient natural-number
  prefixes.

The local `relativeUpperDensity` is retained because the library has no exact
ambient-prefix relative **upper**-density declaration.  The local generator
interface is also retained because it receives the current input as required
here, while the library's generic generator receives only the earlier input
prefix.  Neither local definition introduces target identity or membership
feedback.

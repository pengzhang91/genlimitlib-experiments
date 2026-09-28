# Feedback-resistant density boundary

## Theorem normalization

Write
\[
E=\{2^k:k\in\mathbb N\},\qquad O=\mathbb N\setminus E,
\qquad \mathcal U=\{E\cup A:A\subseteq O\}.
\]
Here \(0\in O\). Distinct subsets of \(O\) give distinct members of
\(\mathcal U\), and \(O\) is countably infinite, so Cantor's diagonal
argument shows that \(\mathcal U\) is uncountable.

There are two claims. The positive claim asks for one autonomous injective
output sequence and one class-wide stabilization threshold. The negative
claim has the quantifier form
\[
\forall G\,[G\text{ is deterministic and universally eventually valid and
fresh}]\ \exists K\in\mathcal U\ \exists\pi
\quad \overline d_K(D_K(G,\pi))=0,
\]
where \(\pi\) is causal and its realized stream is clean, injective, and
complete. A round consists, in order, of presentation, an optional query and
its truthful answer, and one output. The score counts a target point only when
its first output strictly precedes its first presentation.

## Definitions

Fix an arbitrary deterministic generator \(G\) obeying the round interface;
for the construction it need not yet be assumed successful. A prior public
transcript is a finite sequence
\[
H_t=((x_s,q_s,b_s,y_s))_{s<t},
\]
where \(q_s=\bot\) means that no query and no answer occurred. Determinism
means that \(G\)'s optional query is a function of \((H_t,x_t)\), and, after a
query, its output is a function of \((H_t,x_t,q_t,b_t)\) (with the evident
no-query version).

The recursive state immediately before round \(t\) is
\[
S_t=(H_t,I_t,R_t,P_t).
\]
The finite sets \(I_t,R_t\subseteq O\) are, respectively, admitted ordinary
points and permanently rejected ordinary points; \(P_t=\{x_s:s<t\}\) is the
set of points already presented. Membership in \(E\) is permanently positive
and need not be stored. The update order below is part of the definition.

## Recursive construction

Start with \(H_0\) empty and \(I_0=R_0=P_0=\varnothing\). Suppose \(S_t\) has
been defined.

1. **Choose the presentation before the current query.** If \(t=2r\), set
   \(x_t=2^r\) and \(I_t^-=I_t\). If \(t=2r+1\), let
   \[
   a_r=\min\bigl(O\setminus(I_t\cup R_t)\bigr),
   \]
   set \(x_t=a_r\), and set \(I_t^-=I_t\cup\{a_r\}\). The minimum exists
   because \(I_t\cup R_t\) is finite and \(O\) is infinite. This admission is
   made before \(G\) sees the round's query answer.

2. **Generate and answer the optional query.** Apply \(G\)'s deterministic
   query rule to \((H_t,x_t)\). If it returns \(\bot\), put
   \(R_t^q=R_t\). If it returns \(q_t\in\mathbb N\), use the following
   exhaustive cases:
   \[
   b_t=1\quad\text{if }q_t\in E\cup I_t^-,
   \]
   \[
   b_t=0\quad\text{if }q_t\in R_t,
   \]
   and if \(q_t\in O\setminus(I_t^-\cup R_t)\), set
   \(R_t^q=R_t\cup\{q_t\}\) and answer \(b_t=0\). In the first two cases
   set \(R_t^q=R_t\).

3. **Generate the output and reserve an untouched output against later
   admission.** With the just-defined answer (or no answer), apply \(G\)'s
   deterministic output rule to obtain \(y_t\). Define
   \[
   R_{t+1}=\begin{cases}
   R_t^q\cup\{y_t\},&y_t\in O\setminus(I_t^-\cup R_t^q),\\
   R_t^q,&\text{otherwise},
   \end{cases}
   \]
   and put \(I_{t+1}=I_t^-\), \(P_{t+1}=P_t\cup\{x_t\}\). Append the
   round data to obtain \(H_{t+1}\).

Every state is finite, so these rules define a unique state at every natural
round. Define the limit sets
\[
I_\infty=\bigcup_t I_t,\qquad R_\infty=\bigcup_t R_t,
\qquad K=E\cup I_\infty.
\]
Then \(K\in\mathcal U\).

## Invariants and fixed-target replay

Induction on \(t\) gives the following invariants:

- \(I_t,R_t\) are finite subsets of \(O\), are disjoint, and grow
  monotonically.
- A membership decision is never reversed. Every positive query answer is at
  a point of \(E\cup I_{t+1}\); every negative query answer is at a point of
  \(R_{t+1}\).
- Every admitted ordinary point was unassigned immediately before admission.
  Every ordinary point newly rejected by a query or output was unassigned at
  that update.
- The state is reconstructible from the prior public transcript: admissions
  are the odd-round presentations, query rejections are recorded by their
  public zero answers, and output reservations are recorded by the public
  outputs. Thus the next presentation rule uses no current-round action.

The first and third invariants follow directly from the disjoint case splits.
They also imply \(I_\infty\cap R_\infty=\varnothing\). Consequently every
constructed query answer equals membership in the single set \(K\): a
positive answer lies in \(E\cup I_\infty=K\); a negative answer lies in
\(R_\infty\), hence outside \(K\). An ordinary point never touched at all is
also outside \(K\) by the definition of \(K\).

For full strategic legality, extend the on-path presentation rule to a total
causal presenter \(\pi\). On input a public history through round \(t-1\), if
that history is exactly \(H_t\), let \(\pi\) return the constructed \(x_t\).
Off that path, let it return the least member of the fixed infinite set \(K\)
not among the finitely many values previously presented in that history. This
is a function only of the prior public history (and the presenter's fixed
target), never of the current query or output.

We now prove replay explicitly. Run \(G\) and \(\pi\) against the truthful
membership oracle for the fixed target \(K\). At round zero the actual and
constructed histories are both empty. Assume through round \(t-1\) that every
actual presentation, query, answer, output, and state transition equals its
constructed counterpart, so the actual history is \(H_t\). The definition of
\(\pi\) gives the same \(x_t\). Determinism of \(G\) gives the same optional
query \(q_t\). The preceding membership argument gives the same answer
\(b_t=\mathbf 1_K(q_t)\), including the case in which an ordinary query was
newly placed in \(R_t^q\) during the defining recursion. Determinism then
gives the same \(y_t\), and the displayed update rules give the same next
state. This proves the induction step. Hence the entire recursively defined
transcript is exactly the truthful interaction with one target fixed in
advance of that realized interaction.

## Presentation legality

At even rounds the presenter lists \(1,2,4,\ldots\), each exactly once. At an
odd round it chooses an ordinary point outside \(I_t\cup R_t\), immediately
admits it, and presents it. Thus ordinary presentations are distinct, cannot
equal a power of two, and belong to \(I_\infty\). Every presented point is
therefore in \(K\), so the stream is clean and injective.

Conversely every point of \(E\) occurs at its designated even round. The only
ordinary points in \(K\) are members of \(I_\infty\), and each enters that
union only by being chosen and presented at an odd round. Hence the range of
the stream is exactly \(K\). The presenter is causal by its definition above.
The presentation is therefore globally legal: clean, injective, complete, and
chosen from transcript information available before each current query.

## Density lemmas

Use \([0,N]=\{0,1,\ldots,N\}\), and enumerate \(O\) increasingly as
\(o_0,o_1,\ldots\). For every \(j\ge0\),
\[
o_j\le 2j+1. \tag{1}
\]
Indeed, \([0,2j+1]\) has \(2j+2\) elements and at most \(j+1\) powers of
two. The latter assertion is immediate for \(j=0,1,2\); for \(j\ge3\), the
inequality \(2^j\ge2j+2\), proved by induction, shows that no more than the
first \(j+1\) powers can occur. Thus at least \(j+1\) points of the interval
are in \(O\), proving (1).

Consider the selection of \(a_r\) just before round \(2r+1\). Exactly \(r\)
ordinary points have previously been admitted. There have been \(2r+1\)
completed rounds, and each could have newly rejected at most one queried
ordinary point and at most one output ordinary point. This count includes all
reserved core-round overhead. Therefore
\[
|I_{2r+1}\cup R_{2r+1}|
 \le r+2(2r+1)=5r+2. \tag{2}
\]
Every ordinary point smaller than the least unassigned point \(a_r\) is
assigned. Its zero-based rank in \(O\) is consequently at most \(5r+2\).
Combining (1) and (2),
\[
a_r\le o_{5r+2}\le 10r+5. \tag{3}
\]
This is a stopping-time bound valid for every \(r\), regardless of how the
queries and outputs are placed.

Let \(I(N)=|I_\infty\cap[0,N]|\). For every \(N\ge5\), take
\(r=\lfloor(N-5)/10\rfloor\). For every \(i\le r\), (3) gives
\(a_i\le10i+5\le10r+5\le N\); these admitted points are distinct because
each is selected outside the current \(I_t\). Hence the all-prefix inequality
\[
I(N)\ge \left\lfloor\frac{N-5}{10}\right\rfloor+1
       \ge \frac{N-5}{10}. \tag{4}
\]
In particular,
\[
\liminf_{N\to\infty}\frac{|I_\infty\cap[0,N]|}{N+1}\ge\frac1{10}. \tag{5}
\]

Now let \(m_n\) be the largest element of the first \(n\) members of \(K\),
for \(n\ge1\). Since \(|K\cap[0,m_n]|=n\), (4) gives the following when
\(m_n\ge5\); when \(m_n<5\), its conclusion is immediate. Thus in all cases
\[
n\ge I(m_n)\ge\frac{m_n-5}{10},
\qquad m_n\le10n+5. \tag{6}
\]
For \(M\ge1\), the exact core-prefix count is
\[
|E\cap[0,M]|=1+\lfloor\log_2 M\rfloor. \tag{7}
\]
If \(k=\lfloor\log_2 M\rfloor\), the elementary inequality
\(k^2\le2^{k+1}\le2M\) gives
\(|E\cap[0,M]|\le1+\sqrt{2M}\). The same upper bound is immediate at
\(M=0\). For completeness, the first inequality is checked directly through
\(k=3\); thereafter \((k+1)^2\le2k^2\) propagates it by induction. Combining
the bound with (6), and using
\(10n+5\le15n\), gives the explicit target-prefix estimate
\[
\frac{|E\cap K[0:n]|}{n}
\le \frac{|E\cap[0,m_n]|}{n}
\le \frac1n+\sqrt{\frac{30}{n}}. \tag{8}
\]
For every \(\varepsilon>0\), the right side is at most \(\varepsilon\) once
\[
n\ge \max\left\{\frac2\varepsilon,
                 \frac{120}{\varepsilon^2}\right\}. \tag{9}
\]
Thus \(E\) has target-relative upper density zero in \(K\).

## Scored-set containment

Let \(z\in I_\infty\), and let \(t=2r+1\) be its unique admission and
presentation round. It cannot have been output at an earlier round. If it had
already been rejected, it could not be admitted; if it had been untouched,
the first such earlier output would have put it in \(R\); and it could not
already have been admitted without already having been presented. Any output
of \(z\) at round \(t\) occurs after its presentation. Therefore
\(T_y(z)\ge T_x(z)\). No ordinary member of \(K\) is scored.

Equivalently, an ordinary point output before presentation is either already
rejected or is rejected by that output, and so is outside \(K\). This covers
previously admitted, previously rejected, and previously undecided cases.
Consequently
\[
W=D_K(y,x)\subseteq E. \tag{10}
\]
Equations (8)--(10) imply
\[
0\le\limsup_{n\to\infty}\frac{|W\cap K[0:n]|}{n}
\le\limsup_{n\to\infty}\left(\frac1n+\sqrt{\frac{30}{n}}\right)=0.
\]

## Theorem assembly

For the positive clause, use the target-independent sample-free procedure
that outputs \(2^t\) at time \(t\). Its outputs are distinct and belong to
every \(E\cup A\), so it works from threshold zero, independently of the
target.

For the negative clause, begin with any deterministic generator satisfying
the premise for every member of \(\mathcal U\) and every legal presentation.
The construction above applies to every deterministic generator, so it
produces a single \(K\in\mathcal U\) and a causal adaptive clean injective
complete presentation of that \(K\). By the generator's premise its outputs
are eventually valid and fresh on this presentation; independently, the
first-announcement argument proves \(W\subseteq E\), and the finite-prefix
estimates prove \(\overline d_K(W)=0\). The target is fixed, every query is
answered truthfully for it, and no step uses the current query or output to
choose the current presentation.

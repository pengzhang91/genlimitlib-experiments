# Case_019 — canonical proof

## 1. Definitions

Fix \(q\ge0\). A legal presentation \(x\) is injective, covers its target \(K\), and has at most \(q\) distinct off-target values. This is precisely P12 Definition 5.1, PDF page 13. Put \(S_t=\{x_1,\ldots,x_t\}\). Outputs occur after the current input. All positive constructions avoid \(S_t\) and earlier outputs. For any target, \(D_K\) is the set of target values first announced by the generator, and \(K[n]\) is its first \(n\) elements in the fixed universe order.

## 2. The countable positive assertion

### A countable-family half-density lemma

Let \(\mathcal M=(M_i)_{i\ge1}\) be a fixed indexed family of infinite subsets of an enumeration-ordered universe \(U\). A finite nonempty family can be indexed this way by repeating its last member; an empty family gives a vacuous statement. There is a deterministic semantic online generator, always fresh, such that on every complete positive presentation of \(J=M_{i_*}\), even one with repetitions, its focus is eventually an infinite subset of \(J\), and its first-announced target set \(D_J\) satisfies
\[
|D_J\cap J[n]|\ge\frac{n-C-\lfloor\log_2 n\rfloor}{2}\quad(n\ge1)
\tag{HD}
\]
for some finite constant \(C\) depending on that presentation. Here is a stack construction and proof. It uses the nested-language and patient-waiting ideas in P39, Sections 3.1–3.2, but specifies its own state and charging rule.

**State and rule.** After a round the state is a finite stack
\[
C_0=U\supseteq C_1\supseteq\cdots\supseteq C_s,
\]
a next-push serial number \(h\ge1\), and an age \(a\ge0\). Stack depth is the largest family index processed in the current stack. Each node records the serial number of the push that created it. Initially the stack consists only of \(U\), \(h=1\), and \(a=0\). The top set is called the focus.

At the next round, receive the input \(z_t\), and let \(S_t\) be all input values seen so far. If \(z_t\) is outside the old focus, delete the suffix above the largest depth \(r\) for which \(z_t\in C_r\), and reset \(a=0\). The root ensures that such a depth exists. Do not push on a deletion round.

If no deletion occurred and \(a\ge2^h\), push a node at depth \(j=s+1\), with
\[
C_j=\begin{cases}
M_j,& S_t\subseteq M_j\text{ and }M_j\subseteq C_s,\\
C_s,&\text{otherwise}.
\end{cases}
\]
Label this new edge with serial \(h\), increment \(h\) by one, and reset \(a=0\). There is at most one push per round. Finally output the least element of the current focus not in \(S_t\) or the previous output set, and increment \(a\) by one.

At the end of every round, every stored set is infinite, is either \(U\) or a family member, and contains all inputs observed through that round. These assertions follow by induction: a deletion retains exactly a consistent prefix of a nested stack, and a push either retains the parent set or selects an infinite, consistent subset. The least available element therefore exists. The rule is total on every finite history, uses no future input and no information about the unknown target, and never repeats an output. Its set-inclusion tests concern the fixed known family; the lemma is semantic, not a claim that arbitrary inclusions can be decided by finitely many membership queries.

Before the push with serial \(h\), the generator has made at least \(2^h\) consecutive outputs with the same stack and parent focus. The last \(2^h\) of these outputs will be its charging block. Age is reset after every push or deletion, including a push that leaves the focus set unchanged. Thus this waiting assertion also holds for repeated or rebuilt stack depths.

**Eventual valid focus.** Completeness implies that every \(M_j\), \(j\le i_*\), that fails to contain \(J\) is excluded by an actual sample after finite time. Choose a time \(T_0\) after all these finitely many witnesses have appeared. Any node at depth at most \(i_*\) surviving at a time after \(T_0\) is \(U\) or a consistent \(M_j\) with \(j\le i_*\), so its set contains \(J\).

If a node at depth \(i_*\) exists at such a time, its parent set contains \(J\). That stored parent has not changed since the node was created. The target was consistent at creation, and \(J\) was a subset of that same parent; hence the rule made \(C_{i_*}=J\). All deeper focuses are subsets of \(J\).

If the stack is shallower than \(i_*\) after \(T_0\), its focus contains \(J\), so inputs cannot delete it. Each waiting time is a finite integer. Successive pushes therefore reach depth \(i_*\) in finite time. All intermediate focuses contain \(J\), by the same reasoning. Once that depth is reached, it can never be deleted, because every subsequent input is in \(J\). Consequently there is a finite \(T\ge1\) such that every focus and output at rounds \(t\ge T\) is valid. Repetition of a previous input cannot delete any consistent node; arbitrary repeated-input rounds are covered by this argument.

**Ordinary presenter-first points.** Completeness partitions \(J\) into the first-announced sets \(A_J\) of the presenter and \(D_J\) of the generator. Assign each point of \(A_J\) its unique first presentation time. Consider such a first-occurrence round \(t>T\), with \(z_t\in A_J\). If it belongs to the preceding focus, it was still unannounced when the previous output was chosen. The preceding output is therefore smaller than \(z_t\); equality is impossible because \(z_t\) is presenter-first. That output is a fresh member of \(J\). Distinct such rounds have distinct preceding outputs. Thus every such ordinary point in \(J[n]\) has a distinct partner in \(D_J\cap J[n]\).

**Deletion points and their charging blocks.** Otherwise \(z_t\) deletes a nonempty stack suffix. Let \(r\) be the retained top depth, and assign this point to the edge at depth \(r+1\), the first edge deleted. If its serial is \(h\), the fixed parent set \(C_r\) contains \(z_t\). In the charging block preceding that edge's creation, \(z_t\) belonged to the parent focus and was still unannounced. Every one of the \(2^h\) least-available outputs in that block is consequently smaller than \(z_t\).

An edge, once deleted, never returns; rebuilding its depth creates a new serial. Thus different deletion points are assigned to different serials. Let \(p\) be the number of pushes completed by round \(T\), and put \(H=p+1\). If \(h>H\), the preceding global push already occurred after \(T\). The block for serial \(h\) starts no earlier than that preceding push, since age is reset at every stack change. All its outputs are therefore distinct members of \(J\). If \(z_t\in J[n]\), this forces \(2^h\le n\), and hence \(h\le\lfloor\log_2 n\rfloor\). There are at most that many possible serials. Serials at most \(H\), including any block crossing the validity threshold, account for at most \(H\) additional deletion points. No disjointness assertion about charging blocks is needed: distinct assigned serials and the individual exponential bound already give this count.

There are at most \(T\) presenter-first points from the initial rounds. The partner argument and deletion bound yield
\[
|A_J\cap J[n]|\le |D_J\cap J[n]|+T+H+\lfloor\log_2 n\rfloor.
\]
Since \(A_J\) and \(D_J\) partition \(J\), this proves (HD) with \(C=T+H\). Dividing by \(n\) and taking the lower limit gives \(\underline d_J(D_J)\ge1/2\). Every part of the proof counts first announcements; a repeated input supplies no new presenter-first point and does not invalidate any count.


Apply the lemma to a countable finite-addition expansion of the given family:
\[
\mathcal L^+=\{L_i\cup F:i\ge1,\ F\subseteq U\text{ finite}\}.
\tag{1}
\]
Finite subsets of an enumeration-ordered countable universe are countable: a finite subset of ranks is encoded by the sum of the corresponding distinct powers of two. Pairs of that code with a family index are countable. Every language in (1) is infinite. Thus (1) has an indexing to which the lemma applies. A membership predicate for an individual language in this expansion is the original predicate combined with a finite-set test; the semantic inclusion tests used in the lemma remain explicitly semantic.

For the actual presentation let \(R=R(x)\) and \(F=R\setminus K\). Full coverage gives \(R=K\cup F\), with \(c=|F|\le q\). Thus \(R\in\mathcal L^+\), and the very same input is a complete positive presentation of \(R\). The lemma eventually outputs in \(R\). Its outputs are pairwise distinct, so at most \(c\) of them can lie in \(R\setminus K\). It therefore eventually outputs valid fresh members of \(K\).

For clarity, the density transfer can be checked at every target prefix. If the last point of \(K[n]\) has universe rank \(m_n\), let
\[
b_n=|R\cap U[m_n]|=n+e_n,\qquad 0\le e_n\le c.
\]
Then \(R\cap U[m_n]=R[b_n]\). Removing its at most \(c\) off-target points from (HD) gives
\[
|D_K\cap K[n]|\ge
\frac{n-C-\lfloor\log_2(n+c)\rfloor}{2}-c.
\tag{2}
\]
Divide by \(n\) and take the lower limit. This proves the countable half-density clause. The rule need not know \(q\), although only the requested fixed-\(q\) conclusion is needed. There is no uniform stabilization claim.

## 3. The uncountable witness

Use the marker-and-tail family appearing in P12 Theorem 5.7, PDF page 14. Define
\[
B=\{0,\ldots,q\},\qquad P_j=\{j,j+1,\ldots\},
\]
\[
\mathcal A_q=\bigcup_{j\ge0}\{B\cup A\cup P_j:A\subseteq\mathbb Z\},
\qquad
\mathcal B_q=\{A\cup\mathbb Z_{<0}:A\subseteq\mathbb Z\setminus B\},
\]
\[
\mathcal C_q=\mathcal A_q\cup\mathcal B_q.
\tag{3}
\]
Every member is infinite. Every \(\mathcal A_q\) member contains every marker, whereas every \(\mathcal B_q\) member contains none; the two alternatives are disjoint. The map
\[
S\subseteq\mathbb Z_{<0}\ \longmapsto\ B\cup P_{q+1}\cup S
\]
is injective into \(\mathcal A_q\). The power set of a countably infinite set is uncountable by the diagonal argument: from any proposed list of its subsets, the set disagreeing with the \(r\)-th listed subset on its \(r\)-th element is absent from the list. Therefore (3) is uncountable as an extensional class, not merely multiply indexed.

## 4. Quarter density at noise level \(q\)

Until \(B\subseteq S_t\), output the first still-unannounced member of \(-1,-2,-3,\ldots\). Once \(B\subseteq S_t\), output the first still-unannounced member of \(0,1,2,\ldots\) forever. Here “unannounced” excludes both all observed samples and all previous outputs. Each chosen half-line is infinite, so the rule is total and fresh.

If \(K\in\mathcal B_q\), presenting all \(q+1\) markers would require \(q+1\) distinct contaminants. At noise level \(q\) this is impossible. The rule stays on the negative half-line, all of which is in \(K\), and is always valid.

If \(K\in\mathcal A_q\), completeness gives a finite time at which all markers have appeared as inputs. From that time onward the rule uses the nonnegative half-line. Some \(P_j\) is contained in \(K\), so only finitely many points on that half-line can be invalid. Pairwise freshness limits their total number of outputs to a finite number. The initial negative-output period also contains only finitely many rounds. Hence validity is eventual in this alternative too.

It remains to prove the density assertion, which does not follow just from P12's extreme-value validity algorithm. Let \(H\) be the half-line used forever after some finite round \(T\), ordered by its restriction of the balanced universe order. Let \(Q\) denote all values first announced by our generator. For any prefix \(H[r]\), at most \(2T\) of its points have been announced by round \(T\). Afterwards, as long as the prefix is not cleared, the generator takes a point in it unless the current input just took its last remaining point. Every finite prefix is consequently cleared. Pairing each new presenter-first point with the output in its round, except possibly that last input, gives
\[
|Q\cap H[r]|\ge r/2-T-1/2.
\tag{4}
\]
This does not assume any order for the input stream.

There are only \(f=|H\setminus K|<\infty\) bad points on the eventual half-line. If the last point of \(K[n]\) has balanced universe rank \(m\), then \(n\le m\), and each half-line occupies at least \((m-1)/2\) places of the first \(m\) universe points. Its intersection with that universe prefix is a prefix of \(H\). Thus (4) implies
\[
|D_K\cap K[n]|
\ge \frac{m-1}{4}-T-\frac12-f
\ge \frac n4-(T+f+1).
\tag{5}
\]
Division by \(n\) proves the quarter-density guarantee for every target and every legal level-\(q\) presentation of the same class (3).

## 5. No semantic generator at level \(q+1\)

Assume, for contradiction, that a deterministic semantic generator \(G\) eventually outputs in \(K\setminus S_t\) on every level-\((q+1)\) presentation of every target in (3). We construct one complete injective presentation of a fixed final target on which it makes infinitely many off-target outputs. The construction below expands the obstruction behind P12 Lemma 5.4 and Theorem 5.7, rather than relying on an unverified projection application.

Start by presenting \(0,1,\ldots,q\). At stage \(r\ge1\), let \(\sigma\) be the finite input prefix already constructed. It contains exactly the previously scheduled negative integers \(-1,\ldots,-(r-1)\), the markers, and finitely many additional nonnegative integers. Maintain a finite set \(F_{r-1}\) of reserved nonnegative outputs, all outside \(\sigma\), which will never be presented.

Choose an integer \(M>q\) larger than every nonnegative value in \(\sigma\) and every reserved value. Define a temporary target
\[
L_r=\operatorname{range}(\sigma)\cup P_M\in\mathcal A_q.
\]
The infinite stream consisting of \(\sigma\) followed by \(M,M+1,M+2,\ldots\) is a clean injective complete presentation of \(L_r\). On this one hypothetical stream, the assumed guarantee for \(G\) supplies a finite round, after at least one new tail sample, at which its output \(b_r\) is valid and fresh relative to the samples. All prefix elements have already been presented, and the new tail is being presented in increasing order. Consequently
\[
b_r>\text{the largest tail value presented in that round}\ge M.
\tag{6}
\]
Choose the first extension round satisfying (6), and append exactly that finite tail block to the real stream. The finite round exists by the preceding argument. Since \(G\) depends only on the finite history and the fixed class, its real output at the chosen round is the same \(b_r\). Reserve that value, forming \(F_r=F_{r-1}\cup\{b_r\}\), and then append \(-r\) as the next real input. This finishes the stage.

Every stage is finite and appends at least one tail value and one new negative integer. The tail values in a new stage lie above all previous nonnegative samples and reservations. Inequality (6) also puts \(b_r\) outside the just-completed prefix and above all previous reservations. Thus induction proves injectivity of the entire stream, distinctness of the reservations, and permanent exclusion of every reservation from all inputs. Each new negative input is fresh because earlier negative inputs were exactly \(-1,\ldots,-(r-1)\).

Let \(R\) be the range of the resulting infinite input stream, and define once and for all
\[
K=R\setminus B.
\tag{7}
\]
Every negative integer is scheduled, so \(\mathbb Z_{<0}\subseteq K\). No marker belongs to \(K\), and every other point of \(K\) is a nonnegative nonmarker. Hence \(K\in\mathcal B_q\subseteq\mathcal C_q\). The stream covers all of \(K\) by (7), is injective, and has exactly the \(q+1\) distinct contaminants \(B\). It is therefore globally legal for the asserted noise level.

The temporary targets are used only to establish finite stopping times. They are not successively substituted for the real target. After (7) has been defined, replay the single constructed input stream with fixed target \(K\). At round one the input is the same. Inductively, equal finite input histories give the same output of the deterministic map \(G\); there are no target-dependent oracle answers to change that conclusion. Thus all reserved outputs occur in this one fixed-target replay. Every \(b_r\) was permanently excluded from \(R\), so \(b_r\notin K\). Their chosen rounds are strictly increasing. This gives infinitely many off-target outputs on a legal presentation, contradicting eventual validity.

The real next input at every round is determined from prior history, including completed stopping rounds, not from that round's as-yet-unseen output. Equivalently, for each fixed deterministic \(G\), the recursive construction defines an ordinary fixed infinite sequence whose replay already gives the contradiction. No computational or target-feedback assumption is needed.

## 6. Conclusion and source match

Sections 2 and 4 establish the two positive density clauses, and Section 5 refutes even eventual semantic validity at \(q+1\) for exactly the family used in Section 4. The finite-addition step is the no-omission specialization of P17 Theorem 6.18 (PDF pages 50–51), with the half-density fact proved above as well as stated in P39 Theorem 3.14 (PDF page 18). The source's original \(1/8\) finite-contamination lower-density corollary alone would not prove our \(1/2\) assertion.

P19 Theorem 2.16 (PDF page 7) concerns uniform or target-dependent-only thresholds, not the presentation-dependent threshold here. P06 occurrence-counted noise has not been substituted anywhere. The value \(1/4\) is only the established separation constant; its optimality is not claimed.

Overall proof status: COMPLETE

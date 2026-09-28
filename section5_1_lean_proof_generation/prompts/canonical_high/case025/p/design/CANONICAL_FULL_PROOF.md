# Canonical full proof: isolated presentation-dependent half density

This is the complete proof of the exact post-hoc target, reproduced verbatim from Sections 4–5 of the frozen Case_025 canonical proof.

## 4. A self-contained half-density engine with outputs on repeated rounds

The comparison with presentation-dependent stabilization must address actual repeated-input rounds, not just a deduplicated virtual sequence. We prove the following lemma and then apply it to a fixed countable expansion of the target family.

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


## 5. Finite occurrence noise and the density transfer

Let \(\mathcal L=(L_i)\) be any countable indexed family of infinite subsets of the fixed ordered universe \(U\). The empty-family assertion is vacuous. Form the fixed family
\[
\mathcal L^+=\{L_i\cup F:i\ge1,\ F\subseteq U\text{ finite}\}.
\tag{4}
\]
It is countable: finite subsets of \(U\) have finite sequences of integer ranks as codes, and pairs consisting of an index and such a code form a countable set. Every expanded language is infinite. A finite original family is handled by repeating its indices. No actual noise bound or target is needed to form (4).

Run the lemma's one generator for this expanded family on the actual input stream, making one fresh output at every round, including every repeated-input round. Fix any target \(K\in\mathcal L\) and any complete stream with finitely many off-target occurrences. If \(R\) is its range, completeness and finite occurrence noise give
\[
R=K\cup F,\qquad F=R\setminus K\text{ finite}.
\tag{5}
\]
The input is, by its definition of range, a complete positive presentation of the member \(R\in\mathcal L^+\), possibly with repetitions. The lemma therefore gives eventual outputs in \(R\) and the all-prefix bound (HD) for \(R\).

Only finitely many output rounds can have values in \(R\setminus K\): this set is finite, and the generator never repeats an output. There are also only finitely many output rounds before the lemma's validity time. Thus the actual generator is eventually target-valid on \(K\), with a presentation-dependent time, and is fresh at every round. This argument uses finiteness of the bad output set, not a supposed uniform bound on the last corruption time.

For the density calculation, put \(c=|R\setminus K|\). Let \(a_n\) be the last element of \(K[n]\), and let \(b_n\) be its rank in \(R\). Then
\[
b_n=n+e_n,\qquad 0\le e_n\le c,
\]
and \(R[b_n]\) differs from \(K[n]\) by at most \(c\) points. Let \(Q\) be all generator-first values in the actual interaction. Since \(D_R=Q\cap R\) and \(D_K=Q\cap K\), (HD) gives
\[
\begin{aligned}
|D_K\cap K[n]|
&\ge |D_R\cap R[b_n]|-c\\
&\ge \frac{b_n-C-\lfloor\log_2 b_n\rfloor}{2}-c\\
&\ge \frac{n-C-\lfloor\log_2(n+c)\rfloor}{2}-c.
\end{aligned}
\tag{6}
\]
Divide by \(n\) and take the lower limit. Both the fixed error terms and the logarithmic term vanish, so \(\underline d_K(D_K)\ge1/2\). Every output of the constructed generator was globally unannounced at its output time. Consequently \(W_G\cap K=D_K\), and its raw target output set has the same guarantee.

This is the finite-addition, no-omission instance of the transfer idea in P17 Theorem 6.18, PDF pages 50–51, with an explicit rank calculation. P17's older Corollary 6.20 supplies lower density \(1/8\), not the half density asserted here. The latter is proved by Section 4 and matches P39 Theorem 3.14, PDF page 18, on injective presentations. Section 4 additionally justifies repeated-input rounds directly. No deduplication step has left a round without a valid eventual output.

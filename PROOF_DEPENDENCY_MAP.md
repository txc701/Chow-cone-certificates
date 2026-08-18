# Dependency map for ARXIV_PROOF_DRAFT.md

Frozen mathematical source: `PROOF_CONJECTURE_3_30.md` at commit `e0e64a3`.
Draft numbering (left) with the frozen-proof counterpart (right).

## Dependency DAG

```
Cheng–Lin v3 definitions (U_J, a_J, N_J)      [external, definitional]
Cheng–Lin Lemma 3.29  (M_{J,J'})              [external, cited]
        |
        v
Lemma 1  (support: part 1 => a_J = 0)         [definitional]
Lemma 2  (reduction: div f = w, f >= 0        [symbolic]
          => identity (1) => Conj. 3.30)
        |
        v
Definition 3 (G, rho) + identity (W)          [definitional]
Definition 4 (selected moves, flow f,          [definitional]
          FL/FR coincidence convention)
        |
        +--> Lemma 5   (three G-ratios)        [symbolic]
        |       |
        |       v
        +--> Corollary 6 (outflow formula)     [symbolic; uses Def. 4 + L5]
        |
        +--> Lemma 7   (in-edge bijection,     [symbolic]
        |               inflow = #2-blocks * G)
        |
        v
Theorem 1 (divergence identity at support      [symbolic; uses (W), C6, L7,
           and non-support nodes; explicit      L1, L2]
           lambda; boundary d = 1)
```

## Table

| Unit (draft) | Frozen counterpart | What it establishes | Justification |
|---|---|---|---|
| §1 statement, (M$_{J,J'}$) | §1 | pinned definitions of $U_J,a_J,N_J$; Lemma 3.29; reading of "nonnegative linear combination" as linear-form identity (1) | definitional / external citation (Cheng–Lin v3) |
| §1 remark ($J=[d]$ term vanishes) | — (new in draft) | reading "all subsets" vs "proper subsets" is immaterial | definitional (via Lemma 1) |
| Lemma 1 (support) | §2 remark + §5 | $a_J=0$ if some $n_i=1$; support = no 1-part; subset criterion | definitional |
| §2 cover-edge dictionary | implicit in frozen §2/§3 | bijection $J\leftrightarrow c(J)$; split $(i,p)\leftrightarrow$ added element $j$; final-block offset bound $p\le n_r-2$; legality of $j=d$ | definitional (made explicit in draft) |
| Lemma 2 (reduction) | §2 | div-$w$ flow $\Rightarrow$ identity (1) $\Rightarrow$ Conjecture 3.30; sign/orientation audit | symbolic (coefficient comparison) |
| (W) | §3, eq. (W) | $w(c)=G(c)\sum\rho(n_i)$ | definitional |
| Definition 4 | §3 | selected moves, move-flows $G(\text{child})$, edge flow as move-sum, FL/FR coincidence at final 4 | definitional |
| Lemma 5 (ratios) | Lemma 1 (frozen) | $G$-ratios $\rho(m)$, $(m-2)(m-3)/2$, $m-3$; sum identity | symbolic (factorial algebra) |
| Corollary 6 (outflow) | inside frozen §5 | outflow$(c)=G(c)\sum_{n_i\ge4}\rho(n_i)$; edge-sum = move-sum | symbolic |
| Lemma 7 (in-edges) | Lemma 2 (frozen, incl. 2026-08-19 hardening) | constructive classification; completeness; well-definedness; injectivity; non-aliasing except final-(2,2); flow $=G(c)$; inflow $=\#2\text{-blocks}\cdot G(c)$ | symbolic (finite case analysis) |
| Theorem 1 / 1$'$ | §5 | div $f=w$ everywhere; explicit $\lambda$; $d=1$ boundary | symbolic (combines (W), C6, L7, L1, L2) |
| §8 cross-checks | §5 Remark + §9 (notes) | exact verification $d\le25$ etc.; staircase-uniqueness statement labelled conjectural | **computational — NOT load-bearing** |

## Computational-dependency audit

Every unit on the path
Cheng–Lin definitions → Lemma 1 → Lemma 2 → Definitions 3/4 → Lemma 5 →
Corollary 6 → Lemma 7 → Theorem 1
is justified definitionally or symbolically, uniformly in $d$. The only
computational items are in §8 (cross-checks), which nothing in §§1–7
references. **The theorem depends on no computation.** The empirical
staircase-uniqueness statement is quarantined in §8, labelled conjectural,
and used nowhere.

Frozen-proof material intentionally *omitted* from the draft (not needed
for Theorem 1): the converse direction of the flow/ideal equivalence,
max-flow/min-cut material, the staircase identities $\sigma(T_k)=0$ and
shell-decomposition corollaries (frozen §6). These remain available in the
repository for a longer paper but are not part of the referee draft's
dependency chain.

# Computational kill test — Cheng–Lin Conjecture 3.30

Pinned target: **Conjecture 3.30** of R. Cheng, W. Lin, *arXiv:2603.21680v3*
(local copy: `paper/cheng-lin-v3.pdf`). The conjecture asserts that the
inequality $\sum_{J\subseteq[d]} a_J N_J\le 0$ (Corollary 3.28) is a
nonnegative linear combination of the monotonicity inequalities
$N_J/U_J\le N_{J'}/U_{J'}$, $J\subseteq J'$ (Lemma 3.29), for every $d\ge1$.
The authors report computer verification for $d\le19$ (Remark 3.31).

Definitions of $U_J$, $a_J$, $w_J=U_Ja_J$ and the equivalent formulations
(nonnegative flow on Boolean cover edges with divergence $w$; nonnegativity of
$\sum_{\mathcal D}w$ over all downward-closed ideals) are stated and **proved**
in `RESEARCH_NOTES.md`. Current progress: `STATUS.md`.

## Layout

- `src/weights_bitmask.py`, `src/weights_recursive.py` — two independent
  exact-integer implementations of $J\mapsto(U_J,a_J,w_J)$.
- `src/support.py` — support reduction (all parts $\ge2$) and the reduced DAG.
- `src/dinic.py` — Dinic max-flow, arbitrary-precision integer capacities.
- `src/flows.py` — the two network constructions (full lattice / support DAG).
- `src/ideals.py` — brute-force ideal enumeration oracle ($d\le5$ only).
- `src/run_stage1_oracle.py` — reproduces `results/stage1_oracle_d1-5.json`.
- `tests/` — pytest suite; every claim above is asserted there.
- `results/` — machine-readable per-run outputs (JSON only, no binaries).

## Reproduce

```sh
python3 -m pip install pytest   # Python >= 3.10; stdlib only otherwise
python3 -m pytest tests/ -v     # Stage 1 validation suite
python3 src/run_stage1_oracle.py
```

Everything is exact integer arithmetic; a test statically rejects any floating
point in `src/`.

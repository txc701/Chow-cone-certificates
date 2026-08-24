# k=4 peel-width-three discovery checkpoint

Date: 2026-08-24

Branch base: `14527dc`

Scope: exact finite-dimensional discovery only; no Lean formalization and no
all-d theorem.

## Exact problem tested

For a fixed `d`, let `C_d` be the compositions
`c = (n_1,...,n_r)` of `d+2` with every `n_i >= 2`. Put

```text
v(n) = n(n-2),       V(c) = sum_i v(n_i),
Q2(c) = sum_i v(n_i)^2,
B_d = 720 times the fourth central moment of descents on S_(d+1),
S4(c) = 15 V(c)^2 - 6 Q2(c) - 12 V(c) - B_d,
U(c) = n_r (d+1)! / product_i n_i!,
G(c) = U(c) product_i (n_i-1),
w4(c) = G(c) S4(c).
```

`B_d` is recomputed from the exact Eulerian distribution, including the
exceptional small dimensions. The allowed directed covers split one block
`n_i = p+q`, with `p,q >= 2`, and satisfy
`min(p,q) <= 3`. The tested statement is the existence of `f(e) >= 0` with

```text
sum_(c -> x) f(c -> x) - sum_(x -> c) f(x -> c) = w4(c)
```

at every `c` in `C_d`. All saved flows are integers; all calculations use
Python arbitrary-precision integers or exact rational arithmetic.

Max-flow feasibility has exactly this finite meaning. A source supplies the
positive `w4` nodes, negative nodes drain to a sink, and allowed covers have
capacity one more than total supply. A max flow equal to total positive supply
is equivalent to the displayed divergence equations. It proves neither that
the solver's flow is canonical nor that a uniform formula exists.

## Reproducible certificates and verification

Run:

```bash
PYTHONPATH=src python3 src/run_k4_discovery.py \
  --output-dir results/k4_width3_discovery
```

The manifest hashes every generated artifact and the eight source modules
needed to reproduce it. It contains no timestamps or runtime-dependent data.
The primary certificate inventory is:

| d | nodes | allowed edges | positive primary edges | total supply |
|---:|---:|---:|---:|---:|
| 2 | 2 | 1 | 1 | 720 |
| 3 | 3 | 2 | 2 | 6000 |
| 4 | 5 | 5 | 4 | 21960 |
| 5 | 8 | 10 | 8 | 272160 |
| 6 | 13 | 19 | 12 | 2355360 |
| 7 | 21 | 36 | 20 | 17841600 |
| 8 | 34 | 66 | 33 | 250387200 |
| 9 | 55 | 120 | 61 | 2640052800 |
| 10 | 89 | 215 | 98 | 32039884800 |
| 11 | 144 | 382 | 162 | 495982206720 |
| 12 | 233 | 673 | 274 | 6479143070400 |
| 13 | 377 | 1178 | 427 | 106372650384000 |
| 14 | 610 | 2050 | 731 | 1835538921216000 |
| 15 | 987 | 3550 | 1206 | 29785501255910400 |
| 16 | 1597 | 6121 | 1916 | 594440267656435200 |

There are 71 saved certificates: one lexicographic primary certificate for
every `d=2,...,16`, plus eight deterministic exact minimum-cost certificates
at each of `d=4,6,8,10,12,14,16`. The standalone verifier deliberately imports
neither a flow solver nor the repository's support/weight implementation. It
independently enumerates the support, reconstructs `B_d`, `S4`, `U`, `G`, and
`w4`, checks every used cover and nonnegative flow, checks every node's exact
divergence, and checks total divergence. All 71 pass.

The focused checkpoint suite has 106 passing tests. The complete repository
suite has 277 passes and the branch's one pre-existing failure:
`tests/test_weights.py::test_no_floating_point_in_sources` rejects the exact
`Fraction` division already present in `src/k4_weights.py` at base `14527dc`.
This checkpoint does not alter that existing file or policy test.

The certificate schema is sparse: each edge row is
`[parent, block_index, left_part, positive_flow]`, and omitted allowed edges
mean zero. Unbounded flow values are canonical decimal strings. Exact range
files instead contain every allowed edge and its decimal-string minimum,
baseline, maximum, and classification. Feature files are canonical JSON Lines
with one row per allowed edge; rational values use reduced
`{"num": ..., "den": ...}` records. See
`results/k4_width3_discovery/features/schema.json` and the generation parameters
in `manifest.json` for the complete machine-readable schema.

## Certificate nonuniqueness

The secondary costs are total internal flow, width-three mass, first- and
final-block mass, balanced-split mass, right-peel mass, added-cut position, and
reflected position. Together with the primary certificate, the representative
dimensions contain the following observed diversity:

| d | saved certificates | distinct edge vectors | coordinates differing among them |
|---:|---:|---:|---:|
| 4 | 9 | 2 | 4 / 5 |
| 6 | 9 | 8 | 18 / 19 |
| 8 | 9 | 9 | 50 / 66 |
| 10 | 9 | 9 | 141 / 215 |
| 12 | 9 | 9 | 403 / 673 |
| 14 | 9 | 9 | 1160 / 2050 |
| 16 | 9 | 9 | 3055 / 6121 |

Three aggregate costs are exact invariants, not useful selectors. Flow across
each block-count cut is fixed by cumulative divergence, so total internal flow
is fixed. If `Phi(c)` is the sum of the proper prefix sums of `c`, splitting at
cut position `j` gives `Phi(child)-Phi(parent)=j`; hence
`sum_e j(e)f(e) = -sum_c Phi(c)w4(c)`. Added-cut position is therefore fixed,
and reflected position is fixed as its affine complement. The remaining local
objectives vary in the representative range (apart from small-dimensional
degeneracies). Equality seen only among saved certificates is never promoted
to an invariant.

For `d<=10`, exact residual-circulation optimization computes the global
minimum and maximum of every edge coordinate, independently of the baseline
certificate:

| d | fixed positive | fixed zero | positive but variable | optional |
|---:|---:|---:|---:|---:|
| 2 | 1 | 0 | 0 | 0 |
| 3 | 2 | 0 | 0 | 0 |
| 4 | 1 | 0 | 2 | 2 |
| 5 | 0 | 0 | 5 | 5 |
| 6 | 0 | 0 | 3 | 16 |
| 7 | 0 | 0 | 7 | 29 |
| 8 | 0 | 0 | 6 | 60 |
| 9 | 0 | 0 | 4 | 116 |
| 10 | 0 | 0 | 12 | 203 |

Thus, from `d=5` onward in this exact audit, no individual edge coordinate is
fixed. Full coordinate ranges stop at `d=10` because they require two auxiliary
exact max-flow problems per allowed edge; the higher-dimensional comparison is
explicitly sample-based.

## Normalized feature analysis

For every one of the 14,428 allowed edges through `d=16`, the feature tables
record the parent and child compositions, peel size and side, affected block
and position, all prefix sums, left/right size statistics `(L,R)`, variance
statistics `(VL,VR)`, square statistics `(QL,QR)`, `V`, `Q2`, the cross term,
`S4`, `G`, all saved flows available at that dimension, and
`h(e)=f(e)/G(child)` exactly.

Writing `R(e)=G(child)/G(parent)`, the normalized divergence equation is

```text
sum_out R(e) h(e) - sum_in h(e) = S4(c).
```

The ansatz search solves this equation directly; it does not regress against
an arbitrary certificate. Coefficients are shared across dimensions and split
only by the finite edge type `(peel size, side, final/nonfinal)`:

- P0: one constant per edge type.
- P1: a quadratic in `z = block_size - 2*peel_size`.
- P2: the P1 state enlarged by degree-four `z` terms and symmetric exterior
  statistics `N_ext`, `V_ext`, and `Q_ext` with the declared interactions.
- P3: an oriented bounded state using `L,R,VL,VR,QL,QR` and the 23 declared
  monomials.

The frozen split is training `d=3,...,11`, validation `d=12`, and untouched
holdouts `d=13,...,16`. No class produces a candidate: each exact training
system is inconsistent. The first inconsistent training prefix is `d<=4` for
P0, `d<=6` for P1, `d<=9` for P2, and `d<=10` for P3. Consequently no
coefficient vector is promoted, and validation/holdout success is not claimed.

There is also a solver-independent obstruction to any purely block-local
normalized rule in the eventual (`d>=3`) regime. The edges

```text
d=4: parent (2,4), split the final 4 as (2,2)
d=5: parent (3,4), split the final 4 as (2,2)
```

have identical block-local data `(peel=2, balanced, final, block_size=4)`, but
their exact feasible normalized intervals are respectively `[0,504]` and
`[552,648]`. They are disjoint. This rules out a certificate-independent
function of those block-local features. No disjoint-pair obstruction was found
through `d=10` after adding prefix state, symmetric exterior moments, or the
full oriented moment state. That absence is not evidence of existence; it only
means the richer negative result comes from the exact divergence-system
inconsistency, not from marginal interval separation.

## Conclusion and next experiment

Peel-width-three feasibility is exactly certified for every tested
`d=2,...,16`, but the data does **not** reveal a dimension-stable local rule
analogous to the k=2 certificate. The arbitrary max-flow patterns are strongly
nonunique; block-local normalization is impossible; and the four declared
dimension-shared polynomial classes fail exactly. A different nonlinear or
larger bounded-state rule is not ruled out.

The single highest-value next discovery experiment is an exact, complete
weighted-degree-at-most-four ansatz in the oriented moment state
`(z,L,R,VL,VR,QL,QR)`, with weights `1,1,1,2,2,4,4`, reduced by the natural
left/right and final-block symmetries. Solve its divergence equations on
`d=3,...,12` and reserve `d=13,...,16` as holdouts. This adds the mixed terms
missing from P3 while remaining finite, interpretable, exact, and within the
current dimensional boundary. An inconsistency would give a substantially
stronger negative result; a nonnegative solution surviving holdouts would be
the first genuine structural candidate.

The Lean/Conjecture 3.30 line remains frozen at main commit `65e1056`; no Lean
file, theorem, pre-existing mathematical definition, existing result JSON, or
unrestricted `d>20` computation was touched in this checkpoint.

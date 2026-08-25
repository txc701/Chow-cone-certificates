# Desymmetrized degree-four ansatz: cumulative equality scan

Base checkpoint: `199b5d4462858d9e8337afce001fbd23724699c9`.
This decision gate keeps exactly the systematic 276-column lift committed at
that checkpoint. It does not append `phi_G`, `first(child)`, `last(child)`, or
any other feature. It uses one coefficient vector simultaneously in every
dimension, tests exact equalities only, and stops at `d=10` before any
nonnegativity optimization.

## 1. The unique `d=4` left-nullspace relation

In lexicographic row order

```text
(2,2,2), (2,4), (3,3), (4,2), (6),
```

the primitive positive generator of `ker(A^T)` is

```text
y = (6, 6, 8, 3, 1).
```

The corresponding exact `G` values are

```text
G = (30, 30, 40, 15, 5) = 5 y,
```

and the target vector is

```text
b = (-504, -24, -144, -24, 4392).
```

Direct exact verification over all 276 columns gives

```text
y^T A = 0,
y^T b = 6(-504) + 6(-24) + 8(-144) + 3(-24) + 4392 = 0.
```

This is precisely global divergence conservation in the normalized system.
For an edge `u -> v`, the normalized flow column contributes
`+G(v)/G(u)` at `u` and `-1` at `v`. Multiplication of row `c` by `G(c)`
therefore cancels that edge as `+G(v)-G(v)`. Target compatibility is the
identity `sum_c G(c) S4(c) = sum_c w4(c) = 0`.

Since the five-row coefficient matrix has rank four, its left nullity is one,
so this conservation vector spans the complete left kernel. Rank four is thus
structural: it is the largest rank any divergence system on these five states
can have. It is not evidence that this ansatz has captured a structural flow
formula.

## 2. Cumulative shared-coefficient construction

For each `D=4,...,10`, the system consists of every exact composition-state
equation from dimensions `4,...,D`, vertically stacked against the same named
276 coefficients. No dimension receives independent coefficients.

For auditability, a complete augmented equation is canonicalized by clearing
denominators, dividing by the integer gcd, and fixing its first nonzero sign.
Only equations proportional as complete `[A|b]` rows would be deduplicated.
There are no such duplicates in this scan, so the raw and deduplicated counts
agree at every prefix.

The exact results are:

| D | cumulative raw | cumulative dedup | rank A | rank [A\|b] | nullity | new constraints |
|---:|---:|---:|---:|---:|---:|---:|
| 4 | 5 | 5 | 4 | 4 | 272 | 4 |
| 5 | 13 | 13 | 11 | 11 | 265 | 7 |
| 6 | 26 | 26 | 23 | 23 | 253 | 12 |
| 7 | 47 | 47 | 43 | 43 | 233 | 20 |
| 8 | 81 | 81 | 76 | 76 | 200 | 33 |
| 9 | 136 | 136 | 130 | 130 | 146 | 54 |
| 10 | 225 | 225 | 217 | 217 | 59 | 87 |

Here “new constraints” means
`rank(A_<=D) - rank(A_<=D-1)`, with preceding rank zero at `D=4`.

The SHA-256 hashes of the deterministically ordered exact sparse rational
matrices and right-hand sides are:

| D | matrix SHA-256 | RHS SHA-256 |
|---:|:---|:---|
| 4 | `6a3fa99832757d90d4cd7d0e8e2cf75dc0156a984d93418159601db6899581ab` | `355b054e8f5fbf7bf0fcc364fa4169cfb4f988687915ba49dce5e8c7501966df` |
| 5 | `a26e8bcb19bd7e13e433cceaa55acf9b27aeb147abe4e40331e98552dac9fc13` | `1e657e0217d971c1a374515b4c21a84980fb40bd2d9efdb8e18cd665250d6fa4` |
| 6 | `cfd0f9f1e2a41bc7eedfd9c555fe0882b87549de37115215752a562604e42489` | `1e185d73ca48ef2db1889490a80a0489912c7fba6b26989399ca70a7e2a2fb18` |
| 7 | `10e7d604c3ad957b1bec0967bf7ce5566bd10b964af5d05a8df7ea1ddf27bf97` | `5e7d5ef4b6911ed32e0a0bb599755168d087df7149f453a2334ffcbdc69fea7d` |
| 8 | `a0c4ba1338e9f167219ba31357b6c0ccc2debcc1fdf94a1fa21613d981c154b4` | `480837bd03467ef426b8e58e127e899072797451be44511542b911f3cd360164` |
| 9 | `26e3b5006e569954d7904ba830638e7ad45fcc9da52daddbe8cf35cade3cadb3` | `584ccbd154a012c98888a497d8e1813a9c50ab6d767838234d441a94a0004fe8` |
| 10 | `3ab29b5c8c4db6251272db846b18748bd4fb2757276e8261ebbab9e0de2c94af` | `b884de88fcdc4aa29a5ea8b0330d770c295cfeb5d6980f3cd650fc6f0bc0e1a8` |

The raw and deduplicated hashes coincide because no row is removed.
The decision artifact additionally records a semantic system hash at each
prefix, binding the dimensions, ordered parameter names, row labels, matrix,
and right-hand side together.

## 3. Decision at `D=10`

Every cumulative prefix is equality-consistent. At the final authorized
prefix,

```text
rank(A_<=10) = rank([A_<=10|b_<=10]) = 217,
affine solution-space dimension = 276 - 217 = 59.
```

The decision artifact records one exact rational solution obtained by exact
sparse elimination with all 59 free coefficients set to zero. It has 217
nonzero coefficients. Direct substitution verifies all 225 residuals are
exactly zero, both before and after equation deduplication, with a separate
zero-residual count for every dimension block.

The `d=10` block contributes 87 new independent coefficient constraints.
Thus its rows genuinely shrink the `D=9` affine solution space from dimension
146 to dimension 59; they are not implied by the earlier dimensions.

## 4. Scope and stopping rule

This result establishes only equality consistency of the specified
276-column feature class through `d=10`. It does not establish edgewise
nonnegativity, a feasible flow, a canonical coefficient vector, or an all-`d`
formula. No inconsistency witness is present because no rank gap occurs.

The scan stops here. It does not test dimensions above 10, add features,
optimize nonnegativity, or attempt symbolic extrapolation.

Exact ranks, hashes, the full rational solution, and its verification are in
`results/k4_desymmetrized_scan/decision.json`. The gate-specific source
regenerates that artifact deterministically.

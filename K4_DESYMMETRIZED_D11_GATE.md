# Desymmetrized degree-four ansatz: exact `d=11` decision gate

Base checkpoint: `60b2fba4a4034e701ad38e344a4c2568ab834906`.
This gate preserves the committed 276 columns, their order, normalization,
and all `D<=10` numerical and semantic hashes. It appends exactly the `d=11`
state equations to the shared-coefficient training system. No feature is
added, removed, or renamed.

## 1. Frozen-prefix embedding

The first 225 equations of the new cumulative system reproduce the committed
`D<=10` prefix exactly. Its hashes remain

```text
matrix: 3ab29b5c8c4db6251272db846b18748bd4fb2757276e8261ebbab9e0de2c94af
RHS:    b884de88fcdc4aa29a5ea8b0330d770c295cfeb5d6980f3cd650fc6f0bc0e1a8
system: 74440aade255dd61367e0671bffdb490cbe9fb4a1af5b7f6e86f2a6de5d58a53
```

The `d=11` block has 144 state equations and 382 allowed edges. No complete
augmented equations become proportional after adjoining it, so the cumulative
raw and deduplicated row counts are both 369. The cumulative graph data used
to construct the equations contains 853 edges.

The new exact hashes are

| system | matrix SHA-256 | RHS SHA-256 | semantic system SHA-256 |
|:---|:---|:---|:---|
| `d=11` block | `f8f12e50980be7cd373291a670e3238513691d1e9735cebcc578f0bef28c36e4` | `80e85f7ab8850a099518736a85a9a508eab54d11f5c9d786c5a63ae5b7dbf070` | `205ece2143e69f67958dc73fc1fed0056be9440d3d9987b9a7b1906ac9e8665e` |
| cumulative `D<=11` | `bf20120706d3b3974fa0668f56d4058e686fe9afcc57cce61c9e307cbc3b3cee` | `9dc33fcaf2e446f0adbedcb221659bc8727db67646b288b5c7ca53825fba3397` | `831caf0f2d25a1b3591779b487ea807552f969a0b1ef5682190104ce74529d20` |

## 2. Exact ranks and decision

The standalone `d=11` block already has

```text
rank(A_11)       = 135,
rank([A_11|b_11]) = 136.
```

Thus `d=11` is inconsistent even without the lower-dimensional equations.
Its coefficient and augmented left-nullities are respectively `144-135=9`
and `144-136=8`.
For the cumulative shared-vector system,

```text
raw rows                         = 369,
deduplicated rows                = 369,
rank(A_<=11)                     = 261,
rank([A_<=11|b_<=11])            = 262,
coefficient nullity              = 276 - 261 = 15,
left nullity                     = 369 - 261 = 108,
new independent d=11 constraints = 261 - 217 = 44.
```

Relative to the 59-dimensional `D<=10` affine solution space, the homogeneous
direction space would shrink by 44 dimensions, from 59 to 15. However, the
augmented rank gap makes the actual affine intersection empty. The number 15
is therefore the nullity of the coefficient matrix, not the dimension of a
nonempty solution family.

This is decision branch A. There is no exact coefficient solution at `D<=11`,
so branches B and C do not apply.

## 3. Structural conservation versus the obstruction

For every `d=4,...,11`, the code independently constructs the primitive
block-supported conservation vector

```text
gamma_d(c) = G_d(c) / gcd_c G_d(c).
```

Each satisfies `gamma_d^T A=0` and `gamma_d^T b=0` exactly. Their disjoint
dimension supports give eight independent structural conservation relations.
They cannot certify inconsistency because their target pairings vanish.

The augmented left-nullity is `369-262=107`. Beyond the eight conservation
vectors, it contains 99 target-compatible non-conservation directions. The
remaining one-dimensional quotient of the 108-dimensional coefficient left
kernel is target-active and accounts for the rank gap.

The new witness instead satisfies

```text
y^T A_<=11 = 0,
y^T b_<=11 =
  1005248254755888251487347868119513082428284468936147983360 != 0.
```

It is supported entirely on `d=11`, confirming that the obstruction is
already present in that standalone block rather than arising only from
sharing coefficients with earlier dimensions.

The saved integer multipliers have gcd one and are oriented to make the
target pairing positive. Six deterministic exact row orderings were tested
for fundamental circuits; their support sizes were

```text
canonical 106, reverse 132, sparse-first 105, dense-first 117,
short-compositions-first 134, long-compositions-first 103.
```

The selected long-compositions-first witness has 103 rows. On exactly that
support,

```text
rank(A_support)       = 102,
rank([A_support|b])   = 103.
```

Hence its coefficient-row dependence is a full-support circuit: deleting any
participating row leaves coefficient-independent, and therefore consistent,
equations. This proves exact inclusion-minimality. It does not prove global
minimum cardinality among every possible witness support.

The complete list of all 103 participating support compositions and their
primitive integer multipliers is in
`results/k4_desymmetrized_d11_gate/decision.json`.

## 4. Stopping rule

The gate stops at the first inconsistent training dimension. No `d=12` state,
edge, matrix, or residual was constructed. No nonnegativity optimization,
sign search, symbolic extrapolation, or feature repair was attempted.

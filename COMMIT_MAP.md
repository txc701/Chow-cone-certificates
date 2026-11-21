# Commit map: private history to public history

The public history was produced from the private repository by removing one file,
`paper/cheng-lin-v3.pdf` (a third-party arXiv PDF), from every commit. Author, committer,
dates, messages and all other content are unchanged; every hash differs, because the
file was added in the first commit. That first commit contained nothing else and is an
empty commit here.

The notes in this repository cite commits by their **private** hash. Use this table to
find them here.

| date (author) | private hash | public hash | subject |
|---|---|---|---|
| 2026-08-09 | `d11b5c7` | `c0f3601` | Initialize Cheng-Lin Conjecture 3.30 project |
| 2026-08-12 | `4f0b233` | `be757ba` | Stage 1: dual weight implementations, d<=5 ideal-enumeration oracle, max-flow cross-validation |
| 2026-08-12 | `347d017` | `cb66591` | Prove flow/ideal equivalence; add README and STATUS |
| 2026-08-12 | `892007d` | `624d630` | Stage 2: exact max-flow feasible for all d<=25 (reproduces paper's d<=19, extends +6) |
| 2026-08-18 | `88e5448` | `3b80d09` | Stage 3 checkpoint: persist structural flow experiments |
| 2026-08-18 | `ac60a2e` | `55c3a28` | Stage 3 complete: staircase tight ideals, shell decomposition, peel2 conjecture |
| 2026-08-18 | `2a9cb9f` | `f7ddd5a` | First decision gate report |
| 2026-08-18 | `d3fb1f6` | `ec8f62e` | Audit passes: explicit uniform peel2 certificate proves Conjecture 3.30 |
| 2026-08-18 | `e0e64a3` | `e2a9e46` | Adversarial re-audit of Lemma 2: no counterexample; proof hardened |
| 2026-08-18 | `dc87a7b` | `8824621` | Referee-facing standalone draft + dependency map (math frozen at e0e64a3) |
| 2026-08-21 | `131daca` | `b721ed6` | Branch A complete: Lean 4 certification of the combinatorial core |
| 2026-08-21 | `14527dc` | `b2cb601` | Branch B: k=4 fourth-moment analogue — new conjecture + deformed structure |
| 2026-08-21 | `ddb8437` | `06c5b6d` | STATUS: record Lean certification completion and k4 branch |
| 2026-08-24 | `65e1056` | `520d3a0` | Hygiene: correct Lean status and preserve axiom audit |
| 2026-08-24 | `f3efcfd` | `6e885ff` | K4: exact width-3 discovery checkpoint |
| 2026-08-24 | `7c37334` | `2d2fd2d` | K4: decide complete degree-4 mirror ansatz |
| 2026-08-24 | `edd9092` | `90ba739` | K4: analyze the d=4 mirror obstruction |
| 2026-08-24 | `59560a5` | `980629e` | K4: audit reversal admissibility |
| 2026-08-24 | `199b5d4` | `b7f5311` | K4: commit desymmetrized d4 gate |
| 2026-08-24 | `60b2fba` | `5b19493` | K4: checkpoint cumulative equality scan through d10 |
| 2026-08-25 | `0b36038` | `83ab635` | K4: freeze degree-four d11 obstruction |
| 2026-08-28 | `0457403` | `03561a8` | K4: checkpoint degree-five quotient gate |
| 2026-08-28 | `c92951f` | `3c65b2d` | Prove the uniform k=4 fourth-moment certificate |
| 2026-08-28 | `5182137` | `dc667d6` | Lift the k=4 certificate to Cheng–Lin’s matroid theorem |
| 2026-08-28 | `6360104` | `bee8307` | Add referee-facing k2-k4 Chow cone manuscript |
| 2026-09-01 | `34317b9` | `6845da3` | Polish the referee-facing Chow cone manuscript |

Full hashes (private, public):

```
d11b5c7428dd227e27a9363049b2f014156a450f  c0f36015da780b37dcc06d0e7a2d5a4e0062e5fb
4f0b23384c67af003987197e0f2e0af1c6b8fff0  be757ba243025b222774757c668c97e50cfc3c08
347d017dedc4258a765142ae4ed5c30b729a6d8d  cb665912fcd298e2ac674ca5782a1982f4898844
892007d8bce84f855ca9ef908b821107d0d17a68  624d6306b758b227e7e60dd175a8205f2c0094de
88e54480495f2d2ba629296f50a78b2fcab5753a  3b80d098cf73e74e3df2810f375bc0d026f11ca5
ac60a2e0b3d73116f9fcfeecfa5aa260495bb702  55c3a28c6e80fc1561af283c6d241f56ec77761d
2a9cb9f952679b79b6a9d560a6cab98b48a3dc8a  f7ddd5a70dc70a8544c1a6521c3be7e3d2414e16
d3fb1f6520ae653859bdcd88a76bdfeddadee9e8  ec8f62e5748a9ea9ec7a3c6508841b411666165a
e0e64a3da37c725df1f2bacbc65162f255f008a2  e2a9e467e78ce22221ed2ebf9ebbd19b55661447
dc87a7bd36e8210a02155335dbba5ff1c7558f38  8824621c92f020e2b3fd915fcee7c35ae3531ce1
131daca088ce1f3617bdf7a8717f724648841173  b721ed649d872ada7db661e12be8b2c99cdaa27d
14527dc2b85994cc777c5c2196d5c594d2af0bc2  b2cb601897252f533035686b613a62f91eeddd5c
ddb84370ff7a26f088550f170238ad848a4a8ea6  06c5b6d1847898c88af713cbe4dc43f89b308e4f
65e105603c2367b8bbde3ff8eed7226e2d17a1a2  520d3a09d9053912d1d5131c1f55686597da4fbc
f3efcfd4fa718884ed9934590af83f46c0772a00  6e885ffeac3341ca3e71a9a30a968c6247045a2e
7c37334f3872b1f4a70febf0da51565b26433626  2d2fd2dcd213ecc348bdd79ad5efce641f81a2e0
edd9092ed632cf802bcc4a4ede7fdefee08b15f1  90ba739629bfb8bdef5f07c4ec8825332256ba29
59560a535c7c1ae3201a44215053ac24cc50b803  980629e70d50d2ebe0193262d005bb0878b85456
199b5d4462858d9e8337afce001fbd23724699c9  b7f5311d349b2090fb04ddb712cfc8844380ee81
60b2fba4a4034e701ad38e344a4c2568ab834906  5b19493e823ac35e4d4d89ae6d2c1bec2234da66
0b3603807fac8698e412053204e252cfe7da2c1c  83ab635c015c119801f9dd6ce1b76b34c19c1c37
0457403cda9800beea75b983b844e26716f13466  03561a84a6ec527f9f4a36f40cbf22c7a99386be
c92951f3cde24cb946171d66a033c4ac7f7b2ecc  3c65b2dbc1e9a86688f7895b22c5cb3013558092
518213795a6da1048b99f9d130de0dd8dce4ef76  dc667d6a99298d0264b60c7eb30a00c4e9769997
6360104dfa8fcaf3bb85132384530fc78a7fbc38  bee83075808dd9d0de5cacda2085270a942529a9
34317b9d0d7a0e4463971fab6757391f1b6533a4  6845da333a8878d08c2510748142874987197bf9
```

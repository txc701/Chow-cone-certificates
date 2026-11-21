# Commit map: private history to public history

The public history was produced from the private repository by removing one file,
`paper/cheng-lin-v3.pdf` (a third-party arXiv PDF), from every commit. Author names, dates,
messages and all other content are unchanged. The e-mail field of every commit was
replaced by the author's GitHub `noreply` address. Every hash differs. The first
commit contained nothing but the removed file and is an empty commit here.

The notes in this repository cite commits by their **private** hash. Use this table to
find them here.

| date (author) | private hash | public hash | subject |
|---|---|---|---|
| 2026-08-09 | `d11b5c7` | `652456a` | Initialize Cheng-Lin Conjecture 3.30 project |
| 2026-08-12 | `4f0b233` | `964f443` | Stage 1: dual weight implementations, d<=5 ideal-enumeration oracle, max-flow cross-validation |
| 2026-08-12 | `347d017` | `7550d74` | Prove flow/ideal equivalence; add README and STATUS |
| 2026-08-12 | `892007d` | `caa4f55` | Stage 2: exact max-flow feasible for all d<=25 (reproduces paper's d<=19, extends +6) |
| 2026-08-18 | `88e5448` | `3732cc4` | Stage 3 checkpoint: persist structural flow experiments |
| 2026-08-18 | `ac60a2e` | `92724d6` | Stage 3 complete: staircase tight ideals, shell decomposition, peel2 conjecture |
| 2026-08-18 | `2a9cb9f` | `590bb06` | First decision gate report |
| 2026-08-18 | `d3fb1f6` | `a9515ee` | Audit passes: explicit uniform peel2 certificate proves Conjecture 3.30 |
| 2026-08-18 | `e0e64a3` | `840bff7` | Adversarial re-audit of Lemma 2: no counterexample; proof hardened |
| 2026-08-18 | `dc87a7b` | `9ab6cfe` | Referee-facing standalone draft + dependency map (math frozen at e0e64a3) |
| 2026-08-21 | `131daca` | `d44358a` | Branch A complete: Lean 4 certification of the combinatorial core |
| 2026-08-21 | `14527dc` | `1fa4ab2` | Branch B: k=4 fourth-moment analogue — new conjecture + deformed structure |
| 2026-08-21 | `ddb8437` | `d5083d4` | STATUS: record Lean certification completion and k4 branch |
| 2026-08-24 | `65e1056` | `0eddd6a` | Hygiene: correct Lean status and preserve axiom audit |
| 2026-08-24 | `f3efcfd` | `63d29a1` | K4: exact width-3 discovery checkpoint |
| 2026-08-24 | `7c37334` | `942be83` | K4: decide complete degree-4 mirror ansatz |
| 2026-08-24 | `edd9092` | `c7277ac` | K4: analyze the d=4 mirror obstruction |
| 2026-08-24 | `59560a5` | `c584a4c` | K4: audit reversal admissibility |
| 2026-08-24 | `199b5d4` | `2616825` | K4: commit desymmetrized d4 gate |
| 2026-08-24 | `60b2fba` | `5315542` | K4: checkpoint cumulative equality scan through d10 |
| 2026-08-25 | `0b36038` | `2434554` | K4: freeze degree-four d11 obstruction |
| 2026-08-28 | `0457403` | `ccbc043` | K4: checkpoint degree-five quotient gate |
| 2026-08-28 | `c92951f` | `f44aa18` | Prove the uniform k=4 fourth-moment certificate |
| 2026-08-28 | `5182137` | `5c509ec` | Lift the k=4 certificate to Cheng–Lin’s matroid theorem |
| 2026-08-28 | `6360104` | `9bcf0f0` | Add referee-facing k2-k4 Chow cone manuscript |
| 2026-09-01 | `34317b9` | `3aa0251` | Polish the referee-facing Chow cone manuscript |

Full hashes (private, public):

```
d11b5c7428dd227e27a9363049b2f014156a450f  652456a272270965feb8cd881fb0963e1f194a23
4f0b23384c67af003987197e0f2e0af1c6b8fff0  964f44348347bdc877aa40eeef90e836d01ef5ba
347d017dedc4258a765142ae4ed5c30b729a6d8d  7550d74a057ebc23c9723718ebb70f3789b7e4f7
892007d8bce84f855ca9ef908b821107d0d17a68  caa4f55a5029fb98b492b19737fea579d3ca4cd7
88e54480495f2d2ba629296f50a78b2fcab5753a  3732cc4f3bb953a953fa6eccf81bb44ba806d75d
ac60a2e0b3d73116f9fcfeecfa5aa260495bb702  92724d625005e779a199444bdaf218d5a7caabce
2a9cb9f952679b79b6a9d560a6cab98b48a3dc8a  590bb06da5bc99abe4aa9e7fde07d3335deb6586
d3fb1f6520ae653859bdcd88a76bdfeddadee9e8  a9515eeade6538036ba651e4920e2bf852227ff3
e0e64a3da37c725df1f2bacbc65162f255f008a2  840bff78e2ea067b9f6104d78112df4187dfc728
dc87a7bd36e8210a02155335dbba5ff1c7558f38  9ab6cfed2627461cee3118d117f0549936ecb4d6
131daca088ce1f3617bdf7a8717f724648841173  d44358a104e04f1131308ecefc83eac50d3019ce
14527dc2b85994cc777c5c2196d5c594d2af0bc2  1fa4ab2563275afa16a49729c5fd5344fd51df6c
ddb84370ff7a26f088550f170238ad848a4a8ea6  d5083d4ad0fe4e3caa5e59b1e3719bac3ab38c8e
65e105603c2367b8bbde3ff8eed7226e2d17a1a2  0eddd6a19a5a46e2c62e4bf32118638771e334eb
f3efcfd4fa718884ed9934590af83f46c0772a00  63d29a11aa6c5f57b6d33cf6eeffdabafcf3ef10
7c37334f3872b1f4a70febf0da51565b26433626  942be83f37866efc49526ec34a8edf3de7dde57e
edd9092ed632cf802bcc4a4ede7fdefee08b15f1  c7277acf49527e235f47810db0b2860b56997980
59560a535c7c1ae3201a44215053ac24cc50b803  c584a4cc5331e74d8b5e3bfb086083e0738cd9ff
199b5d4462858d9e8337afce001fbd23724699c9  26168250c1d599668b0e87c8bca9abcad6804939
60b2fba4a4034e701ad38e344a4c2568ab834906  5315542dd4bfe220653673642fef38214db02fe0
0b3603807fac8698e412053204e252cfe7da2c1c  24345547e2f7f231ae702976895d474cfc3d0f65
0457403cda9800beea75b983b844e26716f13466  ccbc04301d3717f71e548ba2123d76e2aff7ea43
c92951f3cde24cb946171d66a033c4ac7f7b2ecc  f44aa18c3bd639f90d0e794e6660b16e1eb33794
518213795a6da1048b99f9d130de0dd8dce4ef76  5c509ecbde4d6dbaf0d1334e443570c8b0d347c1
6360104dfa8fcaf3bb85132384530fc78a7fbc38  9bcf0f098eb3d29cd79ddf0a99e1fae665fa95a9
34317b9d0d7a0e4463971fab6757391f1b6533a4  3aa0251c02fbbe59b312e8a926852f1c3410dc1d
```

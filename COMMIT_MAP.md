# Commit map: private history to public history

The public history was produced from the private repository by removing one file,
`paper/cheng-lin-v3.pdf` (a third-party arXiv PDF), from every commit. Dates, messages and
all other content are unchanged. In the commit fields the author's name is written
uniformly as `Xichen Tang` and the e-mail is the author's GitHub `noreply` address;
the private history has the name in two forms and machine-local addresses. Every
hash differs. The first commit contained nothing but the removed file and is an
empty commit here.

The notes in this repository cite commits by their **private** hash. Use this table to
find them here.

| date (author) | private hash | public hash | subject |
|---|---|---|---|
| 2026-08-09 | `d11b5c7` | `f0258a0` | Initialize Cheng-Lin Conjecture 3.30 project |
| 2026-08-12 | `4f0b233` | `d0c54bd` | Stage 1: dual weight implementations, d<=5 ideal-enumeration oracle, max-flow cross-validation |
| 2026-08-12 | `347d017` | `180ab12` | Prove flow/ideal equivalence; add README and STATUS |
| 2026-08-12 | `892007d` | `d864a74` | Stage 2: exact max-flow feasible for all d<=25 (reproduces paper's d<=19, extends +6) |
| 2026-08-18 | `88e5448` | `1a4ec45` | Stage 3 checkpoint: persist structural flow experiments |
| 2026-08-18 | `ac60a2e` | `8b80b6b` | Stage 3 complete: staircase tight ideals, shell decomposition, peel2 conjecture |
| 2026-08-18 | `2a9cb9f` | `e83b39b` | First decision gate report |
| 2026-08-18 | `d3fb1f6` | `51d0722` | Audit passes: explicit uniform peel2 certificate proves Conjecture 3.30 |
| 2026-08-18 | `e0e64a3` | `51da029` | Adversarial re-audit of Lemma 2: no counterexample; proof hardened |
| 2026-08-18 | `dc87a7b` | `d3f2885` | Referee-facing standalone draft + dependency map (math frozen at e0e64a3) |
| 2026-08-21 | `131daca` | `f94b055` | Branch A complete: Lean 4 certification of the combinatorial core |
| 2026-08-21 | `14527dc` | `b91d565` | Branch B: k=4 fourth-moment analogue — new conjecture + deformed structure |
| 2026-08-21 | `ddb8437` | `c5ad302` | STATUS: record Lean certification completion and k4 branch |
| 2026-08-24 | `65e1056` | `70025f4` | Hygiene: correct Lean status and preserve axiom audit |
| 2026-08-24 | `f3efcfd` | `1f2c38f` | K4: exact width-3 discovery checkpoint |
| 2026-08-24 | `7c37334` | `6fa26c1` | K4: decide complete degree-4 mirror ansatz |
| 2026-08-24 | `edd9092` | `fae29ea` | K4: analyze the d=4 mirror obstruction |
| 2026-08-24 | `59560a5` | `2c04e2f` | K4: audit reversal admissibility |
| 2026-08-24 | `199b5d4` | `cf704fe` | K4: commit desymmetrized d4 gate |
| 2026-08-24 | `60b2fba` | `5265977` | K4: checkpoint cumulative equality scan through d10 |
| 2026-08-25 | `0b36038` | `dca882d` | K4: freeze degree-four d11 obstruction |
| 2026-08-28 | `0457403` | `ce2c559` | K4: checkpoint degree-five quotient gate |
| 2026-08-28 | `c92951f` | `27248b9` | Prove the uniform k=4 fourth-moment certificate |
| 2026-08-28 | `5182137` | `a0bf73b` | Lift the k=4 certificate to Cheng–Lin’s matroid theorem |
| 2026-08-28 | `6360104` | `0fea55d` | Add referee-facing k2-k4 Chow cone manuscript |
| 2026-09-01 | `34317b9` | `ae288d3` | Polish the referee-facing Chow cone manuscript |

Full hashes (private, public):

```
d11b5c7428dd227e27a9363049b2f014156a450f  f0258a0ddf5b39ff8fd3d99b11c9f2e7703397e8
4f0b23384c67af003987197e0f2e0af1c6b8fff0  d0c54bdeaa14ddad4e73bae647daba89be41d7a0
347d017dedc4258a765142ae4ed5c30b729a6d8d  180ab1204a9306eabfc90894b6e2384a0d97af29
892007d8bce84f855ca9ef908b821107d0d17a68  d864a74ca012e3e2a9c6dee31456d594fd44c397
88e54480495f2d2ba629296f50a78b2fcab5753a  1a4ec45bc19bcd172bfab552189041f5cbb04ca2
ac60a2e0b3d73116f9fcfeecfa5aa260495bb702  8b80b6bf402abca7125e64fd3ac7539a97b408f6
2a9cb9f952679b79b6a9d560a6cab98b48a3dc8a  e83b39b647ab9bf28bc699f5868f72a1b55bae08
d3fb1f6520ae653859bdcd88a76bdfeddadee9e8  51d07222e2072126e7fd3267e9883e936a23cf10
e0e64a3da37c725df1f2bacbc65162f255f008a2  51da0297a4ac289d2ff29e1dbdea63f81be097b1
dc87a7bd36e8210a02155335dbba5ff1c7558f38  d3f2885df6f98d338e6698de8ebf24bb4c98706d
131daca088ce1f3617bdf7a8717f724648841173  f94b055c1d8a24b885c3935d9d7ecef4a35f56a5
14527dc2b85994cc777c5c2196d5c594d2af0bc2  b91d56531b36a7983c93a5d32b0a01b3f78f7d00
ddb84370ff7a26f088550f170238ad848a4a8ea6  c5ad302ae0402c5b216420abec7ecb79475aeda2
65e105603c2367b8bbde3ff8eed7226e2d17a1a2  70025f4248936c969dd3246748a9b7f94be9a062
f3efcfd4fa718884ed9934590af83f46c0772a00  1f2c38fbeb42babe86069e956cabb6fd77fb65b9
7c37334f3872b1f4a70febf0da51565b26433626  6fa26c13dfc6bf915d5520fd06db2de6eb12b4f5
edd9092ed632cf802bcc4a4ede7fdefee08b15f1  fae29eac2b90b259e59f280d19ef3ff722c4aedc
59560a535c7c1ae3201a44215053ac24cc50b803  2c04e2f93d0fad3ff2c73b2591a3edb851bc5314
199b5d4462858d9e8337afce001fbd23724699c9  cf704fea99b03729d859b72f0e9eef70b03b30f4
60b2fba4a4034e701ad38e344a4c2568ab834906  526597745b194e0646b946d285b4e1dd4e8694ea
0b3603807fac8698e412053204e252cfe7da2c1c  dca882d5a6a4005dc5aa5ab00d6d76f8faa881bb
0457403cda9800beea75b983b844e26716f13466  ce2c559d8a08f65ac4ca237b25fd23b1727065ca
c92951f3cde24cb946171d66a033c4ac7f7b2ecc  27248b91da021c36b4bba960fbd361e3b4ad9a86
518213795a6da1048b99f9d130de0dd8dce4ef76  a0bf73bbfa0025f81990fa39c586cdd0ac954507
6360104dfa8fcaf3bb85132384530fc78a7fbc38  0fea55d21bf04c934cd180d3294f23d38ad50d10
34317b9d0d7a0e4463971fab6757391f1b6533a4  ae288d30a1714c1b2356af9bdea442889eed0079
```

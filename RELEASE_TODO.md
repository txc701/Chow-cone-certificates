# Open items before the first public release

Nothing in this repository has been published. This file lists what is still undecided or
unverified. Remove it, and the pre-release note at the top of `README.md`, when tagging.

## Decisions that belong to the author

1. **Author line and date of the manuscript.** The TeX still has `\author{Anonymous}` and
   `\date{August 28, 2026}`.
2. **Licence.** There is no `LICENSE` file. A common choice would be Apache-2.0 for `src/`,
   `tests/` and `lean/`, and CC BY 4.0 for the notes and the manuscript.
3. **The AI disclosure in the paper, and one open point of provenance.** `PROVENANCE.md` now
   records how both certificates were found; Part 2, added on 2026-11-21 from the session
   logs of the coding agent, covers `k = 4`, and Part 3 the texts. The manuscript now has a
   section "Use of AI tools", written as a draft for the author to confirm sentence by
   sentence; it must stay in agreement with `PROVENANCE.md`. `PROVENANCE.md` leaves open how
   the prompt that started the `k = 4` run was drafted, which only the author can state. The
   `k = 4` commits carry no `Co-Authored-By` line; `PROVENANCE.md`, not the commit metadata, is
   the record of how that work was done.
4. **Whether the first version includes the `k = 4` theorem.** Two AI reviews found no gap;
   no human has refereed it.
5. **Identity on new commits.** The commits added in November 2026 use an address set only in
   this clone's local git configuration. Choose the address to appear publicly (a GitHub
   `noreply` address is possible) before pushing; the commits can be re-authored while they
   are still local. The historical commits use machine-local addresses that GitHub cannot
   link to an account, and one of them (`Polish the referee-facing Chow cone manuscript`)
   has a placeholder instead of an e-mail address. A `.mailmap` can unify how they display
   without rewriting them.
6. **How to distribute the review material that is not in this repository**: the
   independent verifier with its witness archive (4 MB) and the label-level audit script for
   the `k = 4` certificate. Options are release assets, a separate repository, or not at
   all. Checksums are in `RELEASE_CHECKS.md`.
7. **Repository name and URL.** The manuscript says "the accompanying repository" without a
   link.

## Still to verify

8. **Priority.** On 2026-11-19 an arXiv keyword search and one web search found no follow-up
   to Cheng–Lin's paper proving Conjecture 3.30 or any case of Conjecture 3.14. That is not a
   literature review. Repeat it on the day of release.
9. **arXiv endorsement** for math.CO.
10. **Human review of the `k = 4` proof**, in particular the charge table of manuscript §8.

## Optional improvements

11. Cite G. Bérczi, B. Coron, C. Eur and S. Li, arXiv:2610.17135, in the introduction: it
    disproves the real-rootedness conjecture for Chow polynomials, which changes the context
    of moment inequalities.
12. Corrections to the dated notes proposed in `RELEASE_CHECKS.md` (six stale declaration
    names in `LEAN_CORRESPONDENCE.md`).

## At tagging time

```sh
python3 -m pytest tests/                                   # must pass in full
python3 src/run_functional_scan.py 20 16 10 --witnesses results/functional_scan/witnesses.jsonl.gz
python3 src/verify_functional_scan.py 8 --witnesses results/functional_scan/witnesses.jsonl.gz
git status --short                                         # results/ must be unchanged
cd lean && lake build && lake env lean AxiomCheck.lean && cd ..
latexmk -pdf CHOW_CONE_FLOWS_MANUSCRIPT.tex
```

Then check that the two digests and the test count printed in manuscript §12 still match,
remove this file and the pre-release note, and tag:

```sh
git branch -f main functional-scan       # a fast-forward: main is an ancestor of functional-scan
git tag -a v1.0 main -m "First public release"
```

`main` then contains everything. The earlier branches (`k4-fourth-moment`,
`manuscript-language-pass`, `external-referee-dc87a7b`) are ancestors or snapshots and may be
published or omitted. To keep the frozen `k = 2` state addressable, tag the old head of
`main` first, for example as `k2-lean-frozen`; `COMMIT_MAP.md` gives its hash.

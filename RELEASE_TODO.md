# Open items before the first public release

Nothing in this repository has been published. This file lists what is still undecided or
unverified. Remove it, and the pre-release note at the top of `README.md`, when tagging.

## Decisions that belong to the author

1. **Author line and date of the manuscript.** The TeX still has `\author{Anonymous}` and
   `\date{August 28, 2026}`.
2. **Licence.** Decided by the author on 2026-11-21: Apache-2.0 for code (`LICENSE`), CC BY 4.0
   for the manuscript and the notes (`LICENSE-CC-BY-4.0`); the scope is stated in `README.md`.
   One choice was made in preparing the files and is still the author's to confirm: the
   generated outputs in `results/` are placed under Apache-2.0 with the code.
3. **The AI disclosure in the paper.** The manuscript has a section "Use of AI tools" and
   `PROVENANCE.md` has three parts; both include the author's statements of 2026-11-21 on how
   the prompt of the `k = 4` run was drafted and on the origin of the review pack. Keep the
   two in agreement when either changes. One point stays open for good: which agent first
   proposed the cascade. The `k = 4` commits carry no `Co-Authored-By` line; `PROVENANCE.md`,
   not the commit metadata, is the record of how that work was done.
4. **Whether the first version includes the `k = 4` theorem.** Two AI reviews found no gap;
   no human has refereed it.
5. **Identity on new commits.** Decided: the `noreply` address shown in the author's GitHub
   account settings. The author will supply it; it is not to be guessed. Until then the
   commits of November 2026 carry an address set only in this clone's local git
   configuration, and they must be re-authored before any push. The historical commits use
   machine-local addresses that GitHub cannot link to an account, and one of them (`Polish
   the referee-facing Chow cone manuscript`) has a placeholder instead of an e-mail address.
   A `.mailmap` can unify how they display without rewriting them.
6. **How to distribute the review material that is not in this repository**: the
   independent verifier with its witness archive (4 MB) and the label-level audit script for
   the `k = 4` certificate. Options are release assets, a separate repository, or not at
   all. Checksums are in `RELEASE_CHECKS.md`.
7. **Repository name and URL.** The author's choice is `chow-cone-certificates`, to be made
   public after version 1 is final. The manuscript still says "the accompanying repository"
   without a link; add the URL once the repository exists. No push and no tag until the
   author says so.

## Still to verify

8. **Priority.** On 2026-11-19 an arXiv keyword search and one web search found no follow-up
   to Cheng–Lin's paper proving Conjecture 3.30 or any case of Conjecture 3.14. That is not a
   literature review. Repeat it on the day of release.
9. **arXiv endorsement** for math.CO: unconfirmed. The author will start a submission to see
   whether the system asks for an endorsement.
10. **Human review of the `k = 4` proof**, in particular the charge table of manuscript §8.

## Optional improvements

11. Done on 2026-11-21: the introduction cites Bérczi, Coron, Eur and Li, arXiv:2610.17135.
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

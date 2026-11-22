# Provenance of the certificates

This file describes the traceable discovery process inside this project. It makes no claim
about priority in the literature. Part 1 covers the `k = 2` certificate, Part 2 the `k = 4`
certificate, Part 3 the texts, Part 4 the Lean formalization of the `k = 4` certificate.

Each statement is labelled by its source:

* **[repo]** — verifiable from this repository's files and commit history.
* **[author]** — stated by the author (Xichen Tang) from the author's own ChatGPT
  conversations, which are not part of this repository. For Part 1 the author re-read the
  conversation of 2026-08-18 and confirmed the statements on 2026-11-20. For Part 2 the
  statements were relayed on 2026-11-21.
* **[log]** — read on 2026-11-21 by an AI assistant (Claude Code), at the author's request,
  from the session logs that the coding agent of Part 2 left on the author's machine. The
  logs are not part of this repository. What they show and what they hide is described at
  the start of Part 2.
* **[session]** — stated by the AI assistant (Claude Code) that carried out the work of
  Part 4, from its own working session of 21 and 22 November 2026. The record of that
  session is not part of this repository.

## Part 1. The `k = 2` certificate

### Who contributed what

1. **Problem and coefficients: Cheng and Lin.** Conjecture 3.30, the coefficients $U_J$,
   $a_J$, the inequality of Corollary 3.28 and the monotonicity inequalities of Lemma 3.29 are
   from R. Cheng and W. Lin, arXiv:2603.21680v3. They report computer verification for
   $d\le 19$ (Remark 3.31). **[repo: `README.md`, pinned source]**

2. **Experimental pattern: this repository's exact computations.** Exact big-integer
   max-flow showed feasibility for every $d\le 25$, and the edge-restriction experiments
   showed that certificates supported only on peel-2 splits $n_i\to(2,n_i-2)$ or
   $(n_i-2,2)$ exist for every $d\le 25$, while `peel2_left` alone fails at $d=3$. The
   decision-gate report stated the "peel2 conjecture" and had no uniform formula.
   **[repo: commits `ac60a2e` (2026-08-18 12:32:32 UTC) and `2a9cb9f` (12:33:41 UTC),
   `REPORT.md` items 6 and "peel2 conjecture", `results/stage3_restrictions.json`,
   `results/stage3_peel2_d21-25.json`]**
   These commits carry `Co-Authored-By: Claude` trailers: the computations were written and
   run with Claude Code as coding assistant.

3. **Uniform candidate: ChatGPT, in conversation with the author.** The author took the
   experiment report to a ChatGPT conversation at 12:35 UTC on 2026-08-18. At 12:40:59 UTC
   ChatGPT, combining the peel-2 pattern with Cheng–Lin's coefficients, proposed the
   explicit candidate: on the designated peel-2 moves take flow $G(\mathrm{child})$, with
   $G(\mathbf n)=U_J\prod_i(n_i-1)$. The original candidate already stated the final-block
   multiplicity: when the final block $4$ splits as $4\to(2,2)$, the left and right moves
   land on the same Boolean cover edge, each contributes $G(\mathrm{child})$, and the edge
   carries $2\,G(\mathrm{child})$. **[author]**
   The repository records the candidate as "proposed externally" (`RESEARCH_NOTES.md` §9,
   `PROOF_CONJECTURE_3_30.md`, commit `d3fb1f6`). The timing is consistent with the commit
   history: the report was committed at 12:33:41 UTC and the audit of the candidate at
   12:54:49 UTC. **[repo]**

4. **Audit and proof: this repository.** Commit `d3fb1f6` (2026-08-18 12:54:49 UTC)
   re-derived $w(c)=G(c)\sum_i\rho(n_i)$, the three ratio identities, and the in-edge
   bijection (Lemma 2), added an independent generator `src/explicit_certificate.py` that
   assigns flows by the closed formula, and checked divergence $=w_J$ at every support node
   for $d\le 25$. Commit `e0e64a3` (22:10:36 UTC) hardened Lemma 2 after an adversarial
   re-audit. Both carry `Co-Authored-By: Claude` trailers. **[repo]**
   The author states that the proof was written with Claude Code and that the author
   audited it. **[author, 2026-11-21]**

5. **Blind informal check: Rethlas.** After the audit, the finished proof text was checked
   by the verification agent of Rethlas (H. Ju et al., arXiv:2604.03789; code at
   `github.com/frenzymath/Rethlas`, commit `887cc46`). That agent runs through the Codex
   command-line tool. There were two runs on 2026-08-18: a check of the whole proof, started
   at 21:21 UTC, and a check of Lemma 2 and its use, started at 21:44 UTC. Both returned the
   verdict "correct", with no critical error and no gap. The manifests of the runs record
   Codex CLI 0.146.0, the model identifier `gpt-5.6-sol` and reasoning effort `max`. The
   agent was given the statement, the proof and the text of Cheng and Lin's paper; a patch
   to its instructions forbade web search and any look at this repository. The proof text
   it received has SHA-256
   `12bf8f523b7c1d57a7fd8cafa68e8487452933d6376fa5360598997f8b348b7b`, which is the digest
   of `PROOF_CONJECTURE_3_30.md` at commit `d3fb1f6`. The runs fall after `d3fb1f6` and
   before `e0e64a3`. This is an LLM review, not a proof assistant. Only the verification
   agent of Rethlas was used: Rethlas did not generate the proof, did not produce the peel-2
   experiments and did not perform the audit of step 4.
   **[author; local files outside this repository; the digest can be checked in this
   repository]**

6. **Formal certification: Lean 4.** Commit `131daca` (2026-08-21) machine-checks the
   combinatorial core; see `LEAN_CORRESPONDENCE.md` and `RELEASE_CHECKS.md`. **[repo]**

### Candidate versus the proved certificate

Compared: the candidate as confirmed by the author and as recorded in `RESEARCH_NOTES.md`
§9; the certificate of `PROOF_CONJECTURE_3_30.md` §3 at `d3fb1f6`; the generator
`src/explicit_certificate.py` at `d3fb1f6`; the Lean definitions `indN`, `indFL`, `indFR`,
`F` in `lean/ChowCone/Flow.lean`.

| aspect | candidate | proved certificate (`d3fb1f6`) | Lean |
|---|---|---|---|
| potential | $G(\mathbf n)=U_J\prod_i(n_i-1)$ | same | `G`, with `w_eq_U_mul_a` |
| nonfinal block $n_i\ge4$ | left peel $n_i\to(2,n_i-2)$, flow $G(\text{child})$ | move (N), same | `indN`: `i+1 < length`, `p = 2`, `4 ≤ c_i` |
| final block $n_r\ge4$ | both peels, flow $G(\text{child})$ each | moves (FL) $n_r\to(2,n_r-2)$ and (FR) $n_r\to(n_r-2,2)$ | `indFL` (`p = 2`), `indFR` (`p = c_i − 2`) |
| final block $n_r=4$ | the two moves are the same cover edge $4\to(2,2)$; edge weight $2\,G(\text{child})$ | same: (FL) and (FR) coincide and the flow is $2\,G(\text{child})$ | `F = (indN + indFL + indFR) · G(child)`: both indicators fire, giving `2·G` |
| blocks of size 2 or 3 | no outgoing flow | no selected move | all indicators require `4 ≤ c_i` |

Findings:

* **The proved certificate is the candidate, unchanged.** The audit of 2026-08-18 made no
  correction to the formula. The final-block multiplicity was part of the original
  candidate; the audit recorded it explicitly (commit `d3fb1f6`, items D and H) and proved
  that it is forced: with $G$ instead of $2G$ on the edge $4\to(2,2)$ the divergence
  identity fails at the child, which has two $2$-blocks at positions $r-1,r$.
* **No change between `d3fb1f6` and the final proof.** `e0e64a3` adds two paragraphs to the
  proof of Lemma 2 (distinct children, no edge aliasing) and a test file; the certificate
  definition is untouched. The Lean definitions agree with it clause by clause.
* The asymmetry between nonfinal blocks (left peel only) and the final block (both peels) is
  consistent with the experiments: `peel2_left` alone is infeasible from $d=3$.

## Part 2. The `k = 4` certificate

The proof in `PROOF_K4_FOURTH_MOMENT.md` has two constructive steps. Their origins are
recorded separately.

* **Step 1, the signed initial flow.** For $d\ge3$ the flow
  $(30V(\mathrm{child})+30N-12)F_2+72F_3-48F_4$ has divergence $w^{(4)}$ (§2 of the proof:
  Lemmas 1 and 2, Proposition 3). It is not yet a certificate, because the $F_4$ term is
  negative.
* **Step 2, the removal of the negative terms.** Every negative $F_4$ move is cancelled by a
  zero-divergence path square, and for a final-right move the remaining debt is passed down
  a cascade of further squares (§3). Nonnegativity then rests on the collision bounds $25/16$
  and $79/65$ and on the capacity margins (§4: Lemmas 4 and 5).

### Summary

| | Was it in the author's input? | Who derived it | First readable record (UTC, 28 August 2026) |
|---|---|---|---|
| Step 1 | The approach, yes: the prompt named the two method families that lead to it, in a passage drafted by ChatGPT. The formula, no. | Two sub-agents of the coding agent, one by each route. Neither had received anything from the other. | 21:40:32–21:40:42, the primitive divergences in a command; 21:45:25, the complete identity |
| Step 2 | No. | The agents of the same session, no later than 21:50:46; at 21:45:25 one of them still stated it as an open problem. **The surviving readable records do not determine which agent proposed it first.** | 21:50:46, the name of a task; 21:52:21, a description; 21:52:47, the implementation |

### The session, and what its logs show **[log]**

Both steps were found in one session of OpenAI's Codex command-line agent (version 0.146.0;
the session settings record the model identifier `gpt-5.6-sol` and reasoning effort `ultra`),
which the author ran in the private repository. The session began on 24 August 2026. The
turn that produced the certificate ran from 21:36:51 to 22:14:40 UTC on 28 August, the
evening of that day in the author's time zone (UTC−4). In that turn the session consisted of
a main agent and three sub-agents with the task names `lift_basis`, `lift_membership` and
`lift_tests`. All times below are UTC.

The logs keep in clear the author's prompts, every command the agents ran together with its
output, the agents' progress notes and their final answers. They keep in encrypted form the
agents' intermediate reasoning and most messages passed between agents. Nothing encrypted was
read or decrypted for this file. Each encrypted item carries its creation time in an
unencrypted header. Those times date the items in the sub-agents' logs, whose own line
timestamps are not usable; "between" means bracketed by two such headers.

No session record of another coding tool was found on the machine for this repository in
these days.

### What the author's prompt contained **[log]**

The turn was started by one prompt of the author, entered at 21:36:51. It asked for a
checkpoint commit and for an exact decision on the shared degree-5 system for $d\le11$, set
five proof obligations for any $k=4$ argument, and listed five "Proof-directed alternative
methods". Three of them matter here:

* "Method A — Primitive divergence identities": decompose
  $w^{(4)}(c)=G(c)\,(15V(c)^2-6Q_2(c)-12V(c)-B_d)$ into natural summands and look for
  "separate nonnegative or controllably signed flows" whose divergences realize the
  components.
* "Method B — Lift and correct the k=2 flow": multiply or pair the proved $k=2$ flow with
  state statistics, "compute the exact product-rule correction", and prove the remaining
  correction "by a smaller auxiliary flow".
* "Method C — Recursive shell/peeling construction", using the peel-width-three structure
  seen in the earlier computations.

The prompt contains no formula for a flow. It has neither the signed flow of Step 1, nor the
primitives $F_3$, $F_4$ or their divergences, nor a path square, a cascade or a bound. The
same is true of every earlier prompt of the session and of the agent's other session logs on
the machine, which were searched for these terms. The author's only other inputs that night
were "Continue" at 01:23:27 on 29 August, after the connection had dropped at 22:14:40, and
the instruction to freeze and commit at 02:13:49.

The logs do not show how the prompt itself was drafted. The author states it: on 28 August
the author asked ChatGPT how to continue the search for a proof; at 21:36:07 ChatGPT drafted
the supplementary passage that contains Method A and Method B; at 21:36:51 the author
submitted the prompt containing that passage to the Codex command-line tool. **[author]**
So the two method families that lead to Step 1 were suggested by ChatGPT, and the formulas
were derived by the Codex agents.

### Step 1: the signed initial flow **[log]**

Step 1 was derived inside the session, twice, along the two routes the prompt had named.

1. **`lift_membership`**, whose final answer is headed "Method A". Its turn began at
   21:37:26. Between 21:40:32 and 21:40:42 it issued a command containing the polynomials
   $n(n-3)/2$, $n(n-2)(n-4)/3$ and $n(n-2)(n-3)(n-5)/8$, which are the $\tau_2,\tau_3,\tau_4$
   of Lemma 1, and an ansatz expressing $v^2-9v$, $v=n(n-2)$, as a combination of them, which
   is identity (1) of the proof for a single block. The command failed because a library was
   missing, and the agent ran no other computation in that turn. It reported to the main
   agent at 21:44:20 in a message that is encrypted. Its final answer of 21:58:06 states the
   identity in the form used in the proof.
2. **`lift_tests`.** Its turn began at 21:37:31. Its commands show it reading the proved
   $k=2$ flow and its Lean formalization, and searching the repository for an existing
   product rule. Its final answer, completed at 21:45:25, multiplies the $k=2$ flow by
   $P(\mathrm{child})$ with $P=30(V+N)-24$, computes the product-rule residual
   $\psi=12\rho+72\sigma_3-48\sigma_4$, and concludes that
   $(P(\mathrm{child})+12)F_2+72F_3-48F_4$ "has exactly the desired divergence" for $d\ge3$.
   This is the flow of Step 1, and the earliest complete statement of it that can be read.
   The same answer says that the negative term "blocks a uniform certificate" and names the
   next problem: a "dimension-stable rerouting" of the $-48F_4$ divergence through edges of
   peel width at most 3.

Before both had reported, neither sub-agent had received anything from the other. Apart from
its task, each received one message from the main agent before 21:45 (at 21:43:32 and
21:43:35; contents encrypted). The command of `lift_membership` quoted above precedes it, and
when the main agent wrote to `lift_tests` it had not yet heard from `lift_membership`. The
main agent later called the two results "two independent derivations" (21:52:21). The proof
keeps both: Lemma 1 is the statement about primitive divergences and Lemma 2 is the discrete
product rule. **[repo]**

### Step 2: path squares and the final-right cascade **[log]**

Step 2 appeared in the same session a few minutes later. No input of the author intervened.
The readable sequence is:

| time | agent | event |
|---|---|---|
| 21:45:25 | `lift_tests` | poses the rerouting problem (above), without a solution |
| 21:47:09–21:50:17 | main | its commands are environment checks and exact computations on the linear system of the degree-5 family |
| 21:50:06 | `lift_membership` | sends the main agent a message; encrypted; logged by the main agent at 21:50:17 |
| 21:50:23, 21:50:32 | main | assigns new tasks to `lift_basis` and to `lift_tests`; encrypted |
| 21:50:26 | `lift_basis` | three seconds into the new task, writes to `lift_membership`; encrypted |
| 21:50:46 | `lift_tests` | tries to start a helper with the task name `derive_cascade`; refused, agent limit reached. **Earliest readable trace of Step 2** |
| 21:51:36 | `lift_membership` | replies to `lift_basis`; encrypted |
| between 21:52:05 and 21:52:21 | `lift_tests` | notes that it has "reconstructed the two path-difference circulations" and describes the cascade, which ends on a left-2 edge at $x=2$ or a peel-3 edge at $x=3$ |
| between 21:52:10 and 21:52:31 | `lift_basis` | notes "I now have the precise rule" and tests it "at raw-flow level, including coincident final splits and every cascade collision" |
| 21:52:21 | main | "A stronger route has emerged from two independent derivations: an exact all-d signed identity, followed by deterministic path-square rerouting of every negative peel-4 term into peel-2/3 edges." |
| 21:52:47 | main | writes `src/k4_uniform_certificate.py`: the signed flow, the left path square, the final-right square with its cascade, and the correction at $d=2$ |
| 21:52:51 | main | exact check for $d=1,\dots,11$: the divergence matches and no edge is negative |
| 21:54:16 | `lift_tests` | final answer: a separate in-memory implementation agrees for $d=3,\dots,11$ and finds that $d=2$ needs the extra raw flow 72, which the main agent's code already has |
| 21:58:06 | `lift_membership` | final answer: "Method A produced an exact uniform mechanism"; it describes the "path-difference diamonds", the right-2 debt that cascades down, and collision sums at most $25/16$ and below $5/4$ at the $F_3$ terminal. **Earliest readable statement of the bound** |
| 21:59:39 | `lift_basis` | final answer: "Method C audit passed" for $d=1,\dots,11$; it warns that each cascade step must update the prefix |
| 21:59:40 | main | writes the first version of `PROOF_K4_FOURTH_MOMENT.md`, with the bounds $25/16$ and $79/65$ |
| 22:03:33 | main | progress note stating the bound and the positive margins |
| 22:14:40 | | the turn ends: the connection to the model was lost |

What this settles: the path squares and the cascade are absent from the author's input, and
they were produced by the agents of this session no later than 21:50:46, when the cascade is
first named. At 21:45:25 `lift_tests` still stated the rerouting as an open problem; whether
another agent already had it then cannot be read.

What it does not settle: which agent proposed them first. The messages that would decide it,
exchanged between 21:50:06 and 21:51:54, are stored encrypted, and so is all reasoning.
**The surviving readable records do not determine which agent first proposed Step 2.** The
order of events is consistent with `lift_membership` having supplied the rule in its message
of 21:50:06. The main agent had been working on the linear system until then; it re-assigned
`lift_basis` six seconds and `lift_tests` fifteen seconds after logging that message;
`lift_basis` turned to `lift_membership` at once and had "the precise rule" after its reply;
and the final answer of `lift_membership` presents the mechanism as the outcome of its
method. This is an inference from the order and routing of the messages. It is not a
readable statement, and it does not exclude that the main agent formulated the rule itself.

### The proof text, the audits inside the session, and the freeze **[log]** **[repo]**

* 21:59:40 on 28 August: first version of `PROOF_K4_FOURTH_MOMENT.md`, 476 lines, written by
  the main agent.
* 01:23:27 on 29 August: the author's "Continue". The main agent regenerated the stored
  results and ran the tests.
* 01:27:23–01:31:39: `lift_tests` and `lift_membership`, the latter with a helper named
  `proof_adversary`, audited the proof text and answered "No concrete error found" and "No
  substantive mathematical gap found", each with a list of corrections to the wording. The
  main agent applied them between 01:32:42 and 01:36:29.
* 01:37:12: the main agent's final report, which begins "A genuine all-d symbolic k=4
  certificate was found."
* 02:13:49: the author's instruction to freeze and commit without a further review.
  02:16:44: the commit `Prove the uniform k=4 fourth-moment certificate` (private `c92951f`,
  here `27248b9`), with the proof at 529 lines.

The audits of 01:27–01:31 were made by the same model, in the same session, by agents that
had taken part in the construction. They are not independent reviews. The reviews made in
November 2026 are described in `RELEASE_CHECKS.md`.

### First implementation versus the frozen certificate **[log]** **[repo]**

The construction was not revised after it was first written down. The functions that define
the flow in `src/k4_uniform_certificate.py` (`primitive_moves`, `_signed_primitive_flow`,
`_left_peel4_correction`, `_final_right_peel4_correction`, `candidate_flow`,
`verify_candidate_flow`) are the same, line for line, in the version written at 21:52:47 on
28 August and in the frozen commit. The commit only adds the code that writes
`results/k4_uniform_certificate/verification.json`. Neither that file nor the proof text has
changed since the frozen commit.

### The author's own record **[author]**

According to the author, the author's ChatGPT conversation of that night has the terminal
output with the collision bound at 01:20 UTC on 29 August and the report with the
all-dimensional construction at 01:46 UTC. The session logs place the production of both
earlier: the bound between 21:58:01 and 22:03:33 on 28 August, the report at 01:37:12 on
29 August. The two records agree if the author's times are those at which the material
reached that conversation. The conversation was not read for this file.

### Open points

* Which agent first proposed Step 2, in particular the cascade. This cannot be settled from
  the logs as they are stored.

### The reviews of November 2026 **[author]** **[repo]**

* 20 November: audit of the proof and of the step from the certificate to matroids, made
  with Claude (Anthropic).
* 21 November: a review pack produced in a separate OpenAI Codex session (ChatGPT Work
  Mode); the model version was not verified. It is called independent in this repository in
  one sense only: its checking program was implemented separately, and the two sets of
  witnesses were verified against each other's checker.

Details and results are in `RELEASE_CHECKS.md`.

## Part 3. The texts

**[log]** for the dates, **[repo]** for the commits. Times are UTC.

* `K4_MATROID_BRIDGE.md` and `K2_K4_PAPER_OUTLINE.md` were written by the main agent of the
  Codex session of Part 2 at 02:28 on 29 August 2026, after the author's instruction of
  02:24 (commit `Lift the k=4 certificate to Cheng–Lin's matroid theorem`).
* The first version of `CHOW_CONE_FLOWS_MANUSCRIPT.tex` was written by the same agent at
  02:44 on 29 August and frozen at 03:03 (commit `Add referee-facing k2-k4 Chow cone
  manuscript`).
* On 1 September 2026 a second Codex session (version 0.152.0, model identifier
  `gpt-5.6-sol`) revised the abstract and the introduction only, under two prompts of the
  author that restricted it to those parts (commit `Polish the referee-facing Chow cone
  manuscript`).
* In November 2026 Section 11, the reproducibility paragraph of Section 12, the five edits
  proposed by the review of 2026-11-21, the two closing sentences of the abstract, the
  sentence that cites Bérczi, Coron, Eur and Li, and a first draft of the section "Use of AI
  tools" were written with Claude Code.
* On 2026-11-21 the author edited the manuscript outside the repository and returned it. The
  author's changes are: the author line, with an address and an e-mail line; an empty date;
  a rewording of the two paragraphs around Table 1 in Section 8; and the final text of the
  section "Use of AI tools". In that section the sentence on Rethlas and its reference were
  supplied by Claude Code at the author's request. The rewording of Section 8 replaced a
  sentence, written with Claude Code earlier that day, which was wrong for $y=4$; see
  `RELEASE_CHECKS.md`.
  **[repo: the file returned by the author, compared line by line with the version sent]**

* On 2026-11-22, after the Lean formalization of Part 4, five passages of the manuscript
  were changed with Claude Code at the author's request: one sentence of the abstract; the
  paragraph on Lean in Section 12; the name of the release in Section 12; one sentence added
  to the paragraph on Theorem 1.2 in the section "Use of AI tools"; and the last sentence of
  the paragraph "Review" in that section. The wording of all five is by Claude Code,
  including the two sentences in the section "Use of AI tools". The author asked for the
  changes to be applied to the file and received the changed file.
  **[repo: the manuscript at `v1.0` compared with `v1.1`]** **[session]**

Apart from the author's changes of 2026-11-21, the text of the manuscript was drafted by AI
systems under the author's direction. The rewording of Section 8 is the author's own.
**[author, 2026-11-21]**

## Part 4. The Lean formalization of the `k = 4` certificate

**[repo]** for the files and the commits, **[session]** for how the work proceeded. Times
are UTC.

* **What it is.** Nine Lean modules in `lean/ChowCone/K4/`, the axiom report
  `lean/K4AxiomCheck.lean` with its output `lean/K4AxiomCheck.txt`, and
  `K4_LEAN_CORRESPONDENCE.md`. They formalize the combinatorial core of the proof of Part 2
  as it stands in Sections 6 to 9 of the manuscript of 21 November 2026, with Cheng and
  Lin's Lemma 3.29 as a hypothesis. **[repo: the commits after `v1.0` whose messages begin
  "Lean, k = 4" or "K4 correspondence"]**
* **Who wrote it.** The definitions, the statements, the proofs and the correspondence table
  were written by Claude Code (Anthropic) in one working session on the author's machine,
  between 23:46 on 21 November 2026, when the brief arrived, and 03:20 on 22 November, the
  time of the last of those commits. The commits carry `Co-Authored-By` trailers for that
  reason. The author wrote no Lean code. **[session]** **[repo: the commit times]**
* **What the author supplied.** A written brief for the first step, the origins and
  multiplicities of the charges of rows 4 to 6 of Table 1. The brief fixed the notion of a
  source, the forward construction and the statement to be proved, listed four test cases,
  and set the conditions of acceptance: no `sorry`, no custom axiom, no `native_decide`, and
  no use of the enumeration as a hypothesis. How the brief was drafted is not known to the
  assistant. The later steps were proposed by the assistant, each after the previous one
  was finished: the sizes of the charges, rows 1 to 3, the signed flow, the rerouting,
  nonnegativity, Theorem 9.1 and the certificate. The author approved each continuation in
  a short message. **[session]**
* **What it used.** The manuscript and the `k = 2` Lean files of this repository. The proof
  document `PROOF_K4_FOURTH_MOMENT.md` and the implementation
  `src/k4_uniform_certificate.py` were not used. No web search and no other AI system was
  used. **[session]**
* **Where it departs from the text.** The estimates of Section 8 are made edge by edge, with
  indicator functions for the occurrences on an edge, and not occurrence by occurrence. The
  list of origins of a label is proved from a forward construction defined by recursion, as
  the brief required. The hypothesis `d ≥ 3` turned out not to be needed in two statements
  (the origins of rows 4 to 6, and nonnegativity). A numerical test value written by the
  assistant, `r_2 = 1/36` for `y = 2`, was wrong and was rejected by Lean; the file has the
  correct value `1/18`. **[session]** **[repo: `K4_LEAN_CORRESPONDENCE.md`]**
* **What was checked, and by whom.** Lean checked every proof, and the axiom report lists
  155 declarations on the three standard axioms or a subset of them. The agreement of the
  Lean definitions with the manuscript was checked only by the assistant that wrote them.
  The assistant also computed the flow for `N = 6` by hand and found it in agreement with
  the divergence identity; that computation is not in the repository. No review of the
  formalization by a person or by a second AI system is recorded. **[session]**
  **[repo: `RELEASE_CHECKS.md`]**

## What this attribution does not claim

It describes how the results were found within this project. It does not assert that the
certificates, or the identities behind them, are absent from the literature, and it does not
replace a priority check.

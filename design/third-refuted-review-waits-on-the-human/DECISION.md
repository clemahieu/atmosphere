---
title: "A repeated refutation asks the human one question per undecided point from the third review (and at the second for an undecided design or a closed claim), and files a gate check when the same kind repeats"
date: 2026-11-15
status: active
tags: [process, skeptic, tracker, gate]
one_line: "A round that triages a refuting review counts the epic's refuted reviews and, from the second, writes down the kind of refutation and whether it repeats the previous pass. When the same kind repeats, it either files a tool issue for a gate check across the tree (blocking the refutation's leaves whose instances the check would find) or records why the class cannot be checked mechanically. From the third, and at the second when the kind is undesigned or a closed claim, it files one question to the human for each point it can name, each about that point alone; a leaf waits on the questions whose answer could change it, and the repeat review on all of them. A leaf filed for a refutation is not split into an epic that needs its own review without asking the same way."
revisit_if: "Most answers keep what the tree does, counted over the questions filed under this rule; or an epic still reaches a fifth refuted review; or the questions filed at a second refutation are mostly ones the next pass would have closed anyway; or leaves that waited on no question are regularly rewritten after the answers; or the checks filed this way mostly catch nothing after their first run."
confidence: "The thresholds are a judgement from the history measured below. That a repeated refutation marks something a pass cannot close is what the history shows. That the round can name the point is shown by three of the four questions first asked under this rule, which listed their points. That it names the kind early is weaker: at the second refutation it did so in one of those three. That tree-wide gate checks contain repeated proof and contract classes is shown by three prior classes measured below."
---

## Decision

A round that triages a refuting review counts the reviews of that epic that closed refuted before it. Which closings count is `design/review-is-a-leaf-of-its-epic/`'s.

From the second refuted review, the round writes an assessment into the epic's notes and one line into the round's notifications. The assessment says which criterion each pass refuted and its kind, whether the leaves that answered them added state, an operation or an obligation of the glue to the model or only proof, which kind this refutation is, and whether it repeats the kind the previous pass refuted:

- **Undesigned.** The leaves decided something no record here decides. The round names the part of a kernel it is, what any kernel has to decide about that part, which record decides each point or that none does, and the usual answers, from general knowledge and under the License principle.
- **Closed claim.** The criterion says nothing else can do something, or that a list is exact, and each pass finds one more case.
- **Stale criterion.** The tree is right and the criterion's wording is behind it.
- **From below.** A specification that does not say when it refuses, or a witness that does not start from what boot ensures.

From the second refuted review, when the assessment names the same kind the previous pass refuted, the round also decides the check for that class:

- When the class can be checked mechanically across the tree, it checks whether an open tool issue or an existing gate step already covers it. When no open tool issue covers it, the round files a tool issue for a gate check that finds every instance of that class across the tree (or widens an existing gate check that covers part of the tree or missed this shape), and blocks every leaf of the refutation whose instances the check would find on that tool issue, so all instances are found and fixed together and guarded against later regressions.
- When the class cannot be checked mechanically—an undecided design with no decided rule to enforce, or a closed claim whose boundary is not yet settled—the round writes that reason in the assessment instead of filing a check.

At the second refuted review the round asks the human when the kind is undesigned or a closed claim. Otherwise no human question waits: the leaves (still waiting on any gate-check issue filed above) and the repeat review go ahead. From the third it asks whatever the kind.

Asking is one question for each point the assessment leaves to the human, each about that point alone:

- An undecided point of the design. The question says what the tree does today and where that was set, the options, one of them to keep it, what each implies for the leaves, and the usual answer.
- A criterion's wording, when the criterion is stale or does not name the measure the passes judged it by. The question is the wording proposed, to take or to leave.
- When the round can name no point, which only a refutation from below that keeps repeating leaves, one question that says so and asks whether to go on.

A leaf filed for the pass waits on the questions whose answer could change it, and on none when it is the same under every option. The repeat review waits on every question, so no further pass runs until the answers. The loop goes on with other work. What the triage found that is not the epic's to decide, a rule of the process or another epic's design, is its own issue where it belongs and no part of the questions.

A leaf filed for a refutation carries the label `refuted`. When a round would split one into more than three pieces, so into an epic that needs a review of its own, it asks the same way instead and the leaf waits on the questions.

`.claude/agents/round.md`, section 6, is the procedure.

## Context

A review that refutes files a leaf per refuted criterion and a repeat review, `design/review-is-a-leaf-of-its-epic/`. Nothing bounded that: a leaf has two proof attempts before the human is asked, and a review had no count at all. The skeptic's report is an issue description a round files verbatim, so a pass could go on choosing what the model gains, one refutation at a time, with nobody asked whether the thing being patched had been designed.

It happened. The record of how a dead process is torn down came to hold, in one paragraph revised by six leaves, the whole of how a core's page-table base register is modelled: what it names when it names no space, under which tag, who writes it at boot. No record decided any of it beforehand: each point was a refutation first.

The same loop happened inside `from below`, where no design was missing. Three consecutive passes refuted the caller's-view contracts in `kernel/verified/capability/caller.rs` on one class—a contract arm met by an unexpected refusal or by a call changing nothing—one or two arms per pass, because each leaf fixed only the arm named while nothing checked the rest of the file or the rest of the tree. Without a gate check, fixing the named arm also leaves every future proof attempt free to weaken another `ensures` to make a proof verify.

## Reasoning

Measured on 2026-11-12 from one `bd list --all --json`. A pass is a review, refuting when its close reason starts `refuted`; before reviews existed a pass is a `Skeptic report` note on the epic, read for its verdict, the repeats checked by hand. Tokens are the output column of the `totals` table `tools/token-ledger.py` writes, summed over each epic and everything below it.

- 63 epics were judged in 110 passes, 53 of them refuting.
- By the number of refuting passes an epic took: none 35, one 18, two 5, three 2, four 1, six 1, nine 1.
- Each of the 10 epics refuted twice or more had one criterion refuted on consecutive passes. So counting refuted reviews finds the same epics as matching criteria would, and needs no judgement of whether two refutations are of the same criterion.
- Of the 5 refuted exactly twice, 4 closed on the next pass and 1 is open. So a wait at the second would have asked the human ten times, four of them for nothing.
- The 5 refuted three times or more hold 25 of the 53 refuting passes and 5.1M of the 41M output tokens. A wait at the third would have asked five times.
- The three longest are of one subject, a ghost token that stands for hardware: a core's base register (9 and 4, one nested in the other) and an IOMMU's command ring (6). The repeating criteria there were closed claims, that a token cannot be made elsewhere or that the exempt leaves are exactly those named.
- The criteria that repeated two or three times and then closed were mostly from below: a refusal condition, a witness from boot.
- Three nested epics, each a leaf filed for a refutation that then split and needed its own review, hold 15 of the 53. The inner epics' criteria were the skeptic's own text, which the next pass then judged.

The kinds come from reading those ten. They matter because the answers differ: a stale criterion wants a reword, a refusal condition wants more proof and no decision, and only the first two kinds want the human.

Measured on 2026-11-15, from the four questions this rule had asked while it asked one question at the third refuted review, with three options: go on, reword the criterion, or decide the design first. Read from the questions and from the notes of their epics.

- Three held something to decide. The fourth held nothing: its kind was from below, its own text said no design was undecided, and the proof leaf that waited on it was the same under every option.
- Each of the three named what was undecided inside the option to decide the design first: three points in one; one point with three usual answers in another; and in the third one point, the same point again as a contradiction in its record, and a rule of the process that was not the epic's.
- Two had been answered. One answer reworded the criterion to name its boundary. The other was none of the three options: it made each of the question's three points an issue of its own, one of them a question to the human.
- At the second refutation the assessment had named a closed claim in one of the three, saying it would close only on a decided boundary; the leaves went ahead, and the third pass found the next case. In the other two it had read the second refutation as from below. So asking at the second by kind would have saved a pass and two leaves once in three. It costs nothing when the kind reads otherwise, since the third asks whatever the kind.

A question is answered as a whole, so a question holding three points is answered only by first taking it apart, and the round that wrote the assessment has the points in front of it. The repeat review waits on every question because the passes are what a repeated refutation spends. A leaf waits only on what could change it: a proof that is the same under every answer gains nothing by waiting. The round judges which leaves those are, and one it lets go wrongly costs that leaf and not a pass.

The round writes the assessment and not the skeptic. The skeptic has no context on purpose and judges evidence; whether a design exists is a question about the records and about the epic's history, which the triaging round has in front of it.

Measured on 2026-11-15 from the three refuting passes on the caller's-view contracts (`kernel/verified/capability/caller.rs`):

- Pass 1 (`main 3c93fbb2`) refuted `revoke_contract`'s epoch-refused arm (admitting refusal from any epoch); one leaf fixed it.
- Pass 2 (`main 36ba7cc8`) refuted `revoke_contract`'s `again` arm and `retype_contract`'s `2M` and `free` `again` arms (each met by an unchanged state); two leaves fixed those arms, and the second assessment read the refutation as `from below`, so no human question waited and nothing checked the remaining arms across the tree.
- Pass 3 (`main f434769d`) refuted `retype_contract`'s `free` `ok` arm (met by a free that freed nothing) and its `again` arms (dropping the repeat's allowance).
- All three passes attacked one class (`from below`, an arm weaker than its specification), while `tools/check-refused.py` already existed in the tree (`awire/src/refused/`) without running on `kernel/verified`. Earlier repeated classes—dropped `ensures` fields across `invoked`'s arms (`design/invoked-arm-is-the-operation-postcondition/`, `tools/check-invoked-arms.py`) and uncounted calls or conjured values across the boundary into verified code (`design/boundary-into-verified-code-counted/`, `tools/check-boundary.py`)—were each contained once a gate step checked the whole tree, and `design/refused-claim-per-way/` sets the claim forms for the operation inventory.

When the second refuted review names the same kind the previous pass refuted, the pattern has already recurred once, and `from below` asks no human question there. Filing a gate-check tool issue then—and blocking the refutation's leaves whose instances the check would find—puts the tree-wide check in place before the leaves run, so every instance is found and fixed together and stays guarded against later regressions. Explaining in the assessment when no mechanical check fits keeps undecided designs and closed claims whose boundary is not yet set (though once set as a list or rule, as in `tools/boundary-list`, a gate check can hold it) from generating checks that cannot be written.

## Alternatives rejected

- **Wait at the second refutation, whatever the kind.** Four of the ten closed on the next pass; see the measurement.
- **Count a criterion, not an epic.** The two agree on every epic in the history, and a criterion's number moves when the criteria are reworded.
- **Report only, never wait.** The longest runs cost the most after the third pass, and a note nobody has to answer does not stop the leaves that patch around a missing decision.
- **Have the skeptic say whether the design exists.** It would need the epic's history and the records' intent, which is the context it is run without.
- **A token budget per epic.** Nothing measured predicts what a pass or an epic costs, `design/review-is-a-leaf-of-its-epic/`, so a budget would stop sound work as readily as a spin.
- **Count in `tools/reviews.py`.** The count is one query at the moment of triage, and the tool lists finished epics, which an epic being triaged is not.
- **One question with the courses as its options: go on, reword the criterion, or decide the design first.** The points to decide sat inside the third option, so the question had to be split before it could be answered, and a matter that was not the epic's rode along with it; see the measurement.
- **Have the round split an undesigned epic at its second refutation, moving the refuted part of its criterion into a sibling epic.** The round would reword one epic's criterion and write another's with no one asked, on a kind it read at the second refutation once in three. The questions make the same cut, and the answers decide what moves.
- **Fix every sibling instance by hand in the refutation's leaf without a gate check.** Leaves later commits—including a proof attempt that weakens an `ensures` so it verifies—free to reintroduce the class, and misses instances outside the leaf's file.
- **File the gate check only from the third refuted review.** A class repeated at the second refutation has already appeared twice, and `from below` waits on no human question at the second, so waiting until the third spends another pass and narrow leaf.
- **File the gate check without blocking the refutation's leaves.** The leaves run first, fix only the named instances, and close before the check exists to catch the rest.
- **Require a gate check for every repeated kind without exception.** An undecided design or an unbounded closed claim has no rule to check until the human decides it.

## What this does not settle

- Passes recorded as notes before reviews existed are not counted, so an epic with such passes reaches the wait later than its history says.
- The kind is the round's judgement. Nothing checks it but the human reading the question.
- Whether the split of a large epic should ask what its subsystem has to decide before any leaf is written, which would catch an undesigned part before the first pass rather than at the third.
- Which leaves an answer could change is the round's judgement, as the kind is. The repeat review waits whatever it judges.
- Whether a repeated class can be checked mechanically, and which leaves its check would find, is the triaging round's judgement, as the kind is.
- Whether a gate check already in `tools/` covers a newly refuted shape or needs an issue to widen it is decided when the round searches existing checks.

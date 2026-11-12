---
title: "An epic's third refuted review waits on the human; its second is only reported"
date: 2026-11-12
status: active
tags: [process, skeptic, tracker]
one_line: "A round that triages a refuting review counts the epic's refuted reviews: the second is reported to the human with the kind of refutation it is and nothing waits; from the third, the leaves it files wait on a question that asks whether to go on, reword the criterion or decide the design first; a leaf filed for a refutation is not split into an epic that needs its own review without the same question."
revisit_if: "Most of the questions are answered `go on`, counted as questions titled `has been refuted` whose answer is that against those answered otherwise; or an epic still reaches a fifth refuted review; or the second refutation's report is never acted on, so it could be dropped or made to wait."
confidence: "The thresholds are a judgement from eight days of history, measured below. That a repeated refutation marks something a pass cannot close is what the history shows; that the human's look is cheaper than the passes it stops is a bet the first questions will settle."
---

## Decision

A round that triages a refuting review counts the reviews of that epic that closed refuted before it.

The second refuted review is reported and nothing waits: the round writes an assessment into the epic's notes and one line into the round's notifications, and the leaves and the repeat review go ahead.

From the third, the round files a question to the human under the epic, and each leaf it filed for that pass waits on it. The repeat review waits on those leaves, so no further pass runs until the answer. The loop goes on with other work.

A leaf filed for a refutation carries the label `refuted`. When a round would split one into more than three pieces, so into an epic that needs a review of its own, it files the same question instead and the leaf waits on it.

The assessment says which criterion each pass refuted, whether the leaves that answered them added state, an operation or an obligation of the glue to the model or only proof, and which kind the refutation is:

- **Undesigned.** The leaves decided something no record here decides. The round names the part of a kernel it is, what any kernel has to decide about that part, which record decides each point or that none does, and the usual answers, from general knowledge and under the License principle.
- **Closed claim.** The criterion says nothing else can do something, or that a list is exact, and each pass finds one more case.
- **Stale criterion.** The tree is right and the wording is behind it.
- **From below.** A specification that does not say when it refuses, or a witness that does not start from what boot ensures.

The question's options are to go on, to reword the criterion, or to decide the design first. `.claude/agents/round.md`, section 6, is the procedure.

## Context

A review that refutes files a leaf per refuted criterion and a repeat review, `design/review-is-a-leaf-of-its-epic/`. Nothing bounded that: a leaf has two proof attempts before the human is asked, and a review had no count at all. The skeptic's report is an issue description a round files verbatim, so a pass could go on choosing what the model gains, one refutation at a time, with nobody asked whether the thing being patched had been designed.

It happened. The record of how a dead process is torn down came to hold, in one paragraph revised by six leaves, the whole of how a core's page-table base register is modelled: what it names when it names no space, under which tag, who writes it at boot. No record decided any of it beforehand: each point was a refutation first.

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

The round writes the assessment and not the skeptic. The skeptic has no context on purpose and judges evidence; whether a design exists is a question about the records and about the epic's history, which the triaging round has in front of it.

## Alternatives rejected

- **Wait at the second refutation.** Four of the ten closed on the next pass; see the measurement.
- **Count a criterion, not an epic.** The two agree on every epic in the history, and a criterion's number moves when the criteria are reworded.
- **Report only, never wait.** The longest runs cost the most after the third pass, and a note nobody has to answer does not stop the leaves that patch around a missing decision.
- **Have the skeptic say whether the design exists.** It would need the epic's history and the records' intent, which is the context it is run without.
- **A token budget per epic.** Nothing measured predicts what a pass or an epic costs, `design/review-is-a-leaf-of-its-epic/`, so a budget would stop sound work as readily as a spin.
- **Count in `tools/reviews.py`.** The count is one query at the moment of triage, and the tool lists finished epics, which an epic being triaged is not.

## What this does not settle

- Passes recorded as notes before reviews existed are not counted, so an epic with such passes reaches the wait later than its history says.
- The kind is the round's judgement. Nothing checks it but the human reading the question.
- Whether the split of a large epic should ask what its subsystem has to decide before any leaf is written, which would catch an undesigned part before the first pass rather than at the third.

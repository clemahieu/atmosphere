#!/usr/bin/env bash
# SPDX-License-Identifier: MIT

# SessionStart hook: the session is the Beads actor. Claude Code runs CLAUDE_ENV_FILE before every
# Bash call of the session and of its subagents, so bd records claude-<pid> as the assignee of what a
# round claims, and a round tells a finished session's issue from a live one by whether the pid is a
# running process of that name (.claude/agents/round.md, Orient). Both variables are the harness's; a
# missing one is a harness change, not a case to paper over.
#
# Grok loads this hook too and sets GROK_SESSION_ID on every hook it runs. A Grok session has no env
# file and runs no rounds, so the hook writes nothing there.
#
# tools/loop.py runs each round, prover and skeptic as a session of its own and names itself the actor,
# loop-<pid>, in their environment, so what a round hands to the prover stays held between the two
# sessions. The hook keeps an actor the environment already names.
set -u
[ -z "${GROK_SESSION_ID:-}" ] || exit 0
[ -z "${BEADS_ACTOR:-}" ] || exit 0
echo "export BEADS_ACTOR=claude-${CLAUDE_PID:?}" >> "${CLAUDE_ENV_FILE:?}"

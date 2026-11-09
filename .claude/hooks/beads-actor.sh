#!/usr/bin/env bash
# SessionStart hook: the session is the Beads actor. Claude Code runs CLAUDE_ENV_FILE before every
# Bash call of the session and of its subagents, so bd records claude-<pid> as the assignee of what a
# round claims, and a round tells a finished session's issue from a live one by whether the pid is a
# running process of that name (.claude/agents/round.md, Orient). Both variables are the harness's; a
# missing one is a harness change, not a case to paper over.
#
# Grok loads this hook too and sets GROK_SESSION_ID on every hook it runs. A Grok session has no env
# file: its rounds carry grok-<pid> in the loop's prompt (.claude/skills/round/SKILL.md), so the hook
# writes nothing there.
set -u
[ -z "${GROK_SESSION_ID:-}" ] || exit 0
echo "export BEADS_ACTOR=claude-${CLAUDE_PID:?}" >> "${CLAUDE_ENV_FILE:?}"

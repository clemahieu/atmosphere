#!/usr/bin/env bash
# SPDX-License-Identifier: MIT

# SessionStart hook for agy: inject the untracked project-root CLAUDE.md beside
# the worktrees when present, since agy loads AGENTS.md inside the worktree and
# does not walk into the parent directory. ATMO_SESSION_START_ROOT overrides the
# parent directory in tests.
set -u

cat >/dev/null

if [ "${ATMO_SESSION_START_ROOT+set}" = set ]; then
  root=$ATMO_SESSION_START_ROOT
else
  top=$(git rev-parse --show-toplevel 2>/dev/null || true)
  root=${top:+$(dirname "$top")}
fi

if [ -n "$root" ] && [ -f "$root/CLAUDE.md" ]; then
  jq -Rs '{injectSteps:[{systemMessage:{systemMessage:.}}]}' "$root/CLAUDE.md"
else
  printf '{}\n'
fi

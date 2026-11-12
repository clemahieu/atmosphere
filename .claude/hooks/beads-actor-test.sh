#!/usr/bin/env bash
# SPDX-License-Identifier: MIT

# Tests beads-actor.sh with a pid and an env file of its own; the session's values are not touched.
set -u

hook="$(dirname "${BASH_SOURCE[0]}")/beads-actor.sh"
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
fail=0

check() {
  local name=$1 ok=$2
  if [ "$ok" = 0 ]; then echo "ok   $name"; else echo "FAIL $name"; fail=1; fi
}
run() { env -u CLAUDE_PID -u CLAUDE_ENV_FILE -u GROK_SESSION_ID -u BEADS_ACTOR "$@" "$hook" </dev/null >/dev/null 2>&1; }

# The hook names the session's claude process in the file Claude Code runs before every Bash call.
run CLAUDE_PID=4242 CLAUDE_ENV_FILE="$dir/env.sh"; check "exits 0" $?
[ "$(cat "$dir/env.sh" 2>/dev/null)" = "export BEADS_ACTOR=claude-4242" ]; check "one export line" $?
actor=$(BEADS_ACTOR= bash -c "source '$dir/env.sh' && echo \"\$BEADS_ACTOR\"" 2>/dev/null)
[ "$actor" = "claude-4242" ]; check "sourcing sets the actor" $?

# A second run for the same session (resume, clear, compact) appends the same value.
run CLAUDE_PID=4242 CLAUDE_ENV_FILE="$dir/env.sh"
[ "$(sort -u "$dir/env.sh" 2>/dev/null | wc -l)" = 1 ]; check "repeat is idempotent" $?

# Without the harness's variables the hook fails rather than naming a wrong actor.
run CLAUDE_ENV_FILE="$dir/other.sh"; rc=$?
[ "$rc" != 0 ] && [ ! -e "$dir/other.sh" ]; check "no pid is an error" $?
run CLAUDE_PID=4242; rc=$?
[ "$rc" != 0 ]; check "no env file is an error" $?

# A session tools/loop.py runs inherits the loop's actor, which the hook keeps.
run BEADS_ACTOR=loop-77 CLAUDE_PID=4242 CLAUDE_ENV_FILE="$dir/loop.sh"; check "inherited actor exits 0" $?
[ ! -e "$dir/loop.sh" ]; check "inherited actor is kept" $?

# Under Grok, which sets GROK_SESSION_ID on every hook, the session has no env file: the hook accepts
# the missing harness variables and writes nothing.
run GROK_SESSION_ID=abc; check "grok session exits 0" $?
run GROK_SESSION_ID=abc CLAUDE_PID=4242 CLAUDE_ENV_FILE="$dir/grok.sh"
[ ! -e "$dir/grok.sh" ]; check "grok session writes nothing" $?

# agy SessionStart hook injects root CLAUDE.md when present beside the worktree and {} otherwise,
# and AGENTS.md + .agents/hooks.json wire shared rules and hooks for agy.
hooks_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "$hooks_dir/../.." && pwd)"
agy_start="$hooks_dir/agy-session-start.sh"

mkdir -p "$dir/with-rules" "$dir/without-rules"
cat > "$dir/with-rules/CLAUDE.md" <<'EOF'
# Local root rules
Line with "quotes" and $variables.
EOF

out=$(printf '{}' | ATMO_SESSION_START_ROOT="$dir/with-rules" "$agy_start" 2>/dev/null); rc=$?
[ "$rc" = 0 ]; check "agy session-start with CLAUDE.md exits 0" $?
got=$(printf '%s' "$out" | jq -r '.injectSteps[0].systemMessage.systemMessage' 2>/dev/null || printf 'INVALID')
[ "$got" = "$(cat "$dir/with-rules/CLAUDE.md")" ]; check "agy session-start injects CLAUDE.md" $?
printf '%s' "$out" | jq -e --rawfile want "$dir/with-rules/CLAUDE.md" '.injectSteps[0].systemMessage.systemMessage == $want' >/dev/null 2>&1
check "agy session-start preserves exact bytes" $?

out_absent=$(printf '{}' | ATMO_SESSION_START_ROOT="$dir/without-rules" "$agy_start" 2>/dev/null); rc=$?
[ "$rc" = 0 ] && [ "$out_absent" = "{}" ]; check "agy session-start without CLAUDE.md emits {}" $?

out_empty=$(printf '{}' | ATMO_SESSION_START_ROOT="" "$agy_start" 2>/dev/null); rc=$?
[ "$rc" = 0 ] && [ "$out_empty" = "{}" ]; check "agy session-start empty root emits {}" $?

[ -L "$repo/AGENTS.md" ] && [ "$(readlink "$repo/AGENTS.md")" = "CLAUDE.md" ]
check "AGENTS.md symlinks to CLAUDE.md" $?

jq -e '
  .["license-guard"].PreToolUse == [{"matcher":"*","hooks":[{"type":"command","command":"../.claude/hooks/license-guard.sh","timeout":10}]}] and
  .["root-rules"].SessionStart == [{"type":"command","command":"../.claude/hooks/agy-session-start.sh","timeout":10}]
' "$repo/.agents/hooks.json" >/dev/null 2>&1
check ".agents/hooks.json wires grouped PreToolUse and flat SessionStart" $?

# hooks.json runs commands with cwd set to .agents/.
pre_cmd=$(jq -r '.["license-guard"].PreToolUse[0].hooks[0].command' "$repo/.agents/hooks.json")
start_cmd=$(jq -r '.["root-rules"].SessionStart[0].command' "$repo/.agents/hooks.json")
out_pre=$(cd "$repo/.agents" && printf '{"hookEventName":"PreToolUse","toolCall":{"id":"t1","name":"read_file","args":{"Path":"CLAUDE.md"}}}' | sh -c "$pre_cmd" 2>/dev/null); rc=$?
[ "$rc" = 0 ] && [ "$(printf '%s' "$out_pre" | jq -r '.decision')" = "allow" ]
check ".agents/hooks.json PreToolUse command resolves from .agents/" $?
out_start=$(cd "$repo/.agents" && printf '{}' | ATMO_SESSION_START_ROOT="$dir/without-rules" sh -c "$start_cmd" 2>/dev/null); rc=$?
[ "$rc" = 0 ] && [ "$out_start" = "{}" ]
check ".agents/hooks.json SessionStart command resolves from .agents/" $?

exit $fail

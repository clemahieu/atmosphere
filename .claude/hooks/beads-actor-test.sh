#!/usr/bin/env bash
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
run() { env -u CLAUDE_PID -u CLAUDE_ENV_FILE "$@" "$hook" </dev/null >/dev/null 2>&1; }

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

exit $fail

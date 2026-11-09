#!/usr/bin/env bash
# Tests license-guard.sh by piping tool calls to it as strings; nothing is opened. The forbidden
# names are assembled from parts so that editing this file does not trip the guard it tests.
# ATMO_LICENSE_GUARD_LOCAL supplies the temporary local list.
set -u

guard="$(dirname "${BASH_SOURCE[0]}")/license-guard.sh"
tree="sel4$(printf .src)"
dir="sel4$(printf .gpl)"
sys=/usr/src
host="elixir$(printf .bootlin.com)"
parent_dir="/tmp/atmo-lg-parent"
fake="atmo-lg-root$(printf .marker)"
# Home spellings are assembled so this file does not contain them. The guard's normalisation joins them.
tilde_slash=$(printf '%s%s' '~' '/')
dollar_home=$(printf '%s%s' '$' 'HOME')
braced_home=$(printf '%s%s%s%s' '$' '{' 'HOME' '}')
root=$(dirname "$(git rev-parse --show-toplevel)")
ref="$root/reference/hammer2"
fail=0
list=$(mktemp)
trap 'rm -f "$list"' EXIT

{
  printf '%s\n' "${tilde_slash}${dir}"
  printf '%s\n' "${braced_home}/$fake"
  printf 'parent %s\n' "$parent_dir"
} > "$list"
export ATMO_LICENSE_GUARD_LOCAL=$list

check() {
  local want=$1 name=$2 json=$3 rc=0
  printf '%s' "$json" | "$guard" >/dev/null 2>&1 || rc=$?
  if [ "$rc" = "$want" ]; then echo "ok   $name"; else echo "FAIL $name: exit $rc, want $want"; fail=1; fi
}
bash_call() { jq -n --arg c "$1" '{tool_name:"Bash",tool_input:{command:$c}}'; }
read_call() { jq -n --arg f "$1" '{tool_name:"Read",tool_input:{file_path:$f}}'; }
grok_call() { jq -n --arg c "$1" '{toolName:"run_terminal_command",toolInput:{command:$c}}'; }

# Direct spellings, in both harnesses' shapes, with the local list naming the directory.
check 2 "grep"           "$(bash_call "grep -rn x ${tilde_slash}${dir}/hammer2.src")"
check 2 "grok shape"     "$(grok_call "grep -rn x ${tilde_slash}${dir}/hammer2.src")"
check 2 "read"           "$(read_call "${dollar_home}/${dir}/README.md")"
check 2 "HOME variable"  "$(bash_call "cat ${dollar_home}/${dir}/${tree}/LICENSE")"
check 2 "system root"    "$(bash_call "grep -r x $sys/kernels")"
check 2 "copyleft host"  "$(jq -n --arg u "https://$host/linux/latest/source" '{tool_name:"WebFetch",tool_input:{url:$u,prompt:"x"}}')"
check 2 "local root form" "$(bash_call "cat ${tilde_slash}${fake}/x")"

# Indirect spellings.
check 2 "relative"       "$(bash_call "cd ${tilde_slash}${dir} && grep -rn x ${tree}/master")"
check 2 "dot-dot"        "$(bash_call "cat ${tilde_slash}${dir}/../${dir}/${tree}/x")"
check 2 "braced HOME"    "$(bash_call "cat ${braced_home}/${dir}/${tree}/x")"
check 2 "quoted HOME"    "$(bash_call "cat \"${dollar_home}\"/${dir}/${tree}/x")"
check 2 "dot-dot system" "$(bash_call "grep x /usr/lib/..$sys/debug/x")"
check 2 "double slash"   "$(bash_call "grep x /usr//src/kernels/x")"

# Parents a recursive search would descend from.
check 2 "parent"         "$(bash_call "grep -rn x ${tilde_slash}${dir}")"
check 2 "parent slash"   "$(bash_call "find ${tilde_slash}${dir}/ -name x")"
check 2 "parent glob"    "$(bash_call "grep -n x ${tilde_slash}${dir}/*")"
check 2 "system parent"  "$(bash_call "cd $sys && grep -r x kernels")"
check 2 "local parent"       "$(bash_call "grep -rn x $parent_dir")"
check 2 "local parent slash" "$(bash_call "find $parent_dir/ -name x")"
check 0 "local parent child" "$(bash_call "cat $parent_dir/child")"

# Allowed. The reference library is beside the worktrees, derived from this worktree.
check 0 "reference grep" "$(jq -n --arg p "$ref" '{tool_name:"Grep",tool_input:{pattern:"x",path:$p}}')"
check 0 "reference cat"  "$(bash_call "cat ${ref}/README")"
check 0 "design doc"     "$(read_call "${ref}/sys/vfs/hammer2/DESIGN")"
check 2 "sibling"  "$(read_call "${dollar_home}/${dir}/hammer2.src/main/docs/DESIGN")"
check 0 "this tree"      "$(read_call "CLAUDE.md")"
check 0 "no tool input"  '{"tool_name":"Read"}'
check 0 "not json"       'not json'

# No local list: tracked system roots and their parent still refuse, and allowed paths pass.
export ATMO_LICENSE_GUARD_LOCAL=
check 2 "no list system root"    "$(bash_call "grep -r x $sys/kernels")"
check 2 "no list system parent"  "$(bash_call "cd $sys && grep -r x kernels")"
check 2 "no list copyleft host"  "$(jq -n --arg u "https://$host/linux/latest/source" '{tool_name:"WebFetch",tool_input:{url:$u,prompt:"x"}}')"
check 0 "no list reference grep" "$(jq -n --arg p "$ref" '{tool_name:"Grep",tool_input:{pattern:"x",path:$p}}')"
check 0 "no list reference cat"  "$(bash_call "cat ${ref}/README")"
check 0 "no list design doc"     "$(read_call "${ref}/sys/vfs/hammer2/DESIGN")"
check 0 "no list grep"           "$(bash_call "grep -rn x ${tilde_slash}${dir}/hammer2.src")"
check 0 "no list read"           "$(read_call "${dollar_home}/${dir}/README.md")"
check 0 "no list grok shape"     "$(grok_call "grep -rn x ${tilde_slash}${dir}/hammer2.src")"

exit $fail

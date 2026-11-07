#!/usr/bin/env bash
# Tests license-guard.sh by piping tool calls to it as strings; nothing is opened. The forbidden
# names are assembled from parts so that editing this file does not trip the guard it tests.
set -u

guard="$(dirname "${BASH_SOURCE[0]}")/license-guard.sh"
tree="sel4$(printf .src)"
sys=/usr/src
host="elixir$(printf .bootlin.com)"
fail=0

check() {
  local want=$1 name=$2 json=$3 rc=0
  printf '%s' "$json" | "$guard" >/dev/null 2>&1 || rc=$?
  if [ "$rc" = "$want" ]; then echo "ok   $name"; else echo "FAIL $name: exit $rc, want $want"; fail=1; fi
}
bash_call() { jq -n --arg c "$1" '{tool_name:"Bash",tool_input:{command:$c}}'; }
read_call() { jq -n --arg f "$1" '{tool_name:"Read",tool_input:{file_path:$f}}'; }

# Direct spellings, in both harnesses' shapes.
check 2 "grep"           "$(bash_call "grep -rn x ~/sel4/$tree/src")"
check 2 "grok shape"     "$(jq -n --arg c "grep -rn x ~/sel4/$tree/src" '{toolName:"run_terminal_command",toolInput:{command:$c}}')"
check 2 "read"           "$(read_call "$HOME/sel4/$tree/README.md")"
check 2 "HOME variable"  "$(bash_call "cat \$HOME/sel4/$tree/LICENSE")"
check 2 "system root"    "$(bash_call "grep -r x $sys/kernels")"
check 2 "copyleft host"  "$(jq -n --arg u "https://$host/linux/latest/source" '{tool_name:"WebFetch",tool_input:{url:$u,prompt:"x"}}')"

# Indirect spellings.
check 2 "relative"       "$(bash_call "cd ~/sel4 && grep -rn x $tree/master")"
check 2 "dot-dot"        "$(bash_call "cat ~/sel4/../sel4/$tree/x")"
check 2 "braced HOME"    "$(bash_call "cat \${HOME}/sel4/$tree/x")"
check 2 "quoted HOME"    "$(bash_call "cat \"\$HOME\"/sel4/$tree/x")"
check 2 "dot-dot system" "$(bash_call "grep x /usr/lib/..$sys/debug/x")"
check 2 "double slash"   "$(bash_call "grep x /usr//src/kernels/x")"

# Parents a recursive search would descend from.
check 2 "parent"         "$(bash_call "grep -rn x ~/sel4")"
check 2 "parent slash"   "$(bash_call "find ~/sel4/ -name x")"
check 2 "parent glob"    "$(bash_call "grep -n x ~/sel4/*")"
check 2 "system parent"  "$(bash_call "cd $sys && grep -r x kernels")"

# Allowed.
check 0 "reference grep" "$(jq -n --arg p "$HOME/atmosphere.src/reference/hammer2" '{tool_name:"Grep",tool_input:{pattern:"x",path:$p}}')"
check 0 "reference cat"  "$(bash_call "cat ~/atmosphere.src/reference/hammer2/README")"
check 0 "design doc"     "$(read_call "$HOME/atmosphere.src/reference/hammer2/sys/vfs/hammer2/DESIGN")"
check 0 "named sibling"  "$(read_call "$HOME/sel4/hammer2.src/main/docs/DESIGN")"
check 0 "this tree"      "$(read_call "CLAUDE.md")"
check 0 "no tool input"  '{"tool_name":"Read"}'
check 0 "not json"       'not json'

exit $fail

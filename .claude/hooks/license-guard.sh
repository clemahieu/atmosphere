#!/usr/bin/env bash
# SPDX-License-Identifier: MIT

# PreToolUse hook: refuse a tool call that would open, fetch or grep a copyleft
# source (CLAUDE.md, License). Exit 2 with the reason on stderr blocks the call
# in Claude Code and in Grok; in agy, whose payload carries toolCall, exit 0 with
# {"decision":"deny","reason":...} or {"decision":"allow"} on stdout does the same.
# Machine-specific roots and parents are one path
# per line in license-guard.local beside this script, or the file named by
# ATMO_LICENSE_GUARD_LOCAL when set; an empty value means no local list.
# A line "parent <path>" is a parent; any other line is a root. Lines starting
# with # are comments. A path may name the home directory with a tilde or the home variable.
set -u

normalize() {
  local s=$1
  s=${s//\"/}
  s=${s//\'/}
  s=${s//"~/"/"$HOME/"}
  s=${s//"\$HOME/"/"$HOME/"}
  s=${s//"\${HOME}/"/"$HOME/"}
  s=${s//\/\//\/}
  while [[ $s =~ ^(.*)/[^/[:space:]]+/\.\./(.*)$ ]]; do
    s=${BASH_REMATCH[1]}/${BASH_REMATCH[2]}
  done
  printf '%s' "$s"
}

# A name that identifies a forbidden tree wherever a path to it is spelled.
names=(
  "sel4.src"  # the seL4 kernel, GPL
)

roots=(
  "/usr/src/kernels"  # Linux kernel headers, GPL
  "/usr/src/debug"    # Fedora debug sources: kernel, binutils, gdb, glibc
)

# Directories holding a forbidden tree: a recursive search from one reaches it.
parents=(
  "/usr/src"
)

repos=(
  github.com/torvalds/linux
  github.com/gregkh/linux
  git.kernel.org
  elixir.bootlin.com
  github.com/seL4/seL4
  gitlab.com/qemu-project/qemu
  github.com/qemu/qemu
  git.qemu.org
  sourceware.org/git/binutils-gdb
  github.com/bminor/binutils-gdb
  git.savannah.gnu.org/cgit/grub
  git.savannah.gnu.org/git/grub
  github.com/openzfs/zfs
)

if [ "${ATMO_LICENSE_GUARD_LOCAL+set}" = set ]; then
  local_file="$ATMO_LICENSE_GUARD_LOCAL"
else
  local_file="$(dirname "${BASH_SOURCE[0]}")/license-guard.local"
fi
if [ -n "$local_file" ] && [ -f "$local_file" ]; then
  while IFS= read -r line || [ -n "$line" ]; do
    line=${line%$'\r'}
    case "$line" in
      ''|\#*) continue ;;
    esac
    case "$line" in
      parent\ *)
        path=$(normalize "${line#parent }")
        [ -n "$path" ] || continue
        parents+=("$path")
        ;;
      *)
        path=$(normalize "$line")
        [ -n "$path" ] || continue
        roots+=("$path")
        ;;
    esac
  done < "$local_file"
fi

input=$(cat)
is_agy=0
if printf '%s' "$input" | jq -e 'type == "object" and has("toolCall")' >/dev/null 2>&1; then
  is_agy=1
  strings=$(printf '%s' "$input" | jq -r '(.toolCall.args // {}) | .. | strings' 2>/dev/null) || {
    printf '{"decision":"allow"}\n'
    exit 0
  }
else
  strings=$(printf '%s' "$input" | jq -r '(.tool_input // .toolInput // {}) | .. | strings' 2>/dev/null) || exit 0
fi

refuse() {
  local msg=$1
  if [ "$is_agy" = 1 ]; then
    jq -cn --arg r "$msg" '{decision:"deny",reason:$r}'
    exit 0
  fi
  echo "$msg" >&2
  exit 2
}

while IFS= read -r s; do
  [ -n "$s" ] || continue
  s=$(normalize "$s")
  for r in "${names[@]}"; do
    case "$s" in *"$r"*)
      refuse "license guard: $r is a forbidden source (CLAUDE.md, License); refer to it by name, not by path" ;;
    esac
  done
  for r in "${parents[@]}"; do
    if [[ $s =~ (^|[[:space:]=:])"$r"/?\*?([[:space:]\;\|\&\)]|$) ]]; then
      refuse "license guard: $r holds a forbidden source (CLAUDE.md, License); name the directory you want inside it"
    fi
  done
  for r in "${roots[@]}"; do
    case "$s" in *"$r"*)
      refuse "license guard: $r is a forbidden source (CLAUDE.md, License); refer to it by name, not by path" ;;
    esac
  done
  for r in "${repos[@]}"; do
    case "$s" in *"$r"*)
      refuse "license guard: $r is copyleft; never fetch or read it (CLAUDE.md, License)" ;;
    esac
  done
done <<< "$strings"
if [ "$is_agy" = 1 ]; then
  printf '{"decision":"allow"}\n'
fi
exit 0

#!/usr/bin/env bash
# PreToolUse hook: refuse a tool call that would open, fetch or grep a copyleft
# source (CLAUDE.md, License). Exit 2 with the reason on stderr blocks the call
# in Claude Code and in Grok. The forbidden list lives here and nowhere else.
set -u

roots=(
  "$HOME/sel4/sel4.src"   # the seL4 kernel, GPL
  "/usr/src/kernels"      # Linux kernel headers, GPL
  "/usr/src/debug"        # Fedora debug sources: kernel, binutils, gdb, glibc
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

input=$(cat)
strings=$(printf '%s' "$input" | jq -r '(.tool_input // .toolInput // {}) | .. | strings' 2>/dev/null) || exit 0

while IFS= read -r s; do
  [ -n "$s" ] || continue
  s=${s//"~/"/"$HOME/"}
  s=${s//"\$HOME/"/"$HOME/"}
  for r in "${roots[@]}"; do
    case "$s" in *"$r"*)
      echo "license guard: $r is a forbidden source (CLAUDE.md, License); refer to it by name, not by path" >&2
      exit 2 ;;
    esac
  done
  for r in "${repos[@]}"; do
    case "$s" in *"$r"*)
      echo "license guard: $r is copyleft; never fetch or read it (CLAUDE.md, License)" >&2
      exit 2 ;;
    esac
  done
done <<< "$strings"
exit 0

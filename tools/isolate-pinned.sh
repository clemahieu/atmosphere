#!/bin/bash
# Keep the host off the CPUs tools/measure-pinned.py measures on, and put it back afterwards.
#
# usage: tools/isolate-pinned.sh plan CPU... | sudo tools/isolate-pinned.sh apply CPU... | sudo tools/isolate-pinned.sh undo
#
# apply takes the measured CPUs and, in this order: stops irqbalance; points every IRQ that accepts
# it, and the default for new ones, at the online CPUs that are neither measured nor a measured
# CPU's SMT sibling; takes those siblings offline; turns boost off and raises each measured CPU's
# cpufreq minimum to its maximum. Each change is written to the state file as it is made, and undo
# reverses them from it; so is each IRQ the kernel would not move, which tools/measure-pinned.py reads.
# plan prints what apply would change and needs no root.
set -euo pipefail

state=/run/atmo-isolate-pinned
sys=/sys/devices/system/cpu

die() {
    echo "isolate-pinned: $*" >&2
    exit 1
}

usage() {
    sed -n 's/^# usage: /usage: /p' "$0" >&2
    exit 2
}

# One CPU per line from a list such as 0-3,8.
expand() {
    local part i parts
    IFS=, read -ra parts <<<"$1"
    for part in "${parts[@]}"; do
        for ((i = ${part%-*}; i <= ${part#*-}; i++)); do echo "$i"; done
    done
}

join() {
    local IFS=,
    echo "$*"
}

member() {
    local x=$1 y
    shift
    for y in "$@"; do
        if [ "$x" = "$y" ]; then return 0; fi
    done
    return 1
}

# The hex mask /proc/irq/default_smp_affinity takes, in 32-bit words, most significant first.
mask() {
    local cpu n last out="" words=()
    last=$(expand "$(cat "$sys/possible")" | tail -n 1)
    for ((n = 0; n <= last / 32; n++)); do words[n]=0; done
    for cpu in "$@"; do words[cpu / 32]=$((words[cpu / 32] | 1 << (cpu % 32))); done
    for ((n = last / 32; n >= 0; n--)); do
        out+=$(printf '%08x' "${words[n]}")
        if [ "$n" -gt 0 ]; then out+=,; fi
    done
    echo "$out"
}

# Sets measured, siblings and others from the CPUs on the command line.
setup() {
    local cpu s online
    [ $# -gt 0 ] || usage
    mapfile -t online < <(expand "$(cat "$sys/online")")
    for cpu in "$@"; do
        if ! [[ $cpu =~ ^[0-9]+$ ]] || ! member "$cpu" "${online[@]}"; then die "CPU $cpu is not online"; fi
    done
    [ -e "$sys/cpufreq/boost" ] || die "no $sys/cpufreq/boost to turn boost off with"
    measured=("$@")
    siblings=()
    for cpu in "$@"; do
        for s in $(expand "$(cat "$sys/cpu$cpu/topology/thread_siblings_list")"); do
            member "$s" "${measured[@]}" "${siblings[@]}" || siblings+=("$s")
        done
    done
    others=()
    for cpu in "${online[@]}"; do
        member "$cpu" "${measured[@]}" "${siblings[@]}" || others+=("$cpu")
    done
    [ ${#others[@]} -gt 0 ] || die "no CPU would be left for the rest of the host"
}

clock() {
    local cpu f
    echo "boost: $(cat "$sys/cpufreq/boost")"
    for cpu in "${measured[@]}"; do
        f=$sys/cpu$cpu/cpufreq
        echo "CPU $cpu cpufreq: $(cat "$f/scaling_min_freq") to $(cat "$f/scaling_max_freq") kHz, current $(cat "$f/scaling_cur_freq")"
    done
}

plan() {
    setup "$@"
    echo "measured CPUs: $(join "${measured[@]}")"
    echo "siblings to take offline: $(join "${siblings[@]}")"
    echo "IRQs and the default for new ones to point at: $(join "${others[@]}") (mask $(mask "${others[@]}"))"
    echo "irqbalance: $(systemctl is-active irqbalance || true)"
    clock
}

apply() {
    local allowed irq old error cpu f left=()
    [ "$EUID" -eq 0 ] || die "apply needs root"
    [ ! -e "$state" ] || die "$state exists, so the isolation is applied; run undo first"
    setup "$@"
    : >"$state"

    if systemctl is-active --quiet irqbalance; then
        systemctl stop irqbalance
        echo irqbalance >>"$state"
    fi

    allowed=$(join "${others[@]}")
    echo "default $(cat /proc/irq/default_smp_affinity)" >>"$state"
    mask "${others[@]}" >/proc/irq/default_smp_affinity
    # The kernel refuses the write for a managed IRQ, such as an NVMe queue's, which the driver holds
    # to the CPUs that submit its I/O. A fixed line records each refusal for tools/measure-pinned.py.
    for irq in /proc/irq/[0-9]*; do
        old=$(cat "$irq/smp_affinity_list")
        if [ "$old" = "$allowed" ]; then continue; fi
        if error=$({ printf '%s\n' "$allowed" >"$irq/smp_affinity_list"; } 2>&1); then
            echo "irq ${irq##*/} $old" >>"$state"
        else
            echo "fixed ${irq##*/} ${error##*: }" >>"$state"
            left+=("${irq##*/} ($(cat "/sys/kernel/irq/${irq##*/}/actions" 2>/dev/null || true)) on $(cat "$irq/effective_affinity_list"): ${error##*: }")
        fi
    done

    for cpu in "${siblings[@]}"; do
        echo "offline $cpu" >>"$state"
        echo 0 >"$sys/cpu$cpu/online"
    done

    # Saved before boost goes off, so undo turns boost back on before it restores them.
    for cpu in "${measured[@]}"; do
        f=$sys/cpu$cpu/cpufreq
        echo "freq $cpu $(cat "$f/scaling_min_freq") $(cat "$f/scaling_max_freq")" >>"$state"
    done
    echo "boost $(cat "$sys/cpufreq/boost")" >>"$state"
    echo 0 >"$sys/cpufreq/boost"
    for cpu in "${measured[@]}"; do
        f=$sys/cpu$cpu/cpufreq
        cat "$f/scaling_max_freq" >"$f/scaling_min_freq"
    done

    echo "measured CPUs: $(join "${measured[@]}")"
    echo "siblings offline: $(join "${siblings[@]}")"
    echo "IRQs and the default for new ones point at: $allowed"
    echo "IRQs the kernel refused to move, managed ones such as NVMe queues; tools/measure-pinned.py refuses only if one fires on a measured CPU:"
    for irq in "${left[@]}"; do echo "  IRQ $irq"; done
    echo "irqbalance: $(systemctl is-active irqbalance || true)"
    clock
    echo "state in $state; undo with: sudo $0 undo"
}

undo() {
    local kind a b c
    [ "$EUID" -eq 0 ] || die "undo needs root"
    [ -e "$state" ] || die "no $state, so nothing to undo"
    tac "$state" | while read -r kind a b c; do
        case $kind in
        boost) echo "$a" >"$sys/cpufreq/boost" ;;
        freq)
            echo "$c" >"$sys/cpu$a/cpufreq/scaling_max_freq"
            echo "$b" >"$sys/cpu$a/cpufreq/scaling_min_freq"
            ;;
        offline) echo 1 >"$sys/cpu$a/online" ;;
        irq) echo "$b" >"/proc/irq/$a/smp_affinity_list" ;;
        fixed) ;;
        default) echo "$a" >/proc/irq/default_smp_affinity ;;
        irqbalance) systemctl start irqbalance ;;
        *) die "unknown line in $state: $kind $a $b $c" ;;
        esac
    done
    rm "$state"
    echo "restored; online CPUs $(cat "$sys/online"), irqbalance $(systemctl is-active irqbalance || true), boost $(cat "$sys/cpufreq/boost")"
}

case ${1-} in
plan | apply)
    command=$1
    shift
    "$command" "$@"
    ;;
undo)
    [ $# -eq 1 ] || usage
    undo
    ;;
*) usage ;;
esac

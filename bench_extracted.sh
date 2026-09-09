#!/usr/bin/env bash
# ----------------------------------------------------------------------------
# Benchmark the extracted OCaml certificate checker, end to end:
#
#   lrsgmp (.ine -> .ext)  ->  lrs-postprocess --bin (.ext -> -cert.bin,
#   with the in-memory Rust check)  ->  homology_checker.exe (-cert.bin)
#
# Artifacts and timing conventions follow ../lrs-postprocess/run-cert-pipeline.sh
# (same data directory, same BASE-lrs.time reference files); this script only
# adds the extracted-checker stage, so lrs-postprocess itself stays untouched.
#
# Usage:
#   ./bench_extracted.sh [--force] BASE [BASE ...]
#
# BASE names a data/BASE.ine instance in the lrs-postprocess data directory.
# Stages are skipped when their artifact is newer than its input; --force
# regenerates everything. Results are appended to bench-results.tsv.
#
# Environment:
#   POSTDIR   lrs-postprocess checkout   (default: ../lrs-postprocess)
#   LRSGMP    lrs binary                 (default: ../lrslib/lrsgmp, the pinned patched lrs)
#   CHECKER   extracted checker          (default: _build/default/ocaml/homology_checker.exe)
#   TIME_CMD  GNU time                   (default: gtime, else /usr/bin/time -p)
# ----------------------------------------------------------------------------
set -uo pipefail

here=$(cd -- "$(dirname -- "$0")" && pwd)
POSTDIR="${POSTDIR:-$here/../lrs-postprocess}"
DATA="$POSTDIR/data"
LRSGMP="${LRSGMP:-$here/../lrslib/lrsgmp}"
BIN="$POSTDIR/target/release/lrs-postprocess"
CHECKER="${CHECKER:-$here/_build/default/ocaml/homology_checker.exe}"
RESULTS="$here/bench-results.tsv"

if command -v gtime >/dev/null 2>&1; then
    TIME_CMD="${TIME_CMD:-gtime}"; TIME_STYLE=gnu
else
    TIME_CMD="${TIME_CMD:-/usr/bin/time}"; TIME_STYLE=bsd
fi

force=0
if [[ "${1:-}" == "--force" ]]; then force=1; shift; fi
if [[ $# -lt 1 ]]; then
    grep '^#' "$0" | sed -n '2,24p' | sed 's/^# \{0,1\}//'
    exit 2
fi

for tool in "$LRSGMP" "$BIN" "$CHECKER"; do
    [[ -x "$tool" ]] || { echo "error: missing tool: $tool" >&2; exit 1; }
done

# Wall-clock a command; the elapsed seconds end up in $ELAPSED.
timed() {
    local tf; tf=$(mktemp)
    if [[ "$TIME_STYLE" == gnu ]]; then
        "$TIME_CMD" -f "%e" -o "$tf" "$@"
    else
        { "$TIME_CMD" -p "$@" ; } 2> "$tf"
    fi
    local status=$?
    if [[ "$TIME_STYLE" == gnu ]]; then
        ELAPSED=$(cat "$tf" 2>/dev/null)
    else
        ELAPSED=$(awk '/^real/ {print $2}' "$tf")
    fi
    rm -f "$tf"
    return "$status"
}

# Timing lines: "<label>  <secs> s [<verdict>]" -- the seconds sit before the
# lone "s" token, wherever the verdict is.
checker_field() {
    awk -v k="$1" '$0 ~ "^"k {for (i=2; i<=NF; i++) if ($i=="s") print $(i-1)}' "$2" | tail -1
}
checker_verdict() { awk -v k="$1" '$0 ~ "^"k {print $NF}' "$2" | tail -1; }

[[ -f "$RESULTS" ]] || printf 'instance\tlrs_s\tcertgen_s\tload_s\tvtx_containment_s\tvtx_equality_s\tgraph_equality_s\tchecker_total_s\tchecker_vs_lrs\tverdict\tdate\n' > "$RESULTS"

overall=0
for base in "$@"; do
    ine="$DATA/$base.ine"; ext="$DATA/$base.ext"
    bin="$DATA/$base-cert.bin"; blog="$DATA/$base-bin.log"
    clog="$DATA/$base-ocaml.log"; tfile="$DATA/$base-lrs.time"
    gfile="$DATA/$base-certgen.time"
    echo; echo "########## $base ##########"
    [[ -f "$ine" ]] || { echo "error: no such instance: $ine" >&2; overall=1; continue; }

    # 1. vertex enumeration (the reference time); the output is staged in a
    # .tmp and moved into place on success, so an interrupted run leaves no
    # partial artifact the mtime-based skip test could mistake for a fresh one
    if [[ $force -eq 1 || ! -f "$ext" || "$ine" -nt "$ext" ]]; then
        echo "--- lrsgmp: $base.ine -> $base.ext"
        timed "$LRSGMP" "$ine" "$ext.tmp" > "$DATA/$base-ext.log" 2>&1 \
            || { rm -f "$ext.tmp"; echo "lrsgmp FAILED (see $DATA/$base-ext.log)" >&2; overall=1; continue; }
        mv "$ext.tmp" "$ext"
        printf '%s\n' "$ELAPSED" > "$tfile"
    else
        echo "--- lrsgmp: reusing $base.ext"
    fi
    lrs_s=$(cat "$tfile" 2>/dev/null || echo "")

    # 2. certificate construction + Rust check + binary encoding
    if [[ $force -eq 1 || ! -f "$bin" || "$ext" -nt "$bin" || "$BIN" -nt "$bin" ]]; then
        echo "--- lrs-postprocess --bin: $base.ext -> $base-cert.bin"
        timed "$BIN" postprocess --bin "$ine" "$ext" > "$bin.tmp" 2> "$blog" \
            || { rm -f "$bin.tmp"; echo "postprocess FAILED (see $blog)" >&2; overall=1; continue; }
        mv "$bin.tmp" "$bin"
        certgen_s="$ELAPSED"
        printf '%s\n' "$certgen_s" > "$gfile"
        grep -q "Generated certificate accepted" "$blog" \
            || { echo "warning: Rust check did not report acceptance" >&2; }
    else
        echo "--- lrs-postprocess: reusing $base-cert.bin"
        certgen_s=$(cat "$gfile" 2>/dev/null || echo "")
    fi

    # 3. the extracted OCaml checker (its stderr carries per-check timings)
    echo "--- homology_checker.exe $base-cert.bin"
    "$CHECKER" "$bin" 2> "$clog"
    status=$?
    cat "$clog"
    load_s=$(checker_field "certificate loading" "$clog")
    t1=$(checker_field "vertex containment" "$clog");  v1=$(checker_verdict "vertex containment" "$clog")
    t2=$(checker_field "vertex equality" "$clog");     v2=$(checker_verdict "vertex equality" "$clog")
    t3=$(checker_field "graph equality" "$clog");      v3=$(checker_verdict "graph equality" "$clog")
    total=$(awk -v a="${load_s:-0}" -v b="${t1:-0}" -v c="${t2:-0}" -v d="${t3:-0}" \
                'BEGIN {printf "%.6f", a+b+c+d}')
    ratio=$(awk -v t="$total" -v r="${lrs_s:-0}" \
        'BEGIN {if (r>0) printf "%.3f", t/r; else printf "n/a"}')
    verdict="accepted"; [[ $status -eq 0 ]] || verdict="REJECTED(rc=$status)"
    [[ $status -eq 0 ]] || overall=1

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$base" "${lrs_s:-?}" "${certgen_s:-?}" "${load_s:-?}" \
        "${t1:-?}" "${t2:-?}" "${t3:-?}" "$total" "$ratio" "$verdict" \
        "$(date '+%Y-%m-%d %H:%M')" >> "$RESULTS"
    echo "--- $base: checker total ${total}s (${ratio}x lrs) [$verdict]"
done

echo; echo "results table: $RESULTS"
exit "$overall"

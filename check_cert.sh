#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 ]]; then
    echo "Usage: $0 INSTANCE [MAKE_ARGUMENTS...]" >&2
    echo "Example: $0 poly20dim21" >&2
    exit 2
fi

repo_dir=$(cd -- "$(dirname -- "$0")" && pwd)
cd "$repo_dir"

instance=$1
shift

if [[ ! "$instance" =~ ^[A-Za-z0-9_.-]+$ ]]; then
    echo "Invalid instance name: $instance" >&2
    exit 2
fi

certificate="../lrs-postprocess/data/${instance}-cert.bin"
template="src/CheckCert.v.in"
output="src/CheckCert.v"
target="src/CheckCert.vo"
log_dir="log"
log_file="${log_dir}/${instance}.log"

if [[ ! -f "$certificate" ]]; then
    echo "Certificate not found: $certificate" >&2
    exit 1
fi

if [[ ! -f "$template" ]]; then
    echo "Template not found: $template" >&2
    exit 1
fi

mkdir -p "$log_dir"

sed "s/@INSTANCE@/${instance}/g" "$template" > "${output}.tmp"
mv "${output}.tmp" "$output"

raw_log=$(mktemp "${log_dir}/.${instance}.raw.XXXXXX")
trap 'rm -f "$raw_log"' EXIT

# Keep the complete original output on stdout.
set +e
make rocq 2>&1 | tee "$raw_log"
make_status=${PIPESTATUS[0]}
set -e

# Save a cleaner version in log/INSTANCE.log.
sed -n '
    /Instance/,$ {
        /^[[:space:]]*- : Init\.unit = ()[[:space:]]*$/d
        p
    }
' "$raw_log" > "$log_file"

exit "$make_status"
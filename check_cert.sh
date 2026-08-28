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

if [[ ! -f "$certificate" ]]; then
    echo "Certificate not found: $certificate" >&2
    exit 1
fi

if [[ ! -f "$template" ]]; then
    echo "Template not found: $template" >&2
    exit 1
fi

sed "s/@INSTANCE@/${instance}/g" "$template" > "${output}.tmp"
mv "${output}.tmp" "$output"

make "$@"
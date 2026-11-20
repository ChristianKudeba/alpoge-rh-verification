#!/usr/bin/env bash
# Genuine historical Comparator; no alternate checker and no unsafe fallback.
set -euo pipefail
if [[ $# != 3 ]]; then echo 'usage: run-comparator-isolated.sh PROJECT_DIR CONFIG_PATH LOG_PATH' >&2; exit 2; fi
project_dir=$(realpath "$1")
config_path=$(realpath "$2")
log_path=$(realpath -m "$3")
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
for key in COMPARATOR_EXE COMPARATOR_LEAN4EXPORT COMPARATOR_LANDRUN COMPARATOR_NO_NETWORK; do
  [[ -n ${!key:-} && -x ${!key} ]] || { echo "Missing executable: $key" >&2; exit 125; }
done
[[ $(id -u) != 0 ]] || { echo 'Refusing privileged execution' >&2; exit 125; }
[[ $(cat "$project_dir/lean-toolchain") == leanprover/lean4:v4.33.1 ]] || {
  echo 'Refusing a changed project toolchain' >&2; exit 125;
}
[[ $(lean --version) == 'Lean (version 4.33.1,'* ]] || { echo 'Wrong Lean executable' >&2; exit 125; }
mkdir -p "$(dirname "$log_path")" "$project_dir/.lake"
probe_dir=$(mktemp -d "$(dirname "$log_path")/sandbox-probe.XXXXXX")
trap 'rm -rf -- "$probe_dir"' EXIT
mkdir "$probe_dir/allowed"
printf 'protected\n' > "$probe_dir/protected"
python_binary=$(command -v python3)
{
  date -u '+Started: %Y-%m-%dT%H:%M:%SZ'
  printf 'Project: %s\nConfiguration: %s\n' "$project_dir" "$config_path"
  lean --version
  sha256sum "$config_path" "$COMPARATOR_EXE" "$COMPARATOR_LEAN4EXPORT" "$COMPARATOR_LANDRUN"
  "$COMPARATOR_NO_NETWORK" "$COMPARATOR_LANDRUN" --best-effort --ro / --rw /dev \
    --rwx "$probe_dir/allowed" --ldd --add-exec -- \
    "$python_binary" "$script_dir/probe-sandbox.py" "$probe_dir/protected" "$probe_dir/allowed/test"
  cd "$project_dir"
  # lake env only sets paths; Comparator itself builds Challenge and Solution
  # (including the complete Main import closure) in its Landrun subprocesses.
  "$COMPARATOR_NO_NETWORK" lake env "$COMPARATOR_EXE" "$config_path"
  date -u '+Comparator completed successfully: %Y-%m-%dT%H:%M:%SZ'
} 2>&1 | tee "$log_path"

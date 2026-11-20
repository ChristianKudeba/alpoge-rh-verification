#!/usr/bin/env bash
set -euo pipefail
if [[ $# != 1 ]]; then echo 'usage: prepare-tools.sh TOOL_ROOT' >&2; exit 2; fi
tool_root=$(realpath -m "$1")
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
[[ $(uname -s) == Linux && $(uname -m) == x86_64 && $(id -u) != 0 ]]
mkdir -p "$tool_root/bin" "$tool_root/downloads"

download() {
  local url=$1 output=$2 expected=$3
  if [[ ! -f "$output" ]]; then curl --fail --location --retry 3 "$url" --output "$output"; fi
  printf '%s  %s\n' "$expected" "$output" | sha256sum --check --strict
}
download https://github.com/leanprover/elan/releases/download/v4.4.0/elan-x86_64-unknown-linux-gnu.tar.gz \
  "$tool_root/downloads/elan.tar.gz" 0e8250aa2be86c7af929ade68db617af9edc8b9ccf6eaf5ece228250d0d032e2
tar -xzf "$tool_root/downloads/elan.tar.gz" -C "$tool_root/downloads"
export ELAN_HOME="$tool_root/elan"
export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
"$tool_root/downloads/elan-init" -y --no-modify-path --default-toolchain none
"$ELAN_HOME/bin/elan" toolchain install "$ELAN_TOOLCHAIN"
lean_prefix=$("$ELAN_HOME/bin/lean" --print-prefix)
export PATH="$lean_prefix/bin:$tool_root/bin:$PATH"
lean --version

download https://go.dev/dl/go1.27.4.linux-amd64.tar.gz \
  "$tool_root/downloads/go.tar.gz" 7226736c2339719cda28fbf3a54d71aa63bcefe376e98cef00034268dab24840
tar -xzf "$tool_root/downloads/go.tar.gz" -C "$tool_root"
export GOPATH="$tool_root/gopath" GOCACHE="$tool_root/gocache"

checkout_pin() {
  local url=$1 directory=$2 revision=$3
  if [[ ! -d "$directory/.git" ]]; then git init -q "$directory"; git -C "$directory" remote add origin "$url"; fi
  git -C "$directory" fetch --depth 1 origin "$revision"
  git -C "$directory" checkout --detach "$revision"
  [[ $(git -C "$directory" rev-parse HEAD) == "$revision" ]]
}
checkout_pin https://github.com/leanprover/comparator.git "$tool_root/comparator" c0c5a52d2aff92b457c3e5ed4a68c1ebc5795809
(cd "$tool_root/comparator" && lake build comparator lean4export)
[[ $(git -C "$tool_root/comparator/.lake/packages/lean4export" rev-parse HEAD) == 15f6055e299ad5b89345e533cc2192f4cc00f659 ]]
checkout_pin https://github.com/Zouuup/landrun.git "$tool_root/landrun" ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a
(cd "$tool_root/landrun" && "$tool_root/go/bin/go" build -o "$tool_root/bin/landrun" ./cmd/landrun)
gcc -std=c11 -Wall -Wextra -Werror -O2 "$script_dir/no-network.c" -o "$tool_root/bin/no-network"

export COMPARATOR_EXE="$tool_root/comparator/.lake/build/bin/comparator"
export COMPARATOR_LEAN4EXPORT="$tool_root/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
export COMPARATOR_LANDRUN="$tool_root/bin/landrun"
export COMPARATOR_NO_NETWORK="$tool_root/bin/no-network"
{
  printf 'export ELAN_HOME=%q\n' "$ELAN_HOME"
  printf 'export ELAN_TOOLCHAIN=%q\n' "$ELAN_TOOLCHAIN"
  printf 'export PATH=%q:"$PATH"\n' "$lean_prefix/bin:$tool_root/bin"
  for key in COMPARATOR_EXE COMPARATOR_LEAN4EXPORT COMPARATOR_LANDRUN COMPARATOR_NO_NETWORK; do
    printf 'export %s=%q\n' "$key" "${!key}"
  done
} > "$tool_root/environment.sh"
sha256sum "$COMPARATOR_EXE" "$COMPARATOR_LEAN4EXPORT" "$COMPARATOR_LANDRUN" "$COMPARATOR_NO_NETWORK" > "$tool_root/tool-binaries.sha256"
cat > "$tool_root/toolchain-manifest.json" <<'EOF'
{
  "lean_toolchain": "leanprover/lean4:v4.33.1",
  "lean_release_commit": "819816b2e0a3bf405af45ae5c7af2491d8f5bee6",
  "comparator_commit": "c0c5a52d2aff92b457c3e5ed4a68c1ebc5795809",
  "lean4export_commit": "15f6055e299ad5b89345e533cc2192f4cc00f659",
  "landrun_commit": "ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a",
  "elan_version": "v4.4.0",
  "go_version": "go1.27.4",
  "binary_sha256_file": "tool-binaries.sha256",
  "external_nanoda": false,
  "status": "built; semantic controls and full proof require separate results"
}
EOF
printf 'Tools built. Source %s/environment.sh before using the launcher.\n' "$tool_root"

#!/usr/bin/env bash
# Independently verify the root challenge/solution pair with leanprover/comparator.
#
# Trust required: the Lean kernel, Mathlib, Challenge.lean as the statement,
# and comparator itself. The KTV proof code is checked independently by
# comparator through the exported Solution.lean environment.
set -euo pipefail

TOOLCHAIN_TAG="$(sed -e 's/^leanprover\/lean4://' lean-toolchain | tr -d '[:space:]')"
WORK="${COMPARATOR_WORK:-$HOME/.cache/ktv-comparator}"

mkdir -p "$WORK"

if [ ! -d "$WORK/comparator" ]; then
  git clone --branch "$TOOLCHAIN_TAG" --depth 1 \
    https://github.com/leanprover/comparator "$WORK/comparator"
fi

if [ ! -d "$WORK/lean4export" ]; then
  git clone --branch "$TOOLCHAIN_TAG" --depth 1 \
    https://github.com/leanprover/lean4export "$WORK/lean4export"
fi

(cd "$WORK/comparator" && lake build)
(cd "$WORK/lean4export" && lake build)

if [ ! -x "$WORK/landrun-bin" ]; then
  curl -sL -o "$WORK/landrun-bin" \
    https://github.com/Zouuup/landrun/releases/download/v0.1.14/landrun-linux-amd64
  chmod +x "$WORK/landrun-bin"
fi

EXTRA=""
for d in /lib64 /lib /usr/lib /nix/store; do
  [ -e "$d" ] && EXTRA="$EXTRA --rox $d"
done

printf '#!/usr/bin/env bash\nexec "%s/landrun-bin"%s "$@"\n' "$WORK" "$EXTRA" \
  > "$WORK/landrun"
chmod +x "$WORK/landrun"

export COMPARATOR_LANDRUN="$WORK/landrun"
export PATH="$WORK:$PATH"
export PATH="$WORK/lean4export/.lake/build/bin:$PATH"

lake exe cache get
lake env "$WORK/comparator/.lake/build/bin/comparator" comparator.json

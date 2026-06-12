#!/bin/sh
set -eu

: "${CREUSOT_DATA_HOME:?CREUSOT_DATA_HOME is required}"
: "${CREUSOT_PACKAGE_SRC:?CREUSOT_PACKAGE_SRC is required}"

bin_dir="$CREUSOT_DATA_HOME/bin"
share_dir="$CREUSOT_DATA_HOME/share/why3find"
patched_share="$CREUSOT_DATA_HOME/patched-share/why3find"

require_tool() {
  tool="$1"
  path="$(command -v "$tool")" || {
    echo "required Creusot prover tool '$tool' is not on PATH" >&2
    exit 2
  }
  printf '%s' "$path"
}

if [ ! -f "$CREUSOT_PACKAGE_SRC/creusot/creusot/int.coma" ]; then
  echo "Creusot package source is missing int.coma: $CREUSOT_PACKAGE_SRC" >&2
  echo "Run: cd \$HOME/.local/opt/creusot && rustup run nightly-2026-04-21 cargo run --offline --bin prelude-generator" >&2
  exit 2
fi

mkdir -p "$bin_dir" "$share_dir" "$patched_share"

ln -sfn "$(require_tool why3)" "$bin_dir/why3"
ln -sfn "$(require_tool why3find)" "$bin_dir/why3find"
ln -sfn "$(require_tool alt-ergo)" "$bin_dir/alt-ergo"
ln -sfn "$(require_tool z3)" "$bin_dir/z3"
ln -sfn "$(require_tool cvc4)" "$bin_dir/cvc4"

cat > "$bin_dir/cvc5" <<'EOF'
#!/bin/sh
if [ "$1" = "--version" ]; then
  echo "This is cvc5 version 1.3.1"
  exit 0
fi
exec /usr/bin/cvc5 "$@"
EOF
chmod +x "$bin_dir/cvc5"

mkdir -p "$patched_share/packages"
cp -R "$CREUSOT_PACKAGE_SRC/." "$patched_share/packages/"

# The locally installed Why3/why3find stack does not expose the old signed-BV
# helper names that this Creusot prelude expects. Restore them in the copied
# generated package only; the installed Creusot checkout is left untouched.
perl -0pi -e 's/(constant min_sint_as_BV256 : BV256\.t = (0x[0-9A-F]+).*?function of_bool \[\@inline:trivial\] \(b : bool\) : t = if b then 1:t else 0:t\n)/$1\n  constant two_power_sizem1 : int = $2\n  constant min_sint : t = of_BV256 min_sint_as_BV256\n  constant minus_one : t = sub (of_bool false) (of_bool true)\n/sg' \
  "$patched_share/packages/creusot/creusot/int.coma"

ln -sfn "$patched_share/packages" "$share_dir/packages"

#!/bin/sh
# Installs rustd, cargo-rustd, rustd-rustc and rustd-rustc-first from a GitHub release.
#
#   curl -fsSL https://dioxuslabs.github.io/rustd/install.sh | sh
#
# RUSTD_VERSION names the release: the latest numbered one unless set, or the newest build
# of main (`nightly`) while there is none.
# RUSTD_INSTALL_DIR is where the three binaries go (cargo's bin directory unless set).
set -eu

repo=https://github.com/DioxusLabs/rustd
version=${RUSTD_VERSION:-latest}
dir=${RUSTD_INSTALL_DIR:-${CARGO_HOME:-$HOME/.cargo}/bin}
toolchain=1.99.0

say() { printf 'rustd: %s\n' "$*" >&2; }
fail() { say "$*"; exit 1; }

case "$(uname -s) $(uname -m)" in
    "Darwin arm64") target=aarch64-apple-darwin ;;
    "Linux x86_64") target=x86_64-unknown-linux-gnu ;;
    "Linux aarch64" | "Linux arm64") target=aarch64-unknown-linux-gnu ;;
    *) fail "there is no build for $(uname -s) $(uname -m); see $repo to build from source" ;;
esac

if [ "$version" = latest ]; then
    from=$repo/releases/latest/download
else
    from=$repo/releases/download/$version
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
archive=rustd-$target.tar.gz

say "downloading $from/$archive"
if ! curl -fsSL "$from/$archive" -o "$work/$archive" 2> /dev/null; then
    [ "$version" = latest ] || fail "no release \`$version\` with $archive"
    # Before the first numbered release there is only the build of main.
    from=$repo/releases/download/nightly
    say "there is no numbered release yet; downloading $from/$archive"
    curl -fsSL "$from/$archive" -o "$work/$archive" || fail "no release with $archive"
fi
curl -fsSL "$from/SHA256SUMS" -o "$work/SHA256SUMS" || fail "the release has no SHA256SUMS"

want=$(awk -v name="$archive" '$2 == name || $2 == "*" name { print $1 }' "$work/SHA256SUMS")
if command -v sha256sum > /dev/null; then
    got=$(sha256sum "$work/$archive" | awk '{ print $1 }')
else
    got=$(shasum -a 256 "$work/$archive" | awk '{ print $1 }')
fi
[ -n "$want" ] && [ "$want" = "$got" ] || fail "the checksum of $archive is not the release's"

tar xzf "$work/$archive" -C "$work"
mkdir -p "$dir"
for bin in rustd cargo-rustd rustd-rustc rustd-rustc-first; do
    # Moved into place, so that a daemon that is running keeps the file it started from.
    cp "$work/rustd-$target/$bin" "$dir/.$bin.new"
    chmod 755 "$dir/.$bin.new"
    mv -f "$dir/.$bin.new" "$dir/$bin"
done
say "installed rustd, cargo-rustd, rustd-rustc and rustd-rustc-first in $dir"

case ":$PATH:" in
    *":$dir:"*) ;;
    *) say "$dir is not on your PATH" ;;
esac
if ! command -v rustup > /dev/null; then
    say "rustup was not found: rustd needs Rust $toolchain with rust-src"
elif ! rustup component list --toolchain "$toolchain" --installed 2> /dev/null | grep -q '^rust-src'; then
    say "rustd needs Rust $toolchain with rust-src:"
    say "    rustup toolchain install $toolchain --component rust-src"
fi
say "in a cargo project built with $toolchain: cargo rustd run"

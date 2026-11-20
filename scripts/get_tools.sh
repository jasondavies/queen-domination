#!/bin/sh
# Download, check (SHA-256) and build the two external programs used by the SAT checks:
#   CaDiCaL rel-3.1.0 (commit 6b3d70b9ce00ecbce3f829bab76d185f0e92618c) and
#   drat-trim at commit 2e3b2dc0ecf938addbd779d42877b6ed69d9a985.
# They are built in tools/ (git-ignored); nothing is installed elsewhere.  Idempotent.
# Set CADICAL_TARBALL / DRATTRIM_TARBALL to use local copies of the tarballs.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
T=$ROOT/tools
mkdir -p "$T"
CAD_URL=https://github.com/arminbiere/cadical/archive/refs/tags/rel-3.1.0.tar.gz
CAD_SHA=187fb83106e8d7964f1d409ebf056f3853105c2a8ec32427472eff734c9ccb01
DT_COMMIT=2e3b2dc0ecf938addbd779d42877b6ed69d9a985
DT_URL=https://github.com/marijnheule/drat-trim/archive/$DT_COMMIT.tar.gz
DT_SHA=a75e5a2072fa5a5493ee8504067661c6b452d45a32f889ac5b2c9470c227b58c

fetch() {  # fetch URL SHA OUT LOCALVAR
  if [ -n "$4" ]; then cp "$4" "$3"; elif [ ! -f "$3" ]; then curl -sSfL -o "$3.part" "$1" && mv "$3.part" "$3"; fi
  echo "$2  $3" | sha256sum -c --quiet - || { echo "SHA-256 mismatch for $3" >&2; rm -f "$3"; exit 1; }
}

if [ ! -x "$T/cadical" ]; then
  fetch "$CAD_URL" "$CAD_SHA" "$T/cadical-rel-3.1.0.tar.gz" "${CADICAL_TARBALL:-}"
  rm -rf "$T/cadical-src" && mkdir "$T/cadical-src"
  tar -xzf "$T/cadical-rel-3.1.0.tar.gz" -C "$T/cadical-src" --strip-components=1
  (cd "$T/cadical-src" && ./configure -O3 >/dev/null && make -j2 >/dev/null)
  cp "$T/cadical-src/build/cadical" "$T/cadical"
fi
if [ ! -x "$T/drat-trim" ]; then
  fetch "$DT_URL" "$DT_SHA" "$T/drat-trim-$DT_COMMIT.tar.gz" "${DRATTRIM_TARBALL:-}"
  rm -rf "$T/drat-trim-src" && mkdir "$T/drat-trim-src"
  tar -xzf "$T/drat-trim-$DT_COMMIT.tar.gz" -C "$T/drat-trim-src" --strip-components=1
  (cd "$T/drat-trim-src" && gcc drat-trim.c -std=c99 -D_DEFAULT_SOURCE -O2 -Werror=implicit-function-declaration -o drat-trim)
  cp "$T/drat-trim-src/drat-trim" "$T/drat-trim"
fi
"$T/cadical" --version
echo "drat-trim $DT_COMMIT"

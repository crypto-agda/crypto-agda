#!/bin/bash
set -eu
HERE="$PWD"

GITHUB="$HOME"/.agda-pkg/github

INCL=(-i. -i"$HERE" -ilib)

STDLIB="$GITHUB"/agda/agda-stdlib
INCL=("${INCL[@]}" -i"$STDLIB"/src)

LIBJS="$GITHUB"/crypto-agda/agda-libjs
INCL=("${INCL[@]}" -i"$LIBJS"/lib)

NPLIB="$GITHUB"/crypto-agda/agda-nplib
INCL=("${INCL[@]}" -i"$NPLIB"/lib)

ORIG_DIR=`pwd`
BUILD=_build
mkdir -p "$BUILD"

for m in run libagda proc; do
  coffee -b -c "$LIBJS/$m".coffee
  cp "$LIBJS/$m".js "$BUILD"
done
main="${1:-ZK/PartialHeliosVerifier}"
if [ ! -e "$main".agda ]; then
  echo "$main.agda does not exists." >>/dev/stderr
  exit 1
fi
shift || :
mainmodule="${main/\//.}"
cd "$BUILD"
cat >main.agda <<EOF
module main where
open import FFI.JS using (JS!)
import $mainmodule as M using (main)
main : JS!
main = M.main
EOF
agda --js "${INCL[@]}" main.agda
echo "Running: node run.js jAgda.main $*"
#echo NODE_PATH="$HOME/node_modules:.:$LIBJS"
BUILD_DIR=`pwd`
cd "$ORIG_DIR"
NODE_PATH=":$BUILD_DIR" node $BUILD_DIR/run.js jAgda.main "$@"

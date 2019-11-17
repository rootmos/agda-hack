#!/bin/bash

set -o nounset -o pipefail -o errexit

TMP=$(mktemp -d)
trap 'rm -rf $TMP' EXIT

INPUT=-
AGDA=${AGDA-agda}
BUILD=${BUILD-$TMP/build}
while getopts "f:A:B:-" OPT; do
    case $OPT in
        f) INPUT=$OPTARG ;;
        A) AGDA=$OPTARG ;;
        B) BUILD=$OPTARG ;;
        -) break ;;
        ?) exit 2 ;;
    esac
done
shift $((OPTIND-1))

MODULE=$(basename --suffix=.agda "$INPUT")
if [ "$MODULE" = "-" ]; then
    MODULE=CompilationTest
fi

mkdir -p "$BUILD/src"
cat "$INPUT" > "$BUILD/src/$MODULE.agda"
cat <<EOF > "$BUILD/compilation-test.agda-lib"
name: compilation-test
depend:
  standard-library
  overture
include:
  src
EOF

(cd "$BUILD" && $AGDA --compile --compile-dir="$BUILD" "src/$MODULE.agda") 2>&1 1>>"$BUILD/log"
exec "$BUILD/$MODULE" "$@"

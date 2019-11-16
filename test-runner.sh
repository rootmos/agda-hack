#!/bin/bash

set -o nounset -o pipefail -o errexit

ACTION=run
export VERBOSE=${VERBOSE-}
while getopts "e:t:lvT:-" OPT; do
    case $OPT in
        e) EXE=$OPTARG ;;
        t) TEST_CASE=$OPTARG ;;
        T) TESTS_DIR=$OPTARG ;;
        l) ACTION=list ;;
        v) VERBOSE=1 ;;
        -) break ;;
        ?) exit 2 ;;
    esac
done
shift $((OPTIND-1))

log() {
    if [ -n "$VERBOSE" ]; then
        echo 1>&2 "$@"
    fi
}

if [ "$ACTION" != "list" ] && [ -z "${EXECDIR-}" ]; then
    export EXECDIR=$(mktemp -d .tests.$(date -Is).XXXXXXX)
    log "test results in: $EXECDIR"
fi


if [[ ! -v TEST_CASE ]]; then
    TESTS_DIR=${TESTS_DIR-$(pwd)/tests}

    test_cases() {
        (
            find "$TESTS_DIR" -name "*.args" -exec basename --suffix=.args {} \;
            find "$TESTS_DIR" -name "*.stdout" -exec basename --suffix=.stdout {} \;
            find "$TESTS_DIR" -name "*.stdin" -exec basename --suffix=.stdin {} \;
            find "$TESTS_DIR" -name "*.stderr" -exec basename --suffix=.stderr {} \;
            find "$TESTS_DIR" -name "*.exit-code" -exec basename --suffix=.exit-code {} \;
        ) | sort -u
    }

    run_tests() {
        for TC in $(test_cases); do
            echo "test: $TC"
            "$0" -e "$EXE" -T "$TESTS_DIR" -t "$TC"
        done
    }

    case "${ACTION-run}" in
        list) test_cases ;;
        run) run_tests ;;
    esac

    exit 0
fi

mkdir -p "$(dirname "$EXECDIR/$TEST_CASE")"

if [ -f "$TESTS_DIR/$TEST_CASE.args" ]; then
    cat <<EOF > "$EXECDIR/$TEST_CASE.cmd"
"$EXE" $(cat "$TESTS_DIR/$TEST_CASE.args") $@
EOF
else
    cat <<EOF > "$EXECDIR/$TEST_CASE.cmd"
"$EXE" $@
EOF
fi

if [ -f "$TESTS_DIR/$TEST_CASE.stdin" ]; then
    cp "$TESTS_DIR/$TEST_CASE.stdin" "$EXECDIR/$TEST_CASE.stdin"
else
    cp /dev/null "$EXECDIR/$TEST_CASE.stdin"
fi

set +o errexit
$SHELL "$EXECDIR/$TEST_CASE.cmd" \
    < "$EXECDIR/$TEST_CASE.stdin" \
    1> "$EXECDIR/$TEST_CASE.stdout" \
    2> "$EXECDIR/$TEST_CASE.stderr"
set -o errexit
echo $? > "$EXECDIR/$TEST_CASE.exit-code"

compare() {
    diff "$1" "$2" >/dev/null
}

if [ -f "$TESTS_DIR/$TEST_CASE.exit-code" ]; then
    cp "$TESTS_DIR/$TEST_CASE.exit-code" "$EXECDIR/$TEST_CASE.expected-exit-code"
else
    echo "0" > "$EXECDIR/$TEST_CASE.expected-exit-code"
fi
compare "$EXECDIR/$TEST_CASE.expected-exit-code" "$EXECDIR/$TEST_CASE.exit-code"

if [ -f "$TESTS_DIR/$TEST_CASE.stdout" ]; then
    cp "$TESTS_DIR/$TEST_CASE.stdout" "$EXECDIR/$TEST_CASE.expected-stdout"
else
    cp /dev/null "$EXECDIR/$TEST_CASE.expected-stdout"
fi
compare "$EXECDIR/$TEST_CASE.expected-stdout" "$EXECDIR/$TEST_CASE.stdout"

if [ -f "$TESTS_DIR/$TEST_CASE.stderr" ]; then
    cp "$TESTS_DIR/$TEST_CASE.stderr" "$EXECDIR/$TEST_CASE.expected-stderr"
    compare "$EXECDIR/$TEST_CASE.expected-stderr" "$EXECDIR/$TEST_CASE.stderr"
fi

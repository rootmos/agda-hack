#!/bin/bash

set -o nounset -o pipefail -o errexit

EXE=
while getopts "e-" OPT; do
    case $OPT in
        e) EXE=$OPTARG ;;
        -) break ;;
        \?) echo "Invalid option: -$OPTARG" >&2; exit 2 ;;
    esac
done
shift $((OPTIND-1))

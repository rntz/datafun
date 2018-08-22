#!/bin/bash
set -e
rm -f All.agda agda-failures
find . -iname '*.agda' '!' -name All.agda '!' -name '.*' |
    sort |
    while read name; do
        echo -n "Running ${name}... " >&2
        if agda --allow-unsolved-metas "$name" >/dev/null 2>&1; then
            echo "ok!" >&2
            echo "${name}"
        else
            echo "failed :(" >&2
            echo "${name}" >> agda-failures
        fi
    done |
    cut -d/ -f2- |
    sed -s 's/.agda$//;s,/,.,g;s/^/import /' \
        > All.agda

#!/bin/bash
function find-agdas() {
    find * -iname '*.agda' '!' -name '.*' '!' -regex '.*trash/.*'
}

set -e
echo "digraph {"

# Generate the node names.
find-agdas |
    sed -Ee 's/.agda$//;s,/,.,g;s/.*/"&" [label="&"];/'

# Generate edges. Assumes at most one import per line, but ignores commented-out
# lines.
find-agdas |
    xargs egrep 'import [^ ]+' |
    grep -v -- '--.*import' |
    sed -Ee 's/^(.*).agda:.*import ([^ ]+).*/"\1" -> "\2";/;s,/,.,g'

echo "}"

#!/bin/bash
set -e
echo "digraph {"

# Generate the node names.
find * -iname '*.agda' '!' -name '.*' |
    sed -Ee 's/.agda$//;s,/,.,g;s/.*/"&" [label="&"];/'

# Generate edges. Assumes at most one import per line, but ignores commented-out
# lines.
find * -iname '*.agda' '!' -name '.*' |
    xargs egrep 'import [^ ]+' |
    grep -v -- '--.*import' |
    sed -Ee 's/^(.*).agda:.*import ([^ ]+).*/"\1" -> "\2";/;s,/,.,g'

echo "}"

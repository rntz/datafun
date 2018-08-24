#!/bin/bash
set -e
echo "digraph {"

# Generate the node names.
find * -iname '*.agda' '!' -name '.*' |
    sed -Ee 's/.agda$//;s,/,.,g;s/.*/"&" [label="&"];/'

# Generate edges. Assumes at most one import per line, but ignores commented-out
# lines.
find * -iname '*.agda' '!' -name '.*' |
    xargs egrep 'import [[:alnum:].]+' |
    grep -v -- '--.*import' |
    sed -Ee 's/(.*).agda:.*import ([[:alnum:].]+).*/"\1" -> "\2";/;s,/,.,g'

echo "}"

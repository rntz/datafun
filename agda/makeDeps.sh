#!/bin/bash
set -e
echo "digraph {"

# Generate the node names.
find . -iname '*.agda' '!' -name '.*' |
    sed -Ee 's,^\./,,;s,.agda$,,;s,/,.,g;s/.*/"&" [label="&"];/'

# Generate edges. 
# FIXME: This currently finds commented-out imports as well.
find . -iname '*.agda' '!' -name '.*' |
    xargs egrep -o 'import [[:alnum:].]+' |
    sed -Ee 's,^\./,",; s,\.agda,,; s,/,.,g; s,:import ," -> ",; s,$,";,'

echo "}"

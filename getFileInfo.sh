#!/bin/sh
cd src/org/jakstab/analysis/newIntervals
for i in `find . -name "*.java"`; do echo -ne "$i:\n\t"; cloc --quiet "$i" | tail -n 2 | head -n 1; done; echo -ne "Complete:\n\t"; cloc --quiet . | tail -n 2 | head -n 1

#! /bin/bash

# Tested with TPTP v5.4.0.

# We make two transformations in the FOF problems:
# 1. To transform FOF problems to CNF problems using Otter algorithm.
# 2. To transform FOF problems to CNF problems in Waldmeister format
#    using Otter algorithm.
for file in *.tptp ; do
    tptp2X -tcnf:otter $file
    tptp2X -tcnf:otter -fwaldmeister $file
done

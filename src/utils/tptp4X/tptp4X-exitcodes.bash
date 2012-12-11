#! /bin/bash

# tptp4x from TPTP v5.4.0 yields a failure exit code when it find an
# error.

tptp4X error.tptp

exitcode=$?

if [[ exitcode != 0 ]] ; then
    echo "Exit code from tptp4x after an error: $exitcode"
fi

# tptp4x from TPTP v5.4.0 *does not* yield a failure exit code when it find an
# warning.

tptp4X -w warning.tptp

exitcode=$?

if [[ exitcode != 0 ]] ; then
    echo "Exit code from tptp4x after an warning: $exitcode"
fi

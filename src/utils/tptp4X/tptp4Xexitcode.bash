# tptp4x from TPTP v5.4.0 *does not* yield a failure exit code when it
# find an error.

tptp4X test.tptp

rc=$?
if [[ $rc != 0 ]] ; then
    exit $rc
fi

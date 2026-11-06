#!/bin/bash
# Resumable dep build for the LinkSlope closure: the host kills long-lived lean processes
# (harness restarts under memory pressure), so re-invoke until lake reports success.
cd "$(dirname "$0")"
for i in $(seq 1 12); do
  LEAN_NUM_THREADS=1 lake build Submission.CatalanMeasure.GenD.Signed.Data.Consts.LinkSlope \
    >> /tmp/w4_deps4.log 2>&1
  rc=$?
  echo "=== attempt $i rc=$rc at $(date +%H:%M:%S) ===" >> /tmp/w4_deps4.log
  [ $rc -eq 0 ] && break
  sleep 5
done
echo "LOOP-FINISHED" >> /tmp/w4_deps4.log

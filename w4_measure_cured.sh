#!/bin/bash
# Retry loop: build the cured LinkSlope module, sampling RSS, until lake reports success.
# The host kills long-lived lean processes (harness restarts under pressure), so the only
# way to finish is to re-invoke; lake re-elaborates the module each attempt.
cd "$(dirname "$0")"
for i in $(seq 1 8); do
  t0=$(date +%s)
  ./w4_rss_sample.sh /tmp/w4_cured_rss.txt 'lean .*Consts/LinkSlope.lean' &
  LEAN_NUM_THREADS=1 lake build Submission.CatalanMeasure.GenD.Signed.Data.Consts.LinkSlope >> /tmp/w4_cured_build.log 2>&1
  rc=$?
  t1=$(date +%s)
  echo "=== cured attempt $i rc=$rc wall=$((t1-t0))s ===" >> /tmp/w4_cured_build.log
  [ $rc -eq 0 ] && break
  sleep 3
done
echo "CURED-LOOP-FINISHED" >> /tmp/w4_cured_build.log

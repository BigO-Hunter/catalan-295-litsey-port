#!/bin/bash
# The host SIGTERMs long lean runs; retry the exact peak measurement until one survives.
cd "$(dirname "$0")"
for i in 1 2 3 4; do
  ./measure_peak.sh Submission/CatalanMeasure/GenD/Signed/Data/Consts/LinkSlope.lean > /tmp/w4_cured_peak2.log 2>&1
  if grep -q "exit=0" /tmp/w4_cured_peak2.log; then break; fi
  sleep 2
done
echo PEAK-LOOP-FINISHED >> /tmp/w4_cured_peak2.log

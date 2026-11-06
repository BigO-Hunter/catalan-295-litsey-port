#!/bin/bash
# Append "<epoch> <rss_kb>" samples for the lean process elaborating $2 to $1 every 5 s.
out=$1; pat=$2
while pgrep -f "$pat" > /dev/null; do
  pid=$(pgrep -f "$pat" | head -1)
  rss=$(ps -o rss= -p "$pid" 2>/dev/null | tr -d ' ')
  [ -n "$rss" ] && echo "$(date +%s) $rss" >> "$out"
  sleep 5
done
echo "SAMPLER-DONE" >> "$out"

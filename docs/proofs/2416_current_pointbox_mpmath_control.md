# 2416 — current-source point-box mpmath control

Date: 2026-10-02.

The current 2414 artifact and current evaluator were checked at 5001 uniform
nodes across all four channels.  Stored binary64 operands were converted
exactly to rationals before 90-digit mpmath evaluation.  All 20004 values were
contained by the named four-ULP public hull; there were zero containment
failures and the source hashes matched.

This remains a sampled control, not a full real-domain enclosure proof or a
Lean numeric import.  The producer gate and RH claim remain false.

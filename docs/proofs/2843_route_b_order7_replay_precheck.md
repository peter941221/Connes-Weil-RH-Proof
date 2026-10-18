# 2843 Route B order-7 replay precheck

The exact rational-box replay arithmetic was rerun for cell 4096 at order 7,
using the replay-produced denominator as the reciprocal input. All eight
transition slots satisfy `target_contains_replay` in the Python exact
precheck.

This is a precheck for generating the Lean theorem; it is not itself a Lean
certificate and does not prove the phase-slot membership or global ledger
domination.

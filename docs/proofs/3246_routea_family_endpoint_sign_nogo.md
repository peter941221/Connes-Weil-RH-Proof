# 3246: Direct family endpoint sign no-go

Status
------

The direct endpoint-sign tactic is rejected. No producer_go, SourceRH, or RH
claim follows from this record.

Experiment
----------

The experiment imported the verified 17168 rectangle interface from record
3245 and attempted to prove the single-family inequality

    family 10 rectangle reHi < 0

by fully unfolding the bump interval, phase Taylor rectangle, binary64 owner
coefficient, and complex rectangle multiplication.

Verification result
-------------------

The focused WSL2 ext4 build used Lean 4.30.0 and 10,000,000 heartbeats. Lean
failed with simplifier step-limit exhaustion after about 183 seconds. The
failure is structural: the expression expansion is too large, not evidence
that the mathematical inequality is false.

Decision
--------

Do not raise the simplifier budget or repeat this expansion for all 30
families. The next producer-facing evaluator must preserve cancellation before
the final rectangle multiplication. The intended boundary is:

    coefficient-phase block rectangle
                 |
                 v
    shared positive bump envelope
                 |
                 v
    block physical rectangle

This keeps signed coefficient-phase cancellation inside one object instead of
paying interval widening separately for every family term.

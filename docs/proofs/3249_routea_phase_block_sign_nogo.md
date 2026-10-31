# 3249: Direct phase-block sign expansion no-go

Status
------

The direct phase-block endpoint tactic is rejected. No producer_go, SourceRH,
or RH claim follows from this record.

Experiment
----------

After the exact shared-bump identity of record 3247, the phase aggregate for
families 8 through 29 was expanded directly with norm_num. Both the full
22-family phase rectangle and a five-family subblock exceeded the Lean 4.30.0
simplifier step limit under a 10,000,000-heartbeat focused build.

Decision
--------

The next phase proof must expose precomputed, separately audited local phase
rectangles or coefficient-phase endpoint lemmas. Repeating larger norm_num
expansions is not a viable route. The shared-bump identity remains valid and
is the producer-facing base for those local phase lemmas.

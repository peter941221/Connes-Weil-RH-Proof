# 2385 — shared-geometry 776611 full-grid replay

Date: 2026-10-02.

The shared outward-geometry evaluator completed the 776611-node replay with
16 workers and 20001-node spans.  Its source hash matches the current
evaluator.  The RNDU binary64 roundup of each already-directed term dominates
the original MPFR term accumulator in all four channels.

The rounded-up `corr_D2` reading is `125446.71133496995`.  Reusing the
registered coordinate and mesh-scaled panel prices gives panel/readout ratio
`0.09999966654156531`, still below the pre-registered 0.1 target.  Relative to
2374 the cache widens this channel by about `1.34e-5`; no tightening is being
claimed.

This is a controlled numerical replay, not a producer certificate.  The
directed accumulation theorem, Lean nodewise numerical import, and full
trapezoid certificate remain open; `producer_go` and `rh_claim` stay false.

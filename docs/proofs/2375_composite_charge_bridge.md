# 2375 — composite coordinate-charge bridge

Date: 2026-10-02.

The Lean theorem `compositeNodeUpper_le_of_nodewise_coordinate_charge2359`
now lifts a uniform nodewise coordinate error into the exact composite-node
upper with charge `(cells : ℝ) * step * charge`.  The accompanying ledger
re-reads the 776611-node same-owner run, scales the 2371 coordinate charge by
the measured coordinate-gap ratio, and scales the 2348 panel remainder by the
exact squared mesh ratio.

This is an interface price, not a certificate.  The numeric nodewise import,
directed accumulation theorem, and trapezoid remainder theorem remain open;
the artifact therefore keeps `producer_go: false` and `rh_claim: false`.

# 2277 - Cancellation-preserving corrected-owner screen

Date: 2026-09-30

Result: forming the corrected width-a^2 physical families before taking absolute values reduces the centered-strip screen to B = 337039.47691484215 on the 240001-node refinement. This is 28.2x below the frozen strip cap 9506275.102584327. The same elementary three-integration-by-parts tail price is 1.285918889357026e25, so hgap remains open.

## Scope

The previous 2276 method took absolute values before summing the 30 family terms. This record first forms the physical functions and derivatives with radius r_j = a_j^2, then integrates their absolute values. The 2249 coefficients remain frozen; no new solve is performed.

The third derivative includes the bump term itself: phi3/phi = L3 + 3 L1 L2 + L1^3, followed by the phase terms. The first draft omitted this term and was corrected before the final reading.

## Numerical decision

The binding row is sigma = -1/2 in both grids. The 120001 to 240001 refinement changes B by 1.30e-12. The refined norms are base M0 2.68671432965, base D2 8606.21439765, base D3 631832.429861, corr M0 90.7878822538, corr D2 125446.711322, corr D3 5304345.60051.

The refined strip reading is a numerical screen, not a directed enclosure. The tail price improves the 2276 absolute-family price by about 16 orders of magnitude, but is still 1.2859e18 times the 1e7 hgap budget. This rejects the elementary tail method, not the true tail.

## Decision

1. Re-running the old width-a norms is rejected. Correct physical profiles and cancellation matter.

2. Reusing the same elementary tail envelope is rejected. The next tail attempt must retain oscillation, signed prime-kernel cancellation, or use a direct-difference construction.

3. hstrip and hgap remain explicit. No Lean supplier, producer GO, or RH claim is added.

Reproduction: python3 scripts/routea_corrected_cancellation_screen_2277.py --nodes 120001 --refine; python3 scripts/routea_corrected_cancellation_selftest_2277.py. The artifact records input hashes and the six focused controls pass.

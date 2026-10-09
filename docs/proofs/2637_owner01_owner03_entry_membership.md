Record 2637: owner-01 and owner-03 entry membership certificates (K01 + K03 panel families and probes)
Date: 2026-10-10

Result

Positive at single-entry scope, twice over. The full K01 owner-01 stack
(541 family modules, edge pair ScalarEdge2620K01 / ActualEdge2620K01,
probe `ZProbe2628K01.lean`, 213 theorems) compiled green in ONE xargs
batch: 544 targets, 413 s wall, 4278 jobs, 1088 artifacts (2 per module),
full error list empty, `uses sorry` zero. The full K03 owner-03 stack
(544 targets, same shape) compiled green in its own batch under the same
triple file-level acceptance. Deliverables per owner:
`actualOwnerMomentMatrix2351_entry0{1,3}_mem2628` — the 2597 entry-(d,d)
analytic interval contains the owner moment integral in all four
coordinates — plus `actualFullRealError2628K0{1,3}`, the four support
theorems, the chunked replay chain, and the extraction interfaces
`entry01Interval2628` / `entry03Interval2628` + kernel-rfl bridges.
Numerics: owner 01 edge charge 3/10^69, eps 3150532344482211/10^154;
owner 03 edge charge 4/10^69. Edge bounds were priced by the exact
single-digit formula (minimal k with prod*10^k >= 1, ceiling digit),
whose owners-0/4 regression gate was re-verified bitwise at generation
time.

Scope

Fourth and fifth of the 30 diagonal entries (after d = 0, 2, 4). The
succ-chain hsucc bridge — `(analyticMomentInterval2597 d d) =
(analyticMomentInterval2597 (Fin.succ^d 0) (Fin.succ^d 0)) := rfl` — is
now build-verified at depths 1, 2, and 4; the parameterized generator has
produced four consecutive green stacks with zero probe-side defects across
owners 0, 1, 2, 3 (the K04 original remains the fifth). Partition
assembly, static consumer, complex scalar engine, Producer GO, SourceRH,
and RH all remain open. No route ruling changed.

Pipeline notes

- d=1 is the shallowest owners >= 1 case (`(Fin.succ 0)`, one peel);
  d=3 the first odd depth beyond the hand-built K04. Both closed by
  kernel rfl exactly as at d=2 — the succ-chain shape is depth-uniform.
- Mechanical preflight (token identity, hsucc shape, paren-insensitive
  four-bridge value identity) passed first-try for both probes; the
  paren-insensitivity law from record 2636 (AGENTS 2ce) is now the
  default checker form and produced zero false alarms.
- The edge-bound decade law (AGENTS 2ce) was exercised again: the naive
  `while prod > 10^-k` form would have priced owners 1/3 one decade low;
  the regression gate caught nothing new because the fix landed in 2636.

Next obligations

1. Record 2638: the project-local `Matrix.cons_val` family (indices
   5-29) plus the first owners >= 5 validation at d = 5 (stack already
   generated and prefetched; smoke of the family module passed).
2. Remaining 24 diagonal entries (d = 6..29) via the same parameterized
   pipeline, now unblocked at every index.
3. Partition assembly closure -> static consumer -> complex scalar
   engine (record 2624 GO route).

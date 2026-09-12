# Record 1353 - C6 placement audit: the count->energy step of (★) fails, and the NLLE spec must be repaired

```text
+---------------------------------------------------------------------+
| CLASS: CORRECTION AUDIT (paper-only; NM-loop 1227 read-only lane).   |
| Supersedes record 1346's C6 GRADING ("explicitness, not existence")  |
| and its "(★) is O(1)-robust" claim. Touches NO committed algebra:    |
| the (★) <=> gate equivalence (1345 s1, B0b-d767a1d both legs) is     |
| untouched, and record 1348's in-flight A1b branch is untouched.      |
| Law 42 not engaged: no preregistered branch is adjudicated here;     |
| the Shannon-number smoke ran with its prediction locked in-script    |
| BEFORE execution (1353_c6_shannon_smoke.py header). MODEL grade      |
| throughout; certifies nothing; RH NOT claimed.                       |
| NUMBERING: this record was drafted as "1349" mid-session; 1349 is    |
| RESERVED by the 1350-1352 parallel wave for the batch-1548 A1b       |
| verdict, so the audit takes number 1353 (AGENTS 7c(74) born here).   |
+---------------------------------------------------------------------+
```

## 0. What this is / why / how (zero-base)

What: record 1346 registered N1's bone census as "C7 is the ONLY missing
bone; C6 (the explicit frame lower bound converting 'N_on nodes present'
into 'gain >= A * energy') is a smaller UNCERTAINTY bone - explicitness,
not existence - and the structural conclusion (★) is O(1)-robust."
This audit tests that load-bearing sentence. It fails: the conversion
step is placement-sensitive, the adversary controls placement, and the
degradation is two orders of magnitude against a requirement of a
factor of at most 2. C6 is therefore a SECOND missing theorem, not a
constant.

Why it matters: the N1 lane's whole value proposition (1345) is "a
single missing input named NLLE". If the census is wrong, (a) the H1
target spec (1346 s4) and H2 conditional theorem (1346 s6) as currently
worded carry a hole and must NOT be written up as paper-grade artifacts;
(b) the assault is even colder than COLD-STRUCTURAL (the missing input
is stronger); (c) any future funding decision built on "one bone" is
mispriced. Cheap death before line funding is exactly what 1340's
Stage-0 audit and 1341's dissolution were for.

How: (1) reconstruct the counting step of (★) and name its hidden
uniformity assumption (s2); (2) exhibit the adversary configuration:
cluster the ON-LINE nodes sub-Nyquist-tight, spread the off-line ones -
while passing the f < 1/3 count threshold with room to spare (s3);
(3) measure the information asymmetry with the Slepian/prolate
time-bandwidth operator (a classical ESTIMATE object; using it as an
estimate does not reopen the dead prolate producer route 1055) -
prediction committed in-script before execution (s4, with the smoke
digits); (5) state the repaired spec NLLE-v2 (s5); (6) rails (s7).

## 1. The load-bearing sentence under audit

```text
1346:50-52  "Answer to the owner's first question: C7 is the only
            MISSING bone; C6 is a second, smaller UNCERTAINTY bone
            (explicitness, not existence); C1-C5 are mechanical."
1346:83-87  "(**) treats per-node energies at face value (density
            ansatz). The rigorous version needs the explicit frame
            lower bound ... A is where C6 lives. Structural conclusion
            (**) is O(1)-robust; the exact threshold f* is
            C6-dependent."
```

The counting contest it rests on (1346:78-80):

```text
(**)  contest holds in the window  <=>  N_on >= e^{2 sigma delta} * N_off
      => f = N_off/(N_on+N_off) < 1/2 (delta->0),  < 1/3 uniform
```

## 2. What (**) silently assumes: per-node COUNT = per-node INFORMATION

The step |G(w)G(-w)| <= e^{2 sigma delta} * (on-line energy scale at the
same height) is a POINTWISE comparison at height-matched nodes. Summing
it over nodes turns "energy scale" into "the on-line sampling sum
E_on = sum_{on-line} |G(iy_j)|^2". The conversion E_on >= A * E_window
is valid with A O(1) ONLY IF the on-line nodes in the window are not
confined to a region smaller than their Nyquist footprint. Nothing in
the counting statement enforces that. The adversary chooses the zero
configuration (conditional on consistency with known theorems); we
choose G. The two-constant theorem for band-limited functions says the
adversary's clustering is nearly FREE: G can be suppressed on a set of
width L at information cost sigma*L/pi per window - the Shannon number
N_eff = sigma * L / pi.

## 3. The configuration: cluster-vs-spread, passing f < 1/3

Take T = 3e12 (above the verified base, C5, `1345`). Mean zero spacing
2pi/log(T/2pi) = 6.2832/26.892 = 0.2336. Two committed windows:

| class | sigma | W = pi/sigma | mean count | adversary plan |
|---|---|---|---|---|
| full prime-free | log 2 = 0.6931 | 4.5324 | ~19 | 13 on-line crammed into J (width 0.05), 6 off-line spread over I\J |
| realized (G7) | 0.3365736 | 9.3340 | ~40 | 27 on-line in J, 13 off-line spread |

Checks against the 1346 s3 adversary table (same standards as
configuration A):
- count test: 13 >= 2*6 (27 >= 2*13) - passes with room; f = 0.316 /
  0.325 < 1/3. (**) as a COUNTING statement is satisfied.
- cluster spacing 0.05/13 = 0.0038 / 0.05/27 = 0.0019 = 1.6% / 0.8% of
  mean spacing - blocked by nothing: no unconditional separation floor
  exists (1346:105), and even a hypothetical floor c/log^2 T = 0.0012
  does not forbid it (1346:106 applied to placement, not window
  occupancy).
- window occupancy ~19/40 vs mean 19.4/39.9: SELBERG-type underdensity,
  no local density lower bound available at fixed window width.
- multiplicity, zero-free region, large sieve, pair correlation: all
  silent exactly as in 1346 s3 (this configuration is strictly weaker
  than configuration A's requirements).

So the configuration is consistent with every located unconditional
theorem, satisfies (**) at face value - and, s4, defeats the energy
step by two orders.

## 4. Measured information asymmetry (smoke, MODEL; prediction pre-locked in-script)

Object: time-limiting + band-limiting (Slepian/prolate) operator on an
interval of length L, kernel k(x-y) = sin(sigma(x-y))/(pi(x-y)),
midpoint discretization n = 4000. Its eigenvalues are the per-interval
sampling information; lambda_1 = max_{||G||=1} energy fraction
concentrated on that interval; count(lambda > 1/2) = N_eff. Spectrum is
translation-invariant in L (sinc kernel), so [0,L] represents all
interval positions.

```text
== sigma=0.693147  window W=pi/sigma=4.5324   pred N_eff(J)=0.011032
   J (cluster)    L=  0.0500  lambda_1=0.01103  count(ev>0.5)=0   lam1/pred=1.000
   I\J (spread)   L=  4.4824  lambda_1=0.77842  count(ev>0.5)=1   pred N_eff=0.9890
   I (window)     L=  4.5324  lambda_1=0.78337  count(ev>1/2)=1

== sigma=0.336574  window W=pi/sigma=9.3340   pred N_eff(J)=0.005357
   J (cluster)    L=  0.0500  lambda_1=0.00536  count(ev>0.5)=0   lam1/pred=1.000
   I\J (spread)   L=  9.2840  lambda_1=0.78098  count(ev>0.5)=1   pred N_eff=0.9946
   I (window)     L=  9.3340  lambda_1=0.78337  count(ev>0.5)=1
```

Readout: the cluster's total information ceiling lambda_1(J) =
sigma|J|/pi EXACTLY at this scale (lam1/pred = 1.000 - the single-
eigenvalue trace limit), while the spread set keeps lambda_1 ~ 0.78.
Energy ratio spread:cluster = 70.6x (full class) / 145.7x (realized).
The contest must survive the WORST admissible G; for G = the top
prolate mode of I\J (mass 0.78 on the spread set, <= 0.011 in J), the
per-node energy comparison that (**) needs fails by ~10^1-10^2 against
the allowed factor e^{2 sigma delta} <= 2. The count->energy step is
NOT O(1)-robust; it is placement-dominated.

Normalization note (registered, not papered over): (**) is written for
POINT samples |G(y_j)|^2; this smoke measures L^2-interval energies.
For near-uniform node sets the conversion is a local-spacing
renormalization (factor ~ average spacing / set spacing on each side),
which here is the same 0.2336/0.0019-vs-0.2336/0.73 - it changes the
numbers, not the two-order margin, and it is precisely the kind of
"explicitness" 1346 assumed free. A point-node version of this exact
smoke is the named first step of any official C6 work.

## 5. Repaired spec - NLLE-v2

```text
+---------------------------------------------------------------------+
| NLLE-v2 (near-line local exclusion, distribution-aware):             |
|   There exist explicit eps(T) > 0, spread parameter nu > 0 and T0    |
|   such that for every Nyquist window I at height >= T0:              |
|   (i)  COUNT: the multiplicity-weighted near-line (|beta-1/2| <      |
|        eps) zero count is < f* (v1 said 1/3; v2: f* = f*(A) is NOT   |
|        determined by counts alone - see s6), AND                     |
|   (ii) SPREAD: the ON-LINE zeros in I occupy at least nu*N_eff(J)    |
|        of the prolate information of every sub-window J in which     |
|        they lie (i.e. the on-line set must not be clusterable:       |
|        sum_{on-line} |G(iy_j)|^2 >= A*energy with A explicit).       |
|   Equivalently: NLLE-v1 is a COROLLARY of NLLE-v2, not the whole     |
|   statement. NLLE-v2 <=> RH via the same committed legs (the         |
|   equivalence (★)<=>gate never used counting anywhere; only the      |
|   assault's reduction to a hunt-able theorem did).                   |
+---------------------------------------------------------------------+
```

## 6. Corrections to committed artifacts (pointers added 1353)

| artifact | claim as committed | status after 1353 |
|---|---|---|
| 1346 s1 | "C7 is the only MISSING bone; C6 = explicitness, not existence" | WRONG as a census: C6 = second missing theorem (a distribution/uniform-spread input with no unconditional instance located) |
| 1346 s2 | "(★) is O(1)-robust" | FAILS - placement attack, s3-s4 |
| 1346 s4 | NLLE spec f<1/3, count-only | SUPERSEDED by NLLE-v2 (s5); v1 is the necessary count shadow of v2 |
| 1346 s6 | H1/H2 harvest as worded | H1 must adopt v2; H2's hypothesis strengthens to "majority-or-clustered configuration" - the theorem remains WARM and PROOF-ABLE, its statement gets sharper, its crack gets smaller in scope but colder in reach |
| 1345 s2 / registry | "isolates a single missing input named NLLE" | single missing input -> single missing THEOREM WITH TWO LIMBS (count + spread); the lossless non-circular equivalence itself is untouched |
| N1 funding state | PENDING, COLD-STRUCTURAL | COLD-STRUCTURAL (colder; the s3b non-transfer rails continue to apply unchanged) |
| 1350 s2-s3 (harvest assembly) | H2 legs L3/L4 carry C6 "as estimation leg" | C6 re-graded (two-limb hypothesis); L3 as drafted is not dischargeable from a count-only NLLE - pointer added; the VERBATIM-assembly discipline itself was sound and caught nothing wrongly |
| 1351 (brick design) | B2 injects C6 for windowwise reading; B1+B4 C6-free | CONFIRMED + strengthened: B2's hypothesis must be NLLE-v2, not a frame-constant; iff core untouched by 1353 - pointer added |

## 7. Rails (what 1353 does NOT say)

- It does NOT refute (★) <=> gate: that is algebra on committed
  dictionary terms (1345 s1 re-verified; B0b both legs). (★) as a
  restatement of the gate is exact. What fails is the FURTHER
  reduction "(★) follows from a local COUNTING theorem" - the
  hunt-ability claim.
- It does NOT exhibit a counterexample to the gate: no off-line zeros
  exist under RH, and the adversary configuration is a hypothetical
  compatible-with-known-theorems, not a construction.
- It does NOT reopen the prolate producer route: 1055's DEAD verdict
  bars the asymptotic family as a theorem target; using the Slepian
  time-bandwidth operator as a MODEL ESTIMATE of information content
  is a different act, and no 1353 statement consumes prolate
  asymptotics as a proof step.
- The smoke is n=4000 midpoint-grid numerics at MODEL grade: a
  rig-confirmation of a classical fact (N_eff = sigma*L/pi), not
  evidence about zeta zeros' actual distribution.
- 1348's A1b ladder is on the SPACE axis; 1353 audits the TIME axis.
  No interaction; the alpha bit is still the next mainline input, and
  batch 1548's branch rule stands exactly as committed.

## 8. Artifacts

- docs/proofs/1353_c6_placement_audit_and_nlle_spec_repair.md (this record)
- docs/proofs/1353_c6_shannon_smoke.py (MODEL smoke, prediction
  pre-locked in header)
- pointers added to 1345 / 1346 / 1350 / 1351 headers (no body edits
  to committed adjudications; 1351's iff-core design CONFIRMED, its
  B2 windowwise leg re-specced)
- AGENTS.md 7c(73) banked: "counting-type local conditions on
  band-limited samplers must pass the Shannon-number placement audit
  (per-node count != per-node information; adversary controls
  placement) before any 'O(1)-robust' or threshold-f* claim is made"
- AGENTS.md 7c(74) banked: record-number allocation checks git HEAD
  AND the MEMORY.MD tail for reserved future numbers; re-read pointer
  edits after any bulk sed

## 9. Consequences for the portfolio (1344 B0d-FULL charter lens)

1. A1b (P1) unchanged - in flight, selects the next space-side prereg.
2. N1 assault (PENDING): re-graded colder; do NOT re-fund on the old
   census. Its harvest H1/H2 (now v2-worded) remains the WARM product.
3. A3 audit (P2, task #8) moves UP in the queue: it is now the
   cheapest remaining lane whose verdict is decisive either way
   (2408.15135's operator-positive-side restatement of the same gate).
4. The 1346 s2 factor-4 cancellation result (per-zero balance,
   quartet factor 4) survives untouched - it is algebra at the
   height-matched-node level, which is exactly where 1353's attack
   starts FROM, not where it lands.

## 10. Next steps

1. Owner ruling: accept the census correction (recorded either way in
   this file) and re-grade N1's registry line to the two-limb missing
   theorem.
2. Optional 10-line follow-up: point-node version of the smoke (Gram
   of reproducing kernels at cluster vs spread nodes; smallest vs
   largest eigenvalue) to close the normalization note in s4 - MODEL
   grade, same non-claims.
3. A3 audit of arXiv:2408.15135 v17 as next paper-only action.

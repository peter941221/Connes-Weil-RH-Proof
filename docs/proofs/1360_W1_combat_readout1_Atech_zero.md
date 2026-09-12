# Record 1360 (W1 READOUT #1) - S(T) CLOSED at T>=e; occupancy band VERIFIED; A_tech = 0 (locked OUTCOME 3 fires); target re-specified as correlation theorem A2

```text
+---------------------------------------------------------------------+
| Wave W1 of 1358 (owner "继续打。打到证明RH"). Readout 1 of the       |
| A_tech combat inventory. Outcome bands were locked at 1358 s2       |
| BEFORE these reads (law-42). All constants below parsed from        |
| primary text this session (constants-are-DATA). MODEL where noted;  |
| RH NOT claimed.                                                     |
+---------------------------------------------------------------------+
```

## 1. S(T): the #9 "OPEN T-range" column CLOSES (this constant chain)

Primary parse (verbatim abstract, https://arxiv.org/abs/1208.5846 ,
Trudgian 2012): |S(T)| <= **0.111 log T + 0.275 loglog T + 2.450**,
"which is valid for **all T >= e**".

Newer chain located, constants pending integration: arXiv:2412.15470
(Bellotti-Wong, v2 2025-07-07, improving Hasanalizade-Shen-Wong) -
abstract confirms improvement of the S(T) and zero-counting estimates;
full numeric parse queued (same column, next readout). Our locked
table constants (0.112/0.278/2.51 from 1345:173) are superseded in
coefficient AND closed in range by 1208.5846; kept on record for the
falsifier-archive rule.

## 2. Occupancy band: PLACEHOLDER -> DERIVED (with the closed S(T))

1346-window arithmetic, one window W = pi/log2 = 4.5324, mean count
(W/2pi)log(T/2pi) = 0.7213 logT - 1.155; two-endpoint deviation
<= 2(0.111 logT + 0.275 loglogT + 2.450) + O(1):

    band = [0.4993 logT - O(loglog) , 0.9433 logT + O(loglog)]

matching the 1346:112 placeholder [0.50, 0.94]*logT to first order -
the placeholder was implicitly computed with these constants and is
now an arithmetic corollary of a primary-sourced, globally-valid
S(T) bound. Status edit: band VERIFIED-MODEL (low-T floors omitted
honestly; the O(loglog) terms matter only near T ~ e^40).

## 3. Spread inventory: A_tech = 0 -> locked OUTCOME 3 fires

What would give A > 0: ANY unconditional positive lower bound, for
distinct zero ordinates, of a normalized gap - none exists in the
located sources. Evidence rows:

1. Multiplicity is NOT excluded: "There are two possible types of
   close pairs of zeros: pairs arising from a multiple zero and
   close [distinct pairs]" and "we cannot guarantee that both of
   these distinct zeros are simple. Furthermore, our method does not
   produce a positive proportion of gaps" (Bui et al. 2023, Small
   gaps and small spacings between zeta zeros,
   https://par.nsf.gov/servlets/purl/10506629 :136 region). The
   small-gap literature runs the OTHER way (existence of small gaps).
2. Under RH no uniform normalized lower bound on consecutive gaps is
   known either (GGM-type results give upper-direction statements);
   stated as located-source absence, not as a no-go theorem.
3. No positive proportion of simplicity even unconditionally
   (row-1 quote); the locked m(rho) <= 10 logT cap (1345:185) bounds
   the weight of a cluster, not its existence.

Consequence per the pre-locked table (1358 s2): OUTCOME 3 - "the
A-route main line becomes proving TARGET-A as a new theorem; W1
output = its precise statement + the exact 1/log-scale where it must
bite." Delivered next section - with a correction the readout forced.

## 4. Correction of the battle target (fired by the simplicity row)

The 1358 naive form "exists A0 > 0: every window has spread ratio
>= A0" is the WRONG target: it silently demands excluding multiple
zeros (a separate open problem). The contest-safe condition B4.1 +
factor-2 budget is the JOINT window inequality

```text
+---------------------------------------------------------------------+
| TARGET-A2 (the wall, correlation form): exists explicit T1 >= 3e12  |
| such that for EVERY one-window I at height >= T1, with A(I) the     |
| frame ratio of DISTINCT on-line ordinates in I (multiplicity caps   |
| it, m <= 10 logT, 1345:185):                                        |
|       N_off-nearline(I)  <  f*(A(I)) * N(I),    f*(A) = A/(A+2),   |
| i.e. clustering of the line and near-line off-line majority cannot  |
| coexist in the same window.                                         |
| (A=0 gives f*(0) = 0: a fully clustered window forces ZERO near-    |
| line off-line zeros - the sharp shape of the repulsion we lack.)    |
| A2 discharges (via 1356-B4 + the window brick B2/B3) => the gate   |
| => RH; and RH => A2 is the trivial reading (N_off = 0). So A2 is   |
| the RH-equivalent statement recast as ONE correlation theorem.      |
+---------------------------------------------------------------------+
```

This is the precise, constant-bearing enemy. The scale where it must
bite: window W = pi/log2 ~ 4.53 and the sub-window J scale where the
prolate ceiling collapses A (1353: J ~ 0.05, A ~ 1/70).

## 5. W1 wave-2 queue (attack continues; no menu)

1. Parse 2412.15470 full constants (S(T), N(T) error) -> band tighten.
2. Correlation-mechanism scan for A2: the ONLY located theorem
   family relating one zero's position to others' densities is
   Deuring-Heilbronn-type repulsion (and Benli 2410.06082 explicit
   DH under Landau-Siegel) - audit whether any DH variant takes a
   CLUSTER (not a single near-1 zero) as hypothesis and outputs a
   local exclusion near 1/2. This is the highest-leverage read left.
3. Half-isolation family (2206.11729) re-screen under the A2 lens:
   does it say anything about A(I) vs N_off correlation? (1347
   wave-1 screened it for count-locality only - different question.)
4. W0 continues (task #14): Connes number-field sections Q1-Q3.

Waypoint, not result. The stop word is unchanged: a Lean certificate
at the gate. Current distance: OUTCOME 3 confirmed, target re-locked
as A2, enemy now has a formula and a scale; the next honest distance
number comes from queue item 2 (does ANY mechanism correlate cluster
and off-line count?).

# 043 — Route map to RH after 1629 (redrawn)

Date: 2026-09-18. Supersedes 042 as the *navigation* document (042 keeps the
diagonal-leg operator-bridge audit; nothing in 042 is withdrawn).

Read with: 012 (G8 same-owner readback — the mainline face), 016
(`EndpointMass` weight object), the record set `docs/proofs/1586`–`1629`, and
the laws F8–F40 in the live-state card.

## 1. The only sanctioned chain to RH

```text
   (Hypothesis) off-line zero of zeta
        |
        |  FORMAL, machine-checked
        v
   qw(g) < 0        [the sign of the Weil quadratic form on the off-line test g]
        |
        |  THE GATE:  for all g,  0 <= qw(g)          <-- one inequality, one object
        |  machine-checked equivalence with SourceRH (1343/B0b, 1416, law F20):
        |  proving the gate IS proving RH's analytic statement
        v
   RH  (no off-line zeros)
```

Everything below is *one* decomposition of the gate. The gate itself is not
negotiable and not partially provable: it is a single universal inequality.
Every route in this map is a route to that inequality.

## 2. Anatomy of the gate (mainline G8, map 012)

```text
   GATE  0 <= qw(g) for all g
     |
     |  SAME-OWNER READBACK  (G8SameOwnerReadbackData)
     v
   (star)   P C P  is Hilbert-Schmidt          <-- ONE square-sum, finite
     |
     |  EXACT residual identity (1586-1589, machine-checked)
     v
   residual^2  =  StripDensity(Lambda)         <-- closed to finiteness (1625),
              +  SUM_i dist(h_i, carrier)^2       square-sum content OPEN
```

Two Windows of Obligation hang off the same skeleton:

```text
   WO-S  (source leg)   : the S3 estimate, filed in FIVE equivalent forms (1620)
                          ambient P C P / source gate J^dag C J / source input C J /
                          Hardy-compressed E Q E C J / source projection P C J
                          -- "any further rearrangement is a rename" (1620)
   WO-B  (boundary leg) : the B4 wide Hardy-support certificate
                          = per-column scalar form e^{2 pi I (log lambda'') xi} m psi in H^2(C_+)
                          -- support algebra provably insufficient (1628 sec 3, 1629 sec 4)
   BASE  (shared)       : carrier != {0}, consumed as (hsource : exists y, y != 0)
                          -- a def, NEVER a theorem (law F33)
```

## 3. The five open bones, priced

```text
+---------------------+--------------------------------------------------------+------------------+
| bone                | state                                                  | handle           |
+---------------------+--------------------------------------------------------+------------------+
| (star) / WO-S       | OPEN; five equivalent forms; no further rearrangement  | needs the S3     |
|                     | available                                              | estimate itself  |
| StripDensity(L)     | FINITENESS closed at Tr(P M_Delta P) <= Lambda (1625); | missing layer:   |
|                     | the square-sum CONTENT open; brick specified           | basis-to-measure |
|                     |                                                        | trace identity   |
| EndpointMass(eps)   | OPEN (map 016 weight object)                           | scalar/weight    |
| T1                  | OPEN (transport to the doubled-shift pair)             | pairing          |
| carrier base        | OPEN; see sec 4                                        | criterion or     |
|                     |                                                        | witness          |
| WO-B / B4           | OPEN; premise = cancellation                           | per-column psi   |
+---------------------+--------------------------------------------------------+------------------+
```

## 4. The base after 1629: the single point of failure

The base is the same object in four vocabularies (all committed):

```text
   carrier(lambda) != {0}
     <=>  exists phi != 0 in H^2(C_+),  m phi in H^2(C_-)            (1003/T4 route)
     <=>  exists entire W != 0:  W/A in H^2(C_+), W/B in H^2(C_-)     (de Branges pattern, 1626)
     <=>  (T')  V_arch(1) != {0}  in committed vocabulary            (1627, elementary face)
     <=>  TOEPLITZ:  exists H in H^2(C_+), H != 0, with
          e^{4 pi I (log lambda) xi} m(-xi) H(xi) in H^2(C_-)         (1629, sec 3, model-checked)
```

What is *known* about it:

```text
+---------------------------------------+--------------------------------------------------+
| proved / committed                    | refuted                                          |
+---------------------------------------+--------------------------------------------------+
| scale monotonicity: nonemptiness      | no witness of finite exponential type (1627)     |
|   propagates downward (1626, Lean)    | no construction of infinite type (1628 sec 2)    |
| window witnesses transport in (1628)  | every classical criterion inapplicable:          |
| model m = 1:  nontrivial iff lambda<1 |   m not inner, not in N, gamma not increasing    |
|   (1627; re-derived 1629 sec 3)       |   (1629 sec 2, law F40)                          |
+---------------------------------------+--------------------------------------------------+
```

The honest reading: **no theorem decides the base**; it is a Hardy-only
phenomenon (`H² \ N⁺`), and both model computations that exist (m ≡ 1;
the shortness diagnostic of 1629 §3) suggest the trivial/benign regime, while
nothing constructs a witness. 1628's "one decisive number `D⁺_BM`" is
withdrawn; the remaining candidate criterion is the *big* multiplier theorem
(Hartmann–Mitkovsky §8, Thm 8.5), whose statement is not yet retrieved.

## 5. Decision tree — the four ways forward

```text
                        [BASE: carrier != {0} ?]
                                  |
        +-------------------------+--------------------------+
        |                         |                          |
   (B1) TRUE                 (B2) FALSE                 (B3) BYPASS
        |                         |                          |
  a witness exists          no witness exists;         re-decompose the gate
  (infinite type:           every classical               so that the residual
  Gamma-factor/prolate      mechanism fails too         chain uses a PROVABLY
  class; or a new           |                            nonempty object and
  criterion for the         |                            pays the difference as
  super-linear-phase        STOP the G8 lane;            an error term
  symbol)                   re-decompose (B3)            (cost: new estimates,
        |                   or attack the gate            not a new existence)
        |                   directly
        v                         v                            v
  WO-S/WO-B become          the decomposition is         gate attacked on a
  provable-by-criterion     void, not the gate           different skeleton
        |                         |                            |
        +------------+------------+--------------+-------------+
                     |                           |
                     v                           v
              RH via the tower            (B4) GATE-DIRECT
                                           prove 0 <= qw(g) by the classical
                                           Weil route with NO G8 decomposition
                                           (cost: the original hard problem;
                                            only sensible if B2 refutes G8)
```

Cost ordering (what to spend next, in order):

```text
+----+------------------------------------------------------------+-----------+---------------------+
| #  | action                                                     | cost      | buys                |
+----+------------------------------------------------------------+-----------+---------------------+
| 1  | retrieve MP 2010 (Invent. Math. 180) Thm 8.5 full statement | 1 pass    | a criterion, or     |
|    | + the Sigma(gamma)/I_n definition (8.2), audit its class    |           | definitive closure  |
|    | against m (law F40)                                        |           | of the criterion    |
|    |                                                            |           | route               |
| 2  | write out psi = F^{-1} v for one committed column and test  | 1 brick   | decides WO-B's      |
|    | the B4-scalar membership numerically                        |           | premise on one case |
| 3  | StripDensity square-sum content: land the missing           | 1 brick   | closes one of the   |
|    | basis-to-measure trace identity (specified in 1625)         |           | two residual terms  |
| 4  | probe the Toeplitz kernel numerically for the real m        | 1 rig     | evidence for B1/B2  |
|    | (finite-section / discretized model-space probe)            |           | before theorem work |
| 5  | re-decomposition study: which provably nonempty subspace    | 1 record  | insurance if B2     |
|    | can replace the carrier (B3)                                |           |                     |
+----+------------------------------------------------------------+-----------+---------------------+
```

## 6. Guardrails carried forward

```text
F33  base existence is a HYPOTHESIS — never re-file it as a theorem.
F35  a tree keyword may name a different object than the source's keyword.
F36  no winding/index theory for super-linear phases.
F37  the carrier is a CONJUNCTION of two half-line conditions (scale-dependent).
F38  audit cited criteria's HYPOTHESES against the actual symbol.
F39  check growth constants numerically at one point (pi^{s/2} bookkeeping).
F40  audit the criterion's MODEL CLASS, not only the phase hypotheses:
     a node sequence is not a symbol.
Stop word: a gate certificate, or a proved refutation of the base.
```

## 7. One-line status

Tower formal; gate = `0 ≤ qw(g)` = `(★)` = `P C P` HS; residual skeleton exact
and closed except `StripDensity` content and the carrier distances; both WO legs
rest on a base that 1629 places outside every classical criterion. RH not
claimed; no gap premise introduced.
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

The honest reading: **no theorem decides the base**.  The phrase "Hardy-only
(`H² \ N⁺`)" carried by 1629 §3 is retracted in 1630 §6 (Erratum A) - it is
vacuous, because `H^p ⊂ N⁺` for every `p` and `N⁺ ∩ L² = H²` (Smirnov), so the
`p = 2` case *is* the Hardy kernel and needs no exclusion; what survives of the
phrase is the *correct* content that the base is the `p = 2` endpoint of the
`N_p` scale (law F42).  Model computations: `m ≡ 1` gives nontrivial iff
`λ < 1`; the 1630 §11 finite-section probe shows the real symbol has
`sigma_min(K)` saturating in `K` and decaying in `λ` (`0.4125, 0.0682, 0.0260,
2.99e-6` at `λ = 1, 1/2, 1/e, 0.1`), i.e. the base is approximable by
finite-type data but not attained by it, while nothing constructs an
infinite-type witness. 1628's "one decisive number `D⁺_BM`" is withdrawn.  The
big multiplier theorem (MP 2010, Thm 8.5) is now retrieved *and* audited
(1630 §2, §4): its hypotheses put it outside our symbol's class at `p = 2`
(`l ≳ d` against our `d = 0`, and `p < 1` against `p = 2`), so the criterion
route to the base is closed for the retrieved theorem, not for the base.

**The inventory (1631).**  "No theorem decides the base" is now a 15-row
checklist with named sources rather than an assertion: three tools apply as
stated (MP 2010 Thm A(ii) + Corollary at `p < 1/2`; §4.1's little-multiplier
proposition with the `d = 0` transfer gap; the maximal-vector structure theorem
of Câmara–Partington), six are out of class with one named failing hypothesis
each (Thm B; §5.1's big multiplier — `γ` of bounded variation and `γ′` bounded
below; the "crucial part" sub-problem `h̃′ ≲ 1`; the BM density criterion,
which needs a meromorphic-inner symbol; the classical `|Ψ′| ≲ 1` multiplier;
de Branges' classical machinery, dead because `A` is not Hermite–Biehler), and
the target is MP 2010 (1.6)'s Hardy clause at `p = 2`.  The five open questions
(`Q1` inner-vs-meromorphic `Θ`; `Q2` `e^h ∈ L¹(ℝ)` vs `L²(ℝ)`; `Q3` the joint
`h̃` ceiling; `Q4` transfer to `d = 0`; `Q5` removability of the `ε`-gap) and
the five retrieval targets are in
[1631](../proofs/1631_base_weapon_inventory_and_erratum_c.md) §8.

Two quantitative facts from 1631 that bound the route: the committed phase is
`ψ(x) ~ +2πx log|x|` with `|γ′| ~ 2π log|x|` (logarithmic, *below* every
polynomial — hence inside the survey's generalized multiplier form, see the flag
in 1631 §8), and the two growth budgets differ by one power: an `L¹(dΠ)`
conjugate can carry exponent `< 1`, an inner-function argument can carry `< 2`,
while our phase sits at `1 + o(1)`.  So the growth must come from `Θ` (the
measure side) and the criterion is *not* obstructed by a crude growth count —
the obstruction, if any, is the joint density/atoms constraint (`Q3`).  Also
recorded: **Erratum C** — 1630 §8's two-tap form reads `w(−·) * h(· + c) = w * g`
with `c = 2 log λ`, not `w(· − ã/2π) * h = w * g` (three checks in 1631 §7).

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

**1630 execution (the whole batch of the table above is DONE).**  Records:
1630 (`docs/proofs/1630_mp2010_primary_source_bm_interval_and_shortness_direction.md`),
sections 3, 10, 11 for rows 1, 2, 4 respectively; the Lean brick
`Dev/StripDensityTraceLedger` + audit for row 3; section 8 of the record for
row 5.

```text
+----+---------------------------+--------------------------------------------------+
| #  | row                       | outcome                                          |
+----+---------------------------+--------------------------------------------------+
| 1  | MP 2010 classification    | BM(phase) is ONE interval with d = 0, so the      |
|    |                           | shortness sum is VACUOUS for every beta, lambda;  |
|    |                           | the direction is short => NONTRIVIAL (Erratum A); |
|    |                           | in class only for p < 1/2, not p = 2 (the gap)    |
| 2  | B4-scalar per column      | the literal premise FAILS for all three column    |
|    |                           | classes; mechanism |m| ~ |x|^{2 pi y} vs decay,   |
|    |                           | threshold y = 1/(4 pi); support algebra makes the |
|    |                           | literal line degenerate -> orientation flag       |
| 3  | StripDensity trace layer  | brick landed (2662 jobs, standard axioms, zero    |
|    |                           | warnings in the new modules); 1625's operator     |
|    |                           | sandwich refuted by an explicit C^2 witness       |
| 4  | Toeplitz kernel probe     | no finite-type witness at any lambda (1627        |
|    |                           | confirmed numerically); sigma_min saturates in K  |
|    |                           | and decays in lambda: 0.4125, 0.0682, 0.0260,     |
|    |                           | 2.99e-6 (0.1), <= 1.8e-11 (0.01) - approximable   |
|    |                           | but not attained                                  |
| 5  | B3 re-decomposition       | STRUCK: no provably nonempty substitute exists    |
|    |                           | (inside = base in disguise, larger kills the      |
|    |                           | distance terms, other skeleton = rename)          |
+----+---------------------------+--------------------------------------------------+
```

New laws from this batch:

```text
F41  read the DIRECTION and the exponent off the primary source: "shortness"
     in the BM sense is a nonvanishing mechanism (short => kernel != 0), and
     the criterion's p-range is part of its hypotheses.
F42  name the kernel class and the exponent before invoking a criterion:
     H^p subset N^+ makes "outside N^+" vacuous, and N^+ cap L^2 = H^2 makes
     the p = 2 case exactly the Hardy kernel (Smirnov).
F43  a numeric floor is a property of the rig, not of the object: calibrate it
     on a case with a known exact answer, and quote every reading against it
     (here: window-edge leakage, 4.1e-8 at |xi| <= 64, 1.8e-11 at 128).
F44  a committed formula can be degenerate by its own support algebra (B4-scalar
     with K and the columns on one half-line): check the formula's own support
     before treating its failure as evidence.
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
F41  read the DIRECTION and the exponent off the primary source: shortness in
     the BM sense is a NONVANISHING mechanism (short => kernel != 0), and the
     criterion's p-range is part of its hypotheses.
F42  name the kernel class and the exponent before invoking a criterion:
     H^p subset N^+ makes "outside N^+" vacuous; N^+ cap L^2 = H^2 makes the
     p = 2 case exactly the Hardy kernel (Smirnov).
F43  a numeric floor is a property of the rig, not of the object: calibrate it
     on a case with a known exact answer and quote every reading against it.
F44  a committed formula can be degenerate by its own support algebra
     (B4-scalar with K and the columns on one half-line): check the formula's
     own support before treating its failure as evidence.
F45  an inventory row IS its hypotheses: a tool is listed only with (statement
     verbatim, source, hypothesis list, the single failing hypothesis when out
     of class); a row without a retrieved statement is a POINTER and carries no
     verdict (1631 row B2).
F46  class, exponent and eps-gap are part of a statement: "short" drives
     nontriviality in N_p (p < 1/2), representability up to eps x in N^+, and
     triviality of the PERTURBED symbol in H^2; quoting the word across classes
     is quoting a theorem without its exponent (1631 sec 5).
F47  a re-typing must be tested at the DEGENERATE parameter and on an
     ASYMMETRIC model: 1630's two-tap form passed its m = 1 check only because
     delta is even; lambda = 1 and a shifted-tap model (mu != 0) separate the
     correct pullback from the wrong one (Erratum C, 1631 sec 7).
Stop word: a gate certificate, or a proved refutation of the base.
```

## 7. One-line status

Tower formal; gate = `0 ≤ qw(g)` = `(★)` = `P C P` HS; residual skeleton exact
and closed except `StripDensity` content and the carrier distances; the
`StripDensity` trace layer is landed (brick + refutation of 1625's sandwich);
both WO legs rest on the carrier base, which after 1630 is: NOT decided by any
retrieved criterion (MP 2010 Thm 8.5 audited out of class at `p = 2`), NOT
witnessed by any finite-type function (1627 + 1630 §11, defect decaying in `λ`
from 0.41 to the calibrated floor), and NOT bypassable by a re-decomposition
(B3 struck, 1630 §8).  The single live route is an infinite-type witness or a
criterion at `p = 2`. RH not claimed; no gap premise introduced.
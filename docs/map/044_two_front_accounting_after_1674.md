# 044 — Route map after 1674: the two-front accounting

Date: 2026-09-19. Supersedes 043 as the *navigation* document (043 keeps the
base-weapon inventory, the five questions and the B1/B2/B4 decision tree;
nothing in 043 is withdrawn — the lanes 1635-1674 postdate it).

Read with: 043 (the base inventory), the live-state card (laws F8-F58), the
records `docs/proofs/1635`-`1674`, and repo-root `MEMORY.md` (entries
2026-09-18/19).

## 1. What changed since 043

043 was drawn after 1629 and updated after 1632. Records 1635-1674 then ran
two lanes it does not describe, plus one no-go:

```text
  1636-1642  the carrier base gains a CONSTRUCTIVE program
             (compact-observable interface 1636; Laguerre finite sections
             1639-1642; corrected numerics 1640: finite-section defect
             decreasing, observable mass ~0.92-0.99; four analytic
             obligations, no theorem)
  1643-1674  the endpoint face is compressed to ONE inequality
             (1659: endpoint gate iff survivor-core square-sum;
             1660-1663: reverse-limit / eventual criterion;
             1664: annular reduction; 1669/1670: Gram trace interfaces;
             1672: trace-class owners; 1674: the LOWER side
             0 <= Re tr Gram(N,n) is CLOSED; the uniform UPPER bound is
             the single remaining producer)
  1655       the global full-basis Hilbert-Schmidt escape is a proved
             NO-GO at unit scale
  1673       the WO-B face gets its fixed-coordinate owner K_b P_+ K_b
```

## 2. The gate after 1674

```text
          GATE: 0 <= qw(g)  for all g       [iff SourceRH, machine-checked]
                    |
   +----------------+--------------------+---------------------+
   |                |                    |                     |
[endpoint face] [WO-B face]        [carrier base]       [residual skeleton]
 g8EndpointGate   K_b P_+ K_b        carrier != {0}       StripDensity content /
  iff survivor    (1673 exact        (Laguerre program)   EndpointMass(eps)
  core (1659)     normal form)                             (1625/1630 trace layer)
   |                |                    |
   v                v                    v
 survivor-core   fixed-half-line     four obligations
 square-sum      estimate OPEN       (1636-1642)
   |
   v  (1660-1674, all formal)
 UNIFORM ANNULAR GRAM BOUND
 0 <= Re tr Gram(N,n) <= B   for all n >= N
      ^lower CLOSED (1674)   ^upper OPEN — the single S3 producer
```

## 3. The two-front accounting (Pi / Sigma)

Every remaining obligation is of one of two logical types:

```text
+----+------------------------------------+----------+-------------------+
| #  | object                             | type     | front             |
+----+------------------------------------+----------+-------------------+
| 1  | uniform annular Gram upper bound   | Pi       | A (analysis)      |
|    | 0 <= Re tr Gram(N,n) <= B, n >= N  | (bound)  |                   |
| 2  | fixed-half-line estimate for       | Pi       | A (same tool      |
|    | K_b P_+ K_b (1673)                 | (bound)  | family)           |
| 3  | carrier witness, carrier != {0}    | Sigma    | B (construction:  |
|    |                                    | (exists) | Laguerre, 4 obs.) |
| 4  | StripDensity square-sum content /  | Pi       | A (brick shared   |
|    | EndpointMass(eps)                  |          | with row 1)       |
+----+------------------------------------+----------+-------------------+
```

"One inequality" in the wave language = rows 1+2: one tool family, two
consumers. The honest form is TWO fronts — A, one analysis line with two
consumers; B, one construction line with four obligations.

Why exactly two, and not one: the gate identity

```text
residual^2 = StripDensity + SUM_i dist(h_i, carrier)^2    (1586-1589, exact)
```

is an ABSORPTION identity. It needs (i) an absorber that exists (the carrier,
Sigma) and (ii) a summable leakage (the estimates, Pi). At carrier = {0} the
distance term degenerates to the full norm and the identity loses all
purchase ("true and useless at {0}", 1589; the witness is consumed as a
hypothesis at CCM24FiniteSFixedFullBoundaryInjectivityGuard.lean:103).
Neither type implies the other:

- Pi does not give Sigma: no finite-type witness exists (1627), so no
  finite-window estimate can construct the absorber (1630 sec 11:
  approximable, not attained).
- Sigma does not give Pi: B1 only makes the legs provable-by-criterion
  (043 sec 5); the estimates still have to be executed.

And every merge that would have collapsed the two into one is formally
closed:

```text
+---------------------------------------------+------------------+
| merge route                                 | outcome          |
+---------------------------------------------+------------------+
| provably-nonempty substitute for the        | STRUCK (1630 s8) |
|   carrier (B3)                              |                  |
| global full-basis Hilbert-Schmidt shortcut  | NO-GO  (1655)    |
| finite-type / compact-support witness       | excluded (1627)  |
+---------------------------------------------+------------------+
```

The two-front residue is the post-exclusion minimum, not a design choice.

## 4. Next-wave plan and the decision gate

Spend order (2026-09-19 strategy round):

1. RIG FIRST (laws F43/F52): measure tr Gram(N,n) over (N,n) on exact models
   (m = 1 control + real m). Two questions: does sup_n saturate, and what is
   the decay law of B(N)?
2. DECISION GATE:
   - B(N) decays (polynomial / strip-like) => the kernel-diagonal attack is
     viable: land the basis-to-measure trace identity brick (the 1625
     missing layer, instantiated at Gram(N,n); DOUBLE consumer: the annular
     bound and the StripDensity content) and draft the estimate.
   - B(N) saturates at a positive constant => the S3 face needs genuine
     cancellation; shift main weight to front B.
3. Parallel (front B): Laguerre obligation 1 — completeness and
   normalization of the Laguerre Hardy-side system in the committed input
   space (classical; prerequisite of obligations 2-3).
4. Then WO-B: the fixed-half-line estimate for K_b P_+ K_b with the
   front-A tool.

The 1655 no-go should be numbered as a law in the next wave record
(candidate F59: the ambient leakage leg is not Hilbert-Schmidt on any basis
at unit scale whenever the selected source Laplace value is nonzero — the
global-HS shortcut does not exist and must not be retried).

## 5. Guardrails carried forward

```text
F33  base existence is a HYPOTHESIS — never re-file it as a theorem.
F43  a numeric floor is a property of the rig: calibrate on an exact model
     before reading anything (here: m = 1 controls first).
F52  a degenerate floor reports nothing: live floors only where the model's
     exact witness is absent from the probe family.
F55/F58  Gram weight dxi not du; translate families in the favourable
     direction.
1655 no-go: no global full-basis HS premise at unit scale (to be numbered).
```

Stop word unchanged: a gate certificate, or a proved refutation of the base.

## 7. Execution note (2026-09-19, record 1675)

Section 4 item 1 (rig first) resolved NEGATIVELY and is superseded:
`scripts/annular_gram_trace_1675.py` proved that the truncated-grid carrier
meet is DIMENSION-FORCED (`dim >= 2a/du` for ANY involutive unitary
conjugation; generic-random-phase control identical to the committed
symbol), so B(N)'s decay law cannot be read on any truncated rig. The
decision gate of section 4 is replaced by: attack the uniform annular Gram
upper bound ANALYTICALLY via the kernel-diagonal / local-trace route (the
1625 basis-to-measure trace identity, double consumer with StripDensity
content), calibrating against the m = 1 exact answers (carrier = L^2[-a,a],
B = 0 exactly for N >= a + R, one-sided bounds diverge linearly). Base
numerics remain on front B only, as trend quantities against the forced
count. Laws F59 (the 1655 no-go, numbered) and F60 (the forced-meet law)
are filed in record 1675.

## 6. One-line status

Tower formal; gate = 0 <= qw(g) iff SourceRH; endpoint face = ONE open
inequality (the uniform annular Gram upper bound; positivity closed 1674);
WO-B has its exact fixed-coordinate owner (1673) and owes the half-line
estimate; the carrier base has a constructive program with four open
obligations and no theorem; every merge route between the bound front and
the witness front is formally closed; the next spend is a rig on tr Gram
with an explicit pivot rule. RH not claimed; no gap premise introduced.

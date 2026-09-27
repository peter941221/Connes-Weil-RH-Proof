# Record 2039 — Route D closure: sign conservation under identity splitting

Date: 2026-09-27.

Status: ROUTE D CLOSED (upgrade of the map-108 freeze to a no-go). Pure
deduction from committed facts; no new measurement, no Lean brick, no RH
claim. This closes the "owner-specific factorization" reopen condition that
map 108 left open.

## 1. What is proved

Work at the corrected trace identity interface of
[016](016_corrected_trace_identity.md), conditional on its Section 7 analytic
hypotheses (A trace-class, A*A trace-class, cyclic moves legal):

```text
PositiveTrace_(S,L)(g) = QW(g,g) + D_(S,L)(F_g),
PositiveTrace_(S,L)(g) = Tr(A_g^* A_g) >= 0.
```

Claim (elementary equivalence). The following are equivalent:

```text
(i)  QW(g,g) >= 0;

(ii) there exist an operator C with 0 <= C <= I and a scalar b <= 0 with
     D_(S,L)(F_g) = Tr(A_g^* C A_g) + b.
```

Proof.

```text
(i) => (ii): take C := I and b := D - Tr(A^* A) = D - PositiveTrace = -QW <= 0.

(ii) => (i): QW = Tr(A^* A) - Tr(A^* C A) - b
             = Tr(A^* (I - C) A) - b >= -b >= 0,
```

using I - C >= 0 and A*A trace-class. QED.

So the Route-D factorization target (map 108 first brick, in its weaker
boundary <= 0 form) is EXACTLY the target inequality, for every owner, with
zero deductive content added by the C-machinery. The C = I direction exhibits
the trivial factorization whenever QW >= 0 already holds.

## 2. Corollary: the boundary is forced to carry the whole gap

For ANY decomposition

```text
D_(S,L)(F_g) = D_dom + r,      D_dom <= PositiveTrace(g),
```

one has

```text
r = D - D_dom >= D - PositiveTrace = -QW(g,g).
```

Under the formal mainline theorem (hypothetical off-line zero -> selected
healthy detector with qw(g) < 0), every such remainder satisfies
r >= -QW(g,g) > 0 strictly. In particular:

```text
the map-108 "boundary_S(g) = 0" brick is refuted for every hypothetical
owner by the committed formal facts alone;
the "boundary_S(g) <= 0" form is equivalent to qw(g) >= 0 by Section 1.
```

Map 108's registered kill condition — "the boundary/commutator remainder is
exactly the old qw >= 0 premise under another name" — is therefore met BY
FORCE, not contingently. No owner-specific arithmetic identity can change
this: the conservation is a consequence of the M0 identity itself
(additivity of the split), not of any particular construction of C.

## 3. Law registration

```text
SIGN-CONSERVATION-UNDER-SPLITTING (law F82):
if QW = P - D is an identity with P provably >= 0, then every mechanism
that "dominates part of D by part of P" leaves a remainder carrying at
least the full gap -QW. Identity-split routes cannot shrink the qw >= 0
obligation; only a non-split mechanism (a direct sign on a channel, a
genuinely different positive object, or a construction changing the
owner) can.
```

Screening consequence for future desks: any proposal whose mechanism section
reads "write the defect as [dominated part] + [remainder]" is dead on arrival
under this law and must not be registered.

## 4. Scope and what remains open

- The closure is conditional on the M0 analytic interface (016 Section 7).
  If that interface fails for the actual owner, Route D lacks its identity
  altogether and is deader still. In both branches the registered route
  shape is closed.
- NOT closed by this record: direct defect negativity D_(S,L)(F_g) <= 0,
  which yields QW >= PositiveTrace >= 0 without splitting. That is a
  non-split, Route-A-shaped signed estimate on the actual owner and remains
  governed by the Route-A records ([2038](2038_route_a_one_copy_interval_certificate_audit.md)
  and its predecessors).
- The numerical invariance screen originally considered for this reopen
  (testing whether the defect maps the A-column space into itself on the
  2037 basis) is unnecessary: the closure is logical, not numerical
  (workflow laws F27/F28 — numerics last).

## 5. Consequences for the route ledger

```text
Route A: 2038 no-go stands; reopen attempt = record 2041 interval chain.
Route B: DEAD_ON_CURRENT_FAMILY stands (2035).
Route C: literature-audit lane stands (1995).
Route D: CLOSED by this record (was: FROZEN CURRENT SKETCH, map 108).
Route E: registered as a DESK by record 2040 / map 109, subject to law F82.
```

Evidence:

- `docs/proofs/016_corrected_trace_identity.md` (M0-vanishing, Section 7)
- `docs/map/108_route_d_theta_supersymmetric_defect_domination.md`
- `docs/proofs/112_route_d_universal_contraction_no_go.md`
- mainline README (`route/000_rh_mainline/README.md`): formal qw < 0 producer

No RH claim.

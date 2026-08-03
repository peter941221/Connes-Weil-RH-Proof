# Proof 772: lift-invariant Julia row trace

Date: 2026-08-03

Status: exact signed-trace reformulation of the Proof 770 completed corner.
It shows that Proof 771's weighted `S_1` norm is a strong sufficient
majorant, not the preferred Gate 3U target.  The actual scalar is a
lift-invariant (lift-invariant) Julia row trace, so compact root support can
act before the first absolute value.  This does not prove that trace bound for
CCM24.  Gate 3U, the finite-`S` sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------------+-----------------------------+
| layer                                                | judgment                    |
+------------------------------------------------------+-----------------------------+
| completed physical corner `L_j`                     | exact, Proof 770            |
| bounded prefix lifts                                | conditional source input    |
| weighted Julia row                                  | existing contraction        |
| direct-sum diagonal trace identity                  | exact                       |
| independence from the chosen bounded lifts          | exact                       |
| `S_1` norm of the lift row                          | strong sufficient only      |
| signed source-row trace estimate                     | active Gate 3U formulation  |
| Gate 3U / finite-S sign / Burnol / RH               | open / open / open / open   |
+------------------------------------------------------+-----------------------------+
```

The decisive distinction is:

```text
Proof 771:
  abs(Tr(JuliaRow * LiftRow)) <= norm(LiftRow)_1
  -- valid, but may discard scalar cancellation.

Proof 772:
  estimate Re Tr(JuliaRow * LiftRow) itself
  -- the required compact-support-first Gate quantity.
```

Proof 260 already gives the reason this distinction is mandatory: a completed
crossing can have zero scalar trace while retaining a strictly positive trace
norm.  No generic Hilbert--Schmidt factorization recovers that lost scalar
cancellation after a trace norm has been taken.

## 2. The one Julia row and one lift row

Use Proof 771's finite family notation:

```text
w_j=p_j-1,
E_j=(I-P_j)H,
E_S=direct_sum_j E_j,
Ltilde_j=(U_j^mid)*L_j,
Ltilde_j=Psi_(j-1) X_j.                            (JT.1)
```

Let `iota_j:E_j -> E_S` be the coordinate inclusions.  The weighted lift row
is again

```text
X_S:E_S -> K_0,
X_S iota_j=w_j^(-1/2) X_j.                         (JT.2)
```

The *actual* weighted Julia range row is the bounded map

```text
J_S:K_0 -> E_S,
(J_S x)_j=sqrt(w_j) R_j U_j^mid Psi_(j-1) x.       (JT.3)
```

Proofs 351 and 354 give the contraction ledger

```text
J_S* J_S <= I_(K_0).                               (JT.4)
```

This is not an arbitrary direct-sum row.  Its `j`-th coordinate contains the
same midpoint range sine, the same fixed-source unitary, and the same
chronological Julia prefix that occur in the completed physical trace.

## 3. Exact diagonal trace identity

Assume the existing fixed-`S` physical trace cycle is legal and that
`J_S X_S` is trace class.  The `j`-th diagonal compression is

```text
iota_j* J_S X_S iota_j
 =R_j U_j^mid Psi_(j-1) X_j
 =R_j L_j.                                         (JT.5)
```

The second equality uses `(JT.1)` and that `U_j^mid (U_j^mid)*` is the
identity on the range of `L_j`.  Since the family is finite, ordinary trace
additivity over the direct sum gives

```text
Tr_(E_S)(J_S X_S)
 =sum_j Tr_(E_j)(R_j L_j)
 =sum_j Tr_(P_j H)(L_j R_j).                       (JT.6)
```

The last equality is exactly the already-required legal rectangular trace
cycle.  Proof 770 identifies its real part with the recombined two-root
response, therefore

```text
Q_S_near=2 Re Tr_(E_S)(J_S X_S).                   (JT.7)
```

This equation is the intended row-level owner.  It is a single signed trace
of the whole finite family, not a sum of norms of individual root components.

## 4. The scalar does not depend on the lift choice

Suppose `X_j'` is a second family of bounded lifts satisfying `(JT.1)`, and
let `X_S'` be its weighted row.  Then

```text
Psi_(j-1)(X_j-X_j')=0.                             (JT.8)
```

Consequently the `j`-th diagonal block of the difference is zero:

```text
iota_j* J_S (X_S-X_S') iota_j
 =R_j U_j^mid Psi_(j-1)(X_j-X_j')
 =0.                                                (JT.9)
```

Whenever the two row products are trace class, finite direct-sum trace
additivity turns `(JT.9)` into

```text
Tr(J_S X_S)=Tr(J_S X_S').                          (JT.10)
```

Thus a source proof may choose any bounded lift that exposes the physical
geometry.  It must not manufacture one by applying a Moore--Penrose inverse:
the inverse can be unbounded when the prefix range is nonclosed.  The scalar
is invariant under admissible bounded lift changes; the trace norm
`norm(X_S)_1` is not.

## 5. Why the signed trace is strictly preferable

If `X_S` itself is trace class, then `(JT.4)` gives the valid but coarse bound

```text
abs(Q_S_near)
 <=2 norm(J_S X_S)_1
 <=2 norm(X_S)_1.                                  (JT.11)
```

This is Proof 771's sufficient route.  It has already taken a trace norm
before the physical signed cancellation can be used.

The narrower Gate statement is instead

```text
J_S X_S is trace class,
abs(Re Tr(J_S X_S))
 <=C (1+B_root)^d norm(g)_(H^r)^2.                (JT.12)
```

Equation `(JT.12)` is weaker than a uniform `norm(X_S)_1` bound and is the
only form compatible with Proof 260's obstruction.  It retains all of the
following inside the trace:

```text
the two root orientations recombined in `L_j`;
the outer, reflected second-support, and prolate bracket;
the two quotient-boundary corrections;
the complete chronological Julia prefix;
the compact-root support cancellation.
```

The source must use compact support and the real-line kernel geometry to
bound `(JT.12)` before applying `abs`.  It may not replace `(JT.12)` with a
sum of individual `S_1` norms, a direct-sum Hilbert--Schmidt product, or a
bound on an arbitrary lift row.

## 6. A finite obstruction to the norm-first shortcut

The companion certificate constructs rank-deficient prefixes and a nonzero
family of null lifts `N_j` with

```text
Psi_(j-1) N_j=0.
```

For every scalar `kappa`, replacing `X_j` by `X_j+kappa N_j` preserves every
physical corner and the scalar row trace by `(JT.9)`, while the trace norm of
the weighted lift row grows with `abs(kappa)`.  This does not rule out a
carefully chosen minimal lift, but it proves that a trace-norm estimate on an
arbitrary lift cannot be a canonical Gate argument.

## 7. Evidence and verification

The named source row is the one constructed in
`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSJuliaBessel.lean`; its
Hilbert--Schmidt amplification is
`summable_juliaRangeEnergy_comp`.  The coordinate-level norm-one readout is
in
`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSActualJuliaRangeSineDouglas.lean`
as `exists_weightedRangeSineFactor_of_rangeSine_weighted_le`.

The finite certificate verifies `(JT.5)--(JT.10)`, the contraction-model
analogue of `(JT.4)`, and the null-lift trace-norm growth:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/772_lift_invariant_julia_row_trace_probe.py
```

It checks finite-dimensional block algebra only.  It does not prove a bounded
CCM24 lift, trace-class legality of the infinite row product, the direct
support-polynomial estimate `(JT.12)`, the finite-S sign, Burnol's identity,
or `_root_.RiemannHypothesis`.

## 8. Route judgment

```text
+------------------------------------------------------+-----------------------------+
| statement                                            | judgment                    |
+------------------------------------------------------+-----------------------------+
| row trace identity `(JT.5)--(JT.7)`                 | exact                       |
| lift invariance `(JT.8)--(JT.10)`                   | exact                       |
| trace-norm majorant `(JT.11)`                       | valid but coarse            |
| signed row trace bound `(JT.12)`                    | active Gate 3U theorem      |
| Gate 3U / finite-S sign / Burnol / RH               | open / open / open / open   |
+------------------------------------------------------+-----------------------------+
```

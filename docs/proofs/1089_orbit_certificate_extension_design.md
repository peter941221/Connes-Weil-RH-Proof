# 1089 - Orbit-window certificate extension: the surviving C3 shape after 1087

Date: 2026-09-02.

Status: DESIGN record. It names the consumer, pins the window arithmetic and the
visible prime-power set, and lays the candidate routes. It proves no sign and
does not claim RH. Evidence labels follow map `004` section 1
(FORMAL / LITERATURE-BACKED / NUMERICAL).

## 1. Consumer and evidence base

After record 1087 (root-window spectral verdict, commit `b83dec0`), kernels (a)
and (b) at the ROOT window are closed as attack lines:

- kernel (a) was adjudicated NUMERICALLY NEGATIVE on the root window
  (`docs/proofs/1087_c3_root_window_spectral_verdict.md`): an arch-positive
  witness on the root-window triple-vanishing class would be a not-RH witness,
  not an RH lemma;
- kernel (b) guarded a numerically empty set (orbit-to-root transport; the
  1081 prefix wall has nothing to transport).

The sole surviving C3 shape is the one 1087 section 5 prescribed: grow the
ROOT-local CC20 endpoint certificate OUTWARD to the detector orbit window, with
a finite visible-prime readback. This record makes that target concrete.

The binding consumer is already formal (map `004` section 2):

```lean
healthy_sourceRH_of_right_detector_specific_qw_nonneg
  (C1HealthyYoshidaSpectralNegativity.lean:554)
(hsemiLocal : forall rho : sourceNontrivialZeroSet,
  (1/2 : Real) < rho.1.re ->
    Exists g : CompactLogTest,
      HealthyYoshidaDetectorData rho.1 g /\ 0 <= C1SameOwnerWeil.qw g) :
  RHDefinitionBridge.standard.SourceRH
```

The detector half of the existential is FORMAL
(`exists_healthyDetectorData_of_sourceNontrivialZero_right`,
`C1HealthyYoshidaSpectralNegativity.lean:511`). The missing half is the
matching `0 <= qw g` on the SAME orbit detector. Per map `004` brick table this
is brick P2, OPEN.

## 2. Window arithmetic of the committed orbit detector

The construction behind the D1 export runs through
`exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner_with_raw_targets`
(`C1HealthyYoshidaUnscaledOrbit.lean:492`) with free window parameters. The
committed D1 export pins them at

```text
baseLower = baseUpper|.| = 1,  lower = upper|.| = 1  (i.e. base window (-1,1),
correction window (-1,1)),  epsilon = 1.
```

The exported support bound of the SELECTED OWNER SOURCE TEST (= the detector
`g`, after the half-density shift) is then

```text
supp g.test  subset  Ioo(-(n+2), n+2)          W_n, the orbit window
```

because `(n+1)*baseLower + lower = -(n+1) - 1 = -(n+2)` and symmetric on the
right. Here `n` is the orbit index chosen by the construction for the requested
zero-annihilation radius `R` (the dyadic tail budget), so `n` depends on the
hypothetical zero only through the height budget. This is allowed by the route
ruling `003`: a B5-shaped producer may use the detector's support radius to
select a finite set of visible primes, per zero.

The square window follows from the committed convolution-square support lemma
(`CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo`):

```text
supp (g.convolutionSquare).test  subset  Ioo(-2*(n+2), 2*(n+2)).
```

## 3. Visible prime powers of the orbit square

The same-owner prime machinery (`C1SameOwnerWeil.lean`) evaluates prime terms at
the log-coordinate points `+/- log q` for prime powers `q`:

- `globalPrimeIndexSet F = {q : IsPrimePow q /\ finitePrimeTerm F q <> 0}`
  (`mem_globalPrimeIndexSet_iff`);
- the ROOT vanishing lemma `finitePrimeSum_eq_zero_of_support_subset_open_log_two`
  reads support-in-`(-log 2, log 2)` to `finitePrimeSum F = 0` by the pointwise
  argument `log q >= log 2`.

The identical argument with the window bound `B := 2*(n+2)` gives the orbit
readback (record 1097 lands this as a small Lean lemma):

```text
q in globalPrimeIndexSet g.convolutionSquare  ->  (q : Real) < exp(2*(n+2)),
```

so the visible set of the orbit square is

```text
V_n = { prime powers q : q < exp(2*(n+2)) },
```

finite, explicit, and computable as a `Finset.filter`. Concrete scale for the
first orbit (n = 1): window `(-3, 3)`, square window `(-6, 6)`,
`exp 6 = 403.43`, so `V_1` contains 78 primes plus their in-range higher
powers. The record does not need the exact count in Lean; the filter bound is
the interface.

Sign bookkeeping at the orbit window (map `004` section 3, FORMAL):
`qw g = -arch(F_g) - finitePrimeSum(F_g)`, so

```text
0 <= qw g   iff   arch(F_g) + finitePrimeSum(F_g) <= 0.
```

## 4. The named gate and the one-line bridge

The orbit-window analogue of the record-1080 scalar gate is

```lean
def orbitWindowSemiLocalGate (g : CompactLogTest) : Prop :=
  C1SameOwnerWeil.archimedeanTerm g.convolutionSquare +
    C1SameOwnerWeil.finitePrimeSum g.convolutionSquare <= 0
```

with the one-line bridge (landed with this record,
`C1OrbitWindowSemiLocalGate.lean`):

```lean
theorem qw_nonneg_of_orbitWindowSemiLocalGate :
  orbitWindowSemiLocalGate g -> 0 <= C1SameOwnerWeil.qw g
```

using `qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple`
(the orbit detector is triple-vanishing by `HealthyYoshidaDetectorData.vanishesOnF`).
This makes the P2 obligation a SINGLE Prop on the SAME explicit object, exactly
as record 1085 did for the root gate before 1087 adjudicated it.

## 5. Routes to the gate (design options, none proved)

```text
+----+------------------------------------------+-----------------------------+
| ID | Route                                    | Status / owed contracts     |
+----+------------------------------------------+-----------------------------+
| A  | Restricted-scale certificate: run the    | OPEN. Owes (A1) exact       |
|    | qwLambda finite-section shape with       | sign/convention readback of |
|    | lambda = exp(n+2) so the restricted      | the orbit prime terms to    |
|    | prime index set lambda^2-bound matches   | the visible set V_n (P1     |
|    | V_n, and a finite-section/Toeplitz       | readback infra is FORMAL);  |
|    | coercivity certificate covers            | (A2) finite-section         |
|    | arch + restricted prime sum.             | positivity at orbit scale   |
|    |                                          | (paper-scale E1 shape,      |
|    |                                          | LITERATURE RECONSTRUCTION). |
+----+------------------------------------------+-----------------------------+
| B  | Same-owner trace readback: the semilocal | OPEN. The legality layer is |
|    | chain (ordinaryTraceAlong readbacks +     | exactly the S2 producer     |
|    | residual decomposition, map 004 sec 4)   | thread; its correct         |
|    | reduces the gate to a semilocal trace    | primitive set is decided by |
|    | inequality on the prolate remainder.     | record 1097's fork (the     |
|    |                                          | 1096 A-in-HS discharge vs   |
|    |                                          | the law-16 (a)+(b) set).    |
+----+------------------------------------------+-----------------------------+
| C  | External compact-window supply (Chuk     | BLOCKED for the orbit       |
|    | arXiv:2608.24827 Cor 9 + M1-M6 bridges)  | detector: the D1 orbit      |
|    |                                          | window always contains      |
|    |                                          | points of |u| in (0.8, 2],  |
|    |                                          | so M6 cannot hold for it    |
|    |                                          | (support arithmetic above). |
|    |                                          | Sub-0.8-window orbit        |
|    |                                          | variants face the 1087      |
|    |                                          | negative plateau (NUMERICAL |
|    |                                          | extrapolation beyond the    |
|    |                                          | scanned radius - recon,     |
|    |                                          | not verdict).               |
+----+------------------------------------------+-----------------------------+
```

Route C note (map update): this sharpens map `004` section 6, which said no
support theorem "is currently exported". For the committed fixed-window D1
export the support bound `Ioo(-(n+2), n+2)` IS exported by the underlying
construction, and `n >= 0` forces `sup |u| >= 2 > 0.8`; M6 is therefore
impossible for this detector family, not merely unexported.

## 6. Route B dependency on record 1097

Route B's legality layer currently sits behind record 1096's discharge, which
reduced the S2 sandwiched nuclearity to the single primitive
`targetProlateRemainderFactorHS` (A in HS, i.e. `Tr K_S < inf`). That primitive
is exactly the raw-F1 quantity class that record 1063 falsified in the model
(window growth 16.2 -> 34.3 with no bend, dt-invariant), and the consuming
leaf's own header (`C1ProlateResponseTraceLegalityUnitScale.lean:78-80`) guards
against scheduling it. Record 1097 therefore pre-registers a fork BEFORE any
further producer work:

- H1 (A in HS on the continuum) expected FALSE; rejection returns the route to
  the law-16 obligation set (a) smoothed-factor HS (`AC in HS`) plus
  (b) commutator-remainder trace legality - both measured O(1) flat in
  records 1068/1090;
- H2 (the (a)+(b) set O(1) at deeper windows) expected TRUE; it re-canonicalizes
  the sandwiched-nuclearity contract of record 1095 as the Route-B target,
  with 1096's discharge demoted to a valid-but-vacuous implication.

Route B is only schedulable after that fork fires.

## 7. Optional reconnaissance (not scheduled this record)

A scan adding the quadratic visible-prime row `F(log 2) = 0` may price the
outward reach of the positive region along the orbit scale. Per the 1087
strategic output this is reconnaissance only: it cannot change the map and
requires a named consumer before scheduling (route ruling `003`, freeze item 4).

## 8. What this record changes

- `docs/proofs/1097_p2_contract_fork_preregistration.md` (companion): the fork
  record for Route B's legality layer.
- Lean brick landed with this record: `Dev/C1OrbitWindowSemiLocalGate.lean`
  (+ `...Audit`) - the named gate, the one-line bridge, the support/visible-set
  readback lemmas, and the pinned orbit-window export
  (`exists_pinnedOrbitDetector_with_window_and_visiblePrimes`).
- `docs/map/004` section 6: M6 sharpened from "not exported" to "impossible for
  the committed D1 orbit family" (support arithmetic, FORMAL).

RH is not claimed. GATE 1 mainline untouched.

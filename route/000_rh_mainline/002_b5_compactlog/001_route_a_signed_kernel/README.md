# 002.001 — Route A: same-owner signed physical kernel

Status: ACTIVE CAMPAIGN. RH is not claimed.

Target:

```text
archimedeanTerm(selectedOwner.square)
    + integral(actualAggregate)
    <= -epsilon
```

The aggregate must retain the actual finite visible-prime sum and its signed
cancellation. Primewise absolute majorants are not an acceptable replacement.

Current assessment:

```text
formal:
  selected-owner readback
  derivative-controlled selector interface
  exact aggregate-residual reduction
  variational/minimum-coefficient selector core

open:
  owner-specific strict signed margin
  finite-basis physical-cost margin
  parameter quantifiers
```

Current scoped obstruction:

```text
NO-GO-A2-FINAL-SIGN-CURRENT-SELECTOR
```

This is a no-go for the current selector API, not for every possible
sign-constrained or variational selector.

Height audit (record 1994, pre-registered):

```text
opposite-gates certificate (1902) on the committed owner class:
  gamma_1..gamma_4, gamma_6: hosts (1983)
  gamma_5: RESCUED (1994) — 6/15 cells C > 0, D < 0, det < 0;
           the 1983 hole was a sampling artifact of the 0.90 band
  committed convention basis is now hole-free through gamma_6

extension beyond gamma_6 (records 1994 + 1996, EXT convention):
  1994's 2-cell sample read C < 0 / det > 0 (unhealthy per 1931) and
  left height vs convention UNRESOLVED; the 1996 FULL scale sweep
  (5 scales x 3 deltas per height, pre-registered) closes the
  question as a SAMPLING ARTIFACT —
    gamma_7: HOST_CONFIRMED (window sc = 0.92, all three deltas)
    gamma_8: HOST_CONFIRMED (window sc = 0.88, all three deltas)
    D < 0 on 33/33 cells with certified spreads
  the C health window is ordinate-dependent and single-scale at the
  higher ordinates: future extensions must SWEEP scale, not sample it.
  Opposite-gates hosts now certified at every measured ordinate
  gamma_1 .. gamma_8; no height wall through gamma_8.
```

Authoritative records:

- `docs/map/104_route_a_four_round_campaign.md`
- `docs/proofs/1926_route_a_final_sign_current_selector_no_go.md`
- `docs/proofs/1929_route_a_finite_basis_minimum_selector.md`
- `docs/proofs/1994_opposite_gates_height_audit.md`
- `docs/proofs/1994_opposite_gates_height_preregistration.md`
- `docs/proofs/1996_gamma78_full_sweep_preregistration.md`
- `docs/proofs/1996_gamma78_full_sweep_audit.md`
- `docs/proofs/1997_f2_transport_bridge_desk.md`
- `docs/proofs/2001_route_a_variational_probe_outcome.md`
- `docs/proofs/2003_route_a_health_selector_reregistration.md`
- `docs/proofs/2004_route_a_health_selector_outcome.md`
- `docs/proofs/2005_route_a_variational_probe_evidence_correction.md`
- `docs/proofs/2006_route_a_health_cone_shape_preregistration.md`
- `docs/proofs/2007_record_2006_check_amendment.md`
- `docs/proofs/2009_record_2006_anchor_gate_amendment.md`
- `docs/proofs/2010_route_a_health_cone_outcome.md`
## Recommended next subroute: A-V variational selector

Record 1999 selects `A-V owner-preserving constrained variational selector`
as the next Route-A probe. It replaces the current interpolation selector,
which is blocked by record 1926, with a finite-owner minimum physical-energy
problem and a dual certificate. The selector must preserve the actual support,
Mellin nodes, visible-prime set, grouped aggregate, and quantifier order.

This is a candidate mechanism, not a theorem. The first kill test is a
pre-registered finite constrained quadratic probe. It must report feasibility,
minimum derivative cost, grouped residual, margin ratio, conditioning, and
active constraints. A nonpositive margin, infeasibility, divergent budget
ratio, or owner mismatch is a scoped no-go for A-V.

A-V outcome (record 2001): the unconstrained minimum-H1 selector is a scoped
no-go. On certified gamma_7/gamma_8 owners it produced C < 0; gamma_8 also
had det > 0. gamma_5 rows were rank/pin unresolved at the registered cutoff.
Do not formalize A-V. A possible next Route-A mechanism is A-H, a separately
pre-registered health-constrained selector in the same owner fibre; C > 0 must
be an admissibility condition, not a hidden replacement for the missing D < 0
proof. If A-H fails, Route B becomes the primary research route.

CORRECTION (record 2005). The A-V certification above is not supported by the
run artifact. `results/2000_route_a_variational_probe.json` records route set
`["A", "B"]` and `spread_D = 0.0` on all four rows: `route_spread` averages
only over `("Ap", "B")`, so a singleton certified route gave the degenerate
floor (law F52). The record-2000 family also used width copies `0.86a` /
`1.14a`, which raised the support radius past the `Ap` guard (G5-H and G7-H:
`9.9360 -> 11.3270`, `2393 -> 8212` prime powers; G8-H: `9.5040 -> 10.8346`,
`1647 -> 5284`) and so measured a larger visible-prime set than the committed
owner's. A-V status is therefore UNRESOLVED, not a scoped no-go. Do not
formalize A-V remains correct advice, for the different reason that the probe
cannot be read.

## A-H outcome: health cone has positive extent at high ordinate

Records 2003/2004. Record 2002's registered instrument is superseded: its
`1.2a` copy inflated the support the same way. The replacement keeps two
width copies per node, `0.75a` and `a`, so the support radius, the prime set
and the gate instrument are the committed ones, and scans the feasible fiber
along canonical unit-H1 nullspace directions.

```text
verdict            A-H-CONE-MIXED
instrument check   4/4 anchors reproduce the committed rows (<= 4.3e-11)
scan               4 owners x 2 directions x 7 amplitudes = 56 rows
                   56/56 certified on three routes, D < 0 in 56/56
health radius      G5-H 0, G5-W 0, G7-H 0.10 (both), G8-H 0.10 (dir 1), 0.80 (dir 2)
```

Structural finding: at gamma_8 direction 2 the margin increases monotonically
with the perturbation, `C = 664.35 -> 2128.7` (factor 3.20), with `D < 0` and
`det < 0` certified at every registered amplitude. The committed selector is
therefore not extremal for health; feasible interpolants with a strictly
larger margin exist. The two gamma_5 owners lose health at the first
non-zero amplitude `0.02`; they also hold the two smallest committed margins.

Record 2003 also records that the minimum-H1 endpoint of records 1999/2000 is
not numerically well defined: the family H1 Gram is rank deficient at
`1e-14..1e-15` relative and clipped pseudo-inverses miss the registered pin
gate while the exact-constrained solution needs coefficients of order `1e+14`.
The ray scan replaces that endpoint.

## Health-cone shape scan: stratified, energetic branch at high ordinate

Records 2006 (pre-registration), 2007 and 2009 (instrument amendments) and
2010 (outcome). The scan samples 8 of the 17 restricted-spectrum directions
at 4 amplitudes on the same 4 owners, with a route-robust health predicate.

```text
verdict            H-CONE-STRATIFIED / RANK-FLAT / MECH-MIX
instrument         4/4 anchors pass, 128/128 rows certified, identity
                   checks pass on every row
reproducibility    the re-executed artifact equals the first full run
                   bit-for-bit on C, B01, D, det, W0 (worst 0.0e+00)
health radius      G5-H none/0.02, G5-W none, G7-H 0.05..0.20,
                   G8-H 0.05 at 5 ranks and 0.80 at ranks 2, 4, 6
N = 14 pairs at sigma >= 0.05    (H-CONE-FAT needs 16)
D < 0              128/128 rows on both the route-keyed and route-B readouts
route robustness   healthy_ap = healthy_b on all four owners (4, 0, 16, 21)
```

The improvement direction is the energetic end of the restricted spectrum,
and only at the highest ordinate: exactly three `(owner, rank)` pairs have
`C(0.80) / C(0) > 1`, all G8-H, at ranks 2, 4, 6, with factors 3.20, 4.26,
4.04. Every other pair collapses, most through a sign flip. The registered
`RANK-FLAT` label is a rule artifact (argmax over ratios that are all
negative) and is reported as such.

Conditioning finding (record 2010 section 4): the committed `A` is the
residual of a cancellation of order `f = mm / A`, which is 7196 (G5-H),
86087 (G5-W), 133 (G7-H) and 51 (G8-H). The obligation `D < 0` is well
conditioned (certified-route spread `<= 6.0e-04`), while the health witness
`C > 0` is a cancelled quantity (spread up to `6.9e-02`), which is why the
two gamma_5 owners have no cone. The route-A numeric exposure therefore sits
in the admissibility check, not in the binding obligation.

Not core progress by the core-progress gate: no unconditional bound on the
selected detector, no new no-go (record 1926 stands), no smaller obligation.

Next: test whether the margin-increasing branch is a law in the ordinate
rather than a gamma_8 accident, and check whether the `D < 0` margin on the
same rows is monotone in the same directions.

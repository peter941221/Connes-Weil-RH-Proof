# 2247 — Measured separation input for the 2157 near-pin derivative floor

Date: 2026-09-30

Consumer: record 2157's remaining quantitative input — "separation from the
nonzero orbit targets" for the derivative-cost floor
`derivativeCost >= M >= 4 exp(-X S)/(delta X L^2)`.

Verdict: **measured** at the three 2103 stress candidates; the floor is
finite and explicit everywhere; a uniform-in-configuration separation
theorem remains research-grade.

## The proposition

At a fixed candidate `(rho, N)`: every nonzero target of the owner (the
1994 orbit/real targets with value `+-1`) is separated from every
zero-valued interpolation pin that is not itself a target, with
`|t - z| >= s_min`, and the 2157 floor with `delta = s_min` is positive.
Per fixed `rho` this reduces to a finite certified check (zero isolation);
uniformity over `rho` requires a certified isolation procedure for every
configuration.

## Targets and pins at the stress candidates

Targets (value `+-1`): `rho` (value 1), `1 - conj(rho)` (value -1),
`rho + 1/2` (value -1). Pins (value 0): `conj(rho)`, `1 - rho` (off-line);
`0.5, 1, 1.5` (real-axis); the 1994 kill ordinates; the in-ball zeros
added by the 2103 loop. Pin census per candidate: `27 / 30 / 33` pins =
`21 / 24 / 27` critical-line zeros + 1 non-zero kill pin + 2 off-line pins
+ 3 real-axis pins (the non-zero kill pin is the audited
`27.67032193035704`; see 2245).

## Measured separations and floors

```text
gamma        39.25244858548658  42.12289614653125  45.66611208104108
min |t - z|  1.7246687029005743 1.2837708405212573 2.380992966914273
nearest pin  37.586178158825671 40.9187190121475   43.327073280915   (critical-line zeros)
floor at min 0.0030755954591358543 0.004131877017085821 0.0022278029817236807
```

Per-target floors (the `S = max |Re|` of the achieving pair enters):

```text
target rho      0.0030755954591358543 0.004131877017085821 0.0022278029817236807
target 1-conj   0.009608984322583001  0.01290909094109991  0.006960253456480646
target rho+1/2  0.0007699022126940044 0.0009634863138932067 0.0005846130698864416
```

The overall minimum floor is `0.0005846130698864416` (candidate 3, the
`rho + 1/2` target: `S = 1.445` there dominates the larger separation);
the minimum separation is `1.2837708405212573` (candidate 2, target `rho`
against the zero at `40.9187190121475`). Target-to-target distances:
`0.5` (`rho` vs `rho + 1/2`), `0.89` (`rho` vs `1 - conj rho`), `1.39`;
conjugate pairs sit at `2 gamma ~ 78.5`.

The detector target `t = rho + 1/2` keeps the automatic separation
`t.re - z.re >= rho.re - 1/2 = 0.445` (2157); its measured minimum is
`1.915589239572187 / 1.5307081926260981 / 2.522722241645963`, comfortably
above the automatic bound. The orbit targets `rho` and `1 - conj(rho)`
have no automatic bound; their measured minima are the headline numbers.

## Alternatives and status

The three 2157-admissible alternatives: (1) an explicit separation bound
(this record: measured at the candidates; the formal uniform version needs
certified zero isolation); (2) a cost estimate using the full node geometry
(the direct solver does this; the 2109/2103 ledgers price the construction
without charging a derivative seminorm); (3) a signed argument avoiding the
derivative seminorm charge. No alternative is closed as a uniform
producer; (1) is the one measured here.

Nonclaims: measured separations at three candidates are not a uniform
separation theorem; under the Platt-Trudgian import the in-ball zero list is
complete, so per-candidate the check reduces to certified enclosures of the
listed zeros; no producer GO, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_separation_input_2247.py`;
- artifact: `results/2247_separation_input.json`;
- inputs: `results/2103_full_known_prefix_direct_owner_grid_m6400.json`
  (supports), `r94.owner_nodes_ext`, `r80.ball_radius`.
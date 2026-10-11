# Record 2666 — gate-lambda determination probe (audit grade)

**Verdict: GATE-LAMBDA-SEPARATED-FROM-LANES (audit grade).** On the
committed certified class, the four-point span construction's actual
lambda satisfies BOTH record-2354 scalar acceptance lanes with wide
margins: lambda = Bs/(2C) in [4.0019e4, 1.9570e5] over the 18 certified
cases, against the n=2 lane threshold 256 (separation >= 156.32x) and the
n=3 lane threshold 1e-13 (separation >= 4.0e17x). The lambda condition is
therefore NOT the binding constraint of the 2354 acceptance chain; the
binding constraints remain the gate witness itself and the
prefix/source-zero obligations. No gate witness, no reopening, no RH
claim.

## Question and instrument

Record 2354 left "actual gate lambda" unproved (AGENTS 2ba) and named as
its next step: prove the signed physical-kernel gate on the same object
and read the lambda it actually delivers. This probe narrows that
obligation with committed data only: the construction's lambda is the
quadratic vertex `lam_vertex = Bs/(2C)` of `Q(lam) = D - lam Bs + lam^2 C`
(D = IC(u*u), C = IC(g*g), Bs = IC(u*g)+IC(g*u)), committed per case in
`results/1918_fourpoint_diagonal_sign_certified.json` and re-probed in
`results/1945_fourpoint_explicit_lambda_probe.json`. Record 2354 proves
the tail-budget ratio is non-increasing in lambda > 0, so the vertex
choice is inside a lane iff the threshold is below it — a pure comparison,
no rig re-run, no Gram re-evaluation at the repaired pair, no
annihilation-identity reuse beyond reading committed lambda values
(frozen-family hazard, AGENTS 2ay, respected).

## Readings

```
+--------------+-----------+------------+--------------+------------+
| quantity     | value     |            | quantity     | value      |
+--------------+-----------+------------+--------------+------------+
| cases        | 18        | vertex Q<0 | 18/18        |            |
| lambda min   | 40018.85  | median     | ~40064       | max        |
| lambda max   | 195695.13 |            |              | 195695.13  |
| K range      | 17.1-24.0 | lambda ~   | 0.5 K^4      | ratio 0.92 |
|              |           |            |              | -1.17      |
| n=2 lane     | 256       | separation | >= 156.32x   | SEPARATED  |
| n=3 lane     | 1e-13     | separation | >= 4.0e17x   | SEPARATED  |
+--------------+-----------+------------+--------------+------------+
```

Structural reading: lambda tracks the geometry scale `0.5 K^4`
(K = 3 + |rho|) across the whole class (ratio 0.92-1.17, median 1.05);
the class parameter c moves lambda by < 0.1% at fixed host. The lambda is
a K-geometry scale, not a coefficient scale — which is why the separation
is expected to survive owner changes that keep the captured rho (K
unchanged).

## Repair-drift envelope and the named residual

Under the 2338 repair the coefficients move per-coefficient by at most
1.4e-11 (base) / 7.6e-4 (correction) relative (record 2665
`monotone_screens`). Since lambda = Bs/(2C) is a degree-2/degree-2
rational function of the selected-function coefficients, its first-order
drift is bounded by (Gram-ratio condition constant) x that envelope; the
condition constant is the NAMED RESIDUAL of this probe. An exact check is
the two-entry (Bs, C) re-run at the repaired pair — deliberately NOT
executed here: it re-runs the gate machinery on the frozen family's
construction (the 2ay hazard) and settles a decision only the gate
itself can settle. The audit-grade conclusion stands on the separation
being >= 156x: the drift would have to be four orders larger than the
per-coefficient envelope even at condition constant 1 to reach the
threshold.

## Nonclaims

- No gate witness at the repaired owner; the signed physical-kernel gate
  is the open producer bottleneck and this probe does not touch it.
- No repaired-owner Gram re-run; no map-103 reopening.
- SEPARATED is a necessary-condition audit, not a tail pass: the 2354
  ratios stay conditional on the same-owner gate, prefix and source-zero
  obligations.
- "Actual gate lambda remains unproved" (2ba) stands; what is new is the
  quantified separation and the named residual.

## Evidence

`scripts/routea_gate_lambda_audit_2666.py` (self-contained, committed
artifacts only) -> `results/2666_gate_lambda_audit.json`.

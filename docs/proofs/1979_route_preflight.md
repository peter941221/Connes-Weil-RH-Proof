# 1979 — Preflight decision before further Lean work

Date: 2026-09-25.

Status: PREFLIGHT ONLY. This record does not claim a determinant theorem or RH.

## Result

The route can be screened before writing more Lean, but the screening must keep
the quantifiers explicit. The current evidence gives three different answers:

```text
old cardinal base          SCOPED_SCAN_FAILURE
representative eight-node  SIGN_ONLY
full live route             INSUFFICIENT_EVIDENCE
```

## Evidence

The rerun of `scripts/fourpoint_owner_density_1959.py --cardinal` gives:

```text
pin errors:                 <= 3.34e-16
mass beyond |xi| > 4:       0.9989635633
max contraction profile:    144.2855788618
min contraction profile:    0.9815124928
T_need:                     None
```

Therefore the old cardinal interpolation base fails the required half-
contraction on the scanned range. This is only a finite-scan failure, not an
all-height no-go for every admissible base.

The committed design-owner JSON has 26 rows. Two rows satisfy the sign-side
endpoint simultaneously, but they interpolate only the eight target nodes:

```text
scale=0.90, k=30: C=5.05448, b=29649.4, det=-1.28567e9,
                  lambda=5865.96, T_need=17.7444
scale=1.00, k=40: C=0.984451, b=2305.04, det=-1.23169e7,
                  lambda=2341.44, T_need=17.5439
```

This is `SIGN_ONLY`, not `GO_CANDIDATE`: it proves only that a representative
eight-node sign geometry is reachable. The sample `rho` is also a formal
complex parameter, not an established zeta zero.

The formal consumer's actual owner is already defined by
`C1ExplicitHealthyCorrectionBudget.lean` as

```text
healthyCorrectionNodes rho N routeNodes
  = (sourceNontrivialZerosInClosedBallFinset rho
      (2^(N+1) + 2 + dist 2 rho) union routeNodes)
    union healthyUnscaledTargetNodes rho
```

The paired audit for that module passes with the standard three axioms, but the
finite set is noncomputable and its cardinality, separation products, and
quadratic decay constant remain unevaluated. The old eight-node determinant and
tail numbers therefore cannot be transferred to the live owner.

## Decision gate before Lean

Do not start a new determinant proof until one concrete owner and one `n` pass
all of these interval checks:

```text
C > 0
b > 0
det = C*D - b^2 < 0
beta_s * L_n < multiplicity_rho * lambda^2
```

The last inequality is the decisive gate. The current repository has no
numeric `C4`, `C2`, or actual-owner tail ratio, so the full route remains
`INSUFFICIENT_EVIDENCE`, not `GO`.

## Reproduction

```text
python scripts/fourpoint_owner_density_1959.py --cardinal
python scripts/route_preflight_1979.py
```

The classifier writes `results/1979_route_preflight.json` and deliberately
uses `SIGN_ONLY` for the eight-node sample and `INSUFFICIENT_EVIDENCE` for the
full live owner.

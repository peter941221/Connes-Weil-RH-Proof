# Route-B gate coverage and direction review (3118)

Date: 2026-10-26.

Status: SOURCE-AUDIT / COVERAGE-GAP. No new Lean theorem, gate sign,
numerical experiment, actual nonzero omitted term, or RH proof is claimed.
The formal result of 3117 is unchanged. Route A remains binding and the
authorized Route-B scope is unchanged.

## Review contract

Owner: the actual powered-seed selected test and its four-point span,
with the same hypothetical right off-line source zero rho. The stored
2718 model is evidence about its own stated inputs, not an identified
substitute for that function.

Question: does the stored gate evidence include the complete prime-power
contribution required by the current formal owner, and what signed estimate
would actually reduce the remaining RH obligation?

Consumer: `orbitWindowSemiLocalGate` and the existing same-span
prefix/tail contradiction. The named open premise is a complete same-owner
gate bound, including identification of the computed prime contribution.

Budget: one source review, no prime enumeration, frequency sweep, generated
certificate, or Lean rebuild. Completion is an explicit distinction between
proved facts, missing coverage, and the joint sign target. A wider support
upper bound alone cannot establish an actual nonzero omitted prime term.

Primary source snapshot: main commit
`ae7bd85930a7764440f56075744e9706fa241f94`.

## The gate is still the missing sign

`C1OrbitWindowSemiLocalGate.lean:57` defines the gate as the complete
archimedean term plus finite visible-prime sum being at most zero. On a
triple-vanishing test, `C1HealthyYoshidaDetector.lean:114` proves:

```text
qw(g) = -archimedeanTerm(g.square) - finitePrimeSum(g.square).
```

Thus the gate is exactly the opposite Weil sign in different coordinates.
Its expression is useful only when supplied with an independent arithmetic
estimate. Naming or repackaging the gate does not provide that estimate.

The quadratic expression is already formal at
`C1FourPointSpanGateCertificate.lean:89`. For the actual selected test g_n,
its four-point annihilator u_n, and their span v_n(lambda)=u_n-lambda*g_n,
define C_n as the gate on g_n.square, D_n as the gate on u_n.square, and
b_n as half the sum of the two directed cross gates. Then:

```text
G_n(lambda) = D_n - 2*b_n*lambda + C_n*lambda^2.
gate on v_n(lambda): G_n(lambda) <= 0.
```

The cross gates measure interaction between the two functions. Both
directions are retained; no additional cross-term symmetry is assumed.
Repeating this algebra is not the next missing mathematical input.

## Prime-cut coverage is not yet supplied by the stored model

The stored gate rig at `scripts/g1_gate_sign_rig_2718.py:113` uses:

```python
vals, logs = scan.fast_prime_powers_up_to(math.exp(2.0 * (n + 2)))
```

At n=3 this evaluates prime powers only up to exp(10). Its parent row search
uses the same cutoff at `scripts/fourpoint_gate_row_search_2032.py:131`.

The seed is a ten-fold convolution of the half-rescaled smooth seed.
`C1ExplicitSmoothSeed.lean:148` and `:154` prove its transform and support:

```text
laplaceAt poweredSeed s = laplaceAt smoothSeed ((1/2)*s)^10
support(poweredSeed) is contained in (-10,10).
```

This agrees with the transform implemented by
`scripts/fourpoint_powered_seed_1981.py:29-47`. For the n=3 carrier,
`C1RouteBPoweredSeedCarrier3110.lean:98` proves:

```text
support(poweredSeedCarrierSourceTest3110 targets nodes y)
  is contained in (-55,55).
```

This is a conservative support bound, not an exact support endpoint.
The four-point annihilator preserves the support window, as does the span.
The existing visible-prime theorem
`C1OrbitWindowSemiLocalGate.mem_globalPrimeIndexSet_convolutionSquare_lt_exp`
therefore gives q<exp(110) from this bound, where q denotes a prime power.
It does not give q<=exp(10).

```text
stored n=3 gate calculation:            log(q) <= 10
available formal carrier window:        |x| < 55
visible-prime exclusion from that bound: log(q) >= 110
missing identification:                terms with 10 < log(q) < 110
```

The final line is a coverage obligation. It is not a claim that every
prime power in that interval is visible, that any specified omitted term
is nonzero, or that exp(110) is the exact required cutoff. A sharper support
theorem, direct vanishing at the excluded prime samples, or a certified
remainder for their aggregate could reduce that obligation.

In the absence of one of those results, the stored truncated gate is not a
certificate of the current complete `finitePrimeSum`. Making the cutoff a
construction parameter does not establish that the fixed function vanishes
at the excluded sample points. If the omitted contribution is nonzero, its
sign and size must enter all three gate coefficients; the sign of the total
cannot be inferred from the truncated sign alone.

Records 2034/2035 already identify sensitivity to the cutoff and the need to
pin the visible-prime source. Their small cutoff perturbations are not
coverage proofs for the later powered-seed carrier. Record 2719 addresses
completeness of interpolation zero nodes. That is a different finite set
from the prime powers appearing in the gate.

This review preserves the old model-grade measurements on their stated
truncated book. It does not promote them to a full gate, invalidate the
conditional Lean assemblies, or claim an unconditional Route-B no-go.

## The coefficient-sign branches also need identification

`docs/proofs/2718_gate_sign_rig.md` reports C<0 on both successful model
rows. The branch solver in `g1_joint_acceptance_repricing_2716.py:76` allows
unbounded positive coefficients on the appropriate C<0 branches.

By contrast, `C1C3CarrierTransport.pinned_orbit_positive_pivot` at line 2012
proves C>0 under `HealthyYoshidaDetectorData rho g`. Its proof uses the
negative Weil value of that healthy detector. The four-point gate consumer
uses this positive pivot explicitly at
`C1FourPointSpanGateCertificate.lean:346`.

```text
stored model with C<0:          gate may allow arbitrarily large lambda
healthy detector with C>0:      positive gate coefficients are bounded above
```

These are statements under different inputs. They are not contradictory
theorems and do not prove that the numerical sign is wrong. They do show
that the old unbounded-coefficient branch cannot be inherited by a healthy
detector without proving the exact owner, normalization and full-prime
readback. In particular, C<0 model success does not establish a favorable
positive-pivot determinant for the actual function.

## The correct joint target permits shrinking coefficients

The positive coefficient floor in 3117 is sufficient; it is not necessary
for every possible sequence. Fix rho, the complete prefix, the correction
and its genuine C2 upper bound as in that proof. Put:

```text
H = (3 + norm(rho))^4 > 0
e_n = sqrt(H)*(2*pi)^6*C4*C2*(1/2)^n >= 0.
```

Here C4 is the fixed base's quartic upper constant and C2 the fixed
correction's quadratic upper constant. The specific sufficient scalar
budget used in 3117 becomes, for lambda>0:

```text
e_n^2*(1 + H/lambda)^2 < 1.
```

When 0<=e_n<1 this is equivalent to
`lambda>Ltail_n`, where `Ltail_n=H*e_n/(1-e_n)`. If e_n>=1, no positive
coefficient passes this particular budget. This is paper algebra on the
existing sufficient bound, not a new Lean leaf or a necessity theorem for
the true spectral tail.

On the C_n>0 branch, put `Delta_n=b_n^2-C_n*D_n`. If Delta_n>=0, the
upper endpoint of the gate interval is:

```text
Lplus_n = (b_n + sqrt(Delta_n))/C_n.
```

The exact scalar intersection test for this budget is `Lplus_n>Ltail_n`.
The strict tail threshold also ensures the chosen coefficient is positive.
The double-root case Delta_n=0 is allowed when that root exceeds Ltail_n.
This interval formulation was already described in records 2708 and 2713;
it is not a new mechanism.

For example, coefficients may tend to zero proportionally to e_n and still
pass, provided their ratio to e_n is eventually greater than H by a fixed
margin. Demanding an n-independent positive floor would exclude such a
possibility unnecessarily. The gate vertex minimizes the quadratic gate,
whereas the tail budget improves as lambda increases. Consequently a vertex
failure alone is insufficient: the upper part of the same gate interval
may still intersect the tail range.

The remaining content is an actual signed estimate for this intersection,
with the complete prime contribution. Seed derivative norms and transform
decay bounds control magnitudes; they do not by themselves determine the
signs of the gate coefficients or the determinant.

## Direction and acceptance boundary

The next decisive work is identification of the complete actual gate,
starting with the prime-cut remainder. It is premature to spend a large
certificate campaign tightening the stored truncated gate. Directly
enumerating a much wider prime book is not a substitute for a signed
analytic bound, and no such enumeration was attempted in this review.

After that identification, an estimate of the upper gate endpoint against
the tail threshold can remove the joint sign premise. Acceptance requires
one actual span satisfying both inequalities, with coverage for every
hypothetical right off-line source zero in the final consumer. A finite
sample at the stored heights is not that quantified proof.

This record reduces no new RH-core inequality. Its purpose is to prevent
the next round from treating an already known quadratic identity, an
unproved coefficient floor, or a truncated model gate as the missing
arithmetic argument. The 3117 theorem remains a valid actual-family
negative-qw construction under its stated premises.

## Verification

All cited source locations were read at the pinned main revision. The
cutoff, seed power and support statements were checked directly; no new
mathematical software API was assumed. The patch changes proof records
only, so it introduces no Lean module and needs no new axiom build. The
3117 source hashes and its existing twelve-leaf PASS audit remain unchanged.

## Follow-up: exact accounting and a bounded band (3119)

Record 3119 proves the signed cut-plus-remainder identity on the actual
powered spans and finite complete prime coverage for the stored span.
Its conservative open span window is (-56,56), giving the symbolic bound
ceil(exp(112)); this is not a claim that the old cutoff covers the function.

A same-owner finite-frequency model check adds only the band
10<log(q)<=12. Its signed value at n=3 and lambda=24 is about -1.06179e12,
about 9.0194 times the old gate magnitude. The old row is reproduced
bitwise, and frequency-grid and seed-rule refinements agree. This is
model evidence that the omitted band cannot be ignored, not a theorem
about the full continuum remainder. The complete gate sign remains open.

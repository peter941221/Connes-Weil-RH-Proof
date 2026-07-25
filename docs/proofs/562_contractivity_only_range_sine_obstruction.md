# Proof 562: Contractivity Is Not the Range-Sine Producer

The current Julia input already proves that the normalized Schur transfer is
contractive.  That is not enough to prove the weighted physical row

```text
(p - 1) ||rangeSine x||^2 <= ||canonicalJuliaDefect(T) x||^2.
```

The new Lean source gives an exact scalar guard.  It uses

```text
T = (79/101) I,
rangeSine = (20/101) I,
weight = 9401/400.
```

The transfer is contractive, so its canonical Julia defect is legitimate.
The Pythagorean identity gives, at `x = 1`,

```text
||defect(1)||^2 = 3960/10201,
weight * ||rangeSine(1)||^2 = 9401/10201.
```

Since `9401/10201 > 3960/10201`, the weighted estimate fails despite
contractivity.

This is an abstract contractivity-only guard.  It does not model the CCM24
graph sine, does not construct a source-specific counterexample, and does not
close or refute Gate 3U.  Its purpose is narrower: no proof may replace the
missing source detector estimate with the normalized-Schur contract alone.

Source:
`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSActualJuliaRangeSineContractivityObstruction.lean`

Audit:
`ConnesWeilRH/Dev/CCM24FiniteSActualJuliaRangeSineContractivityObstructionAudit.lean`

Primary external context:
Connes, Consani, Moscovici, "Zeta zeros and prolate wave operators",
arXiv:2310.18423v2, https://arxiv.org/abs/2310.18423.

That paper proves a hilbertian Sonin-space transport and explicitly leaves the
semilocal prolate/positivity route as future work; it does not supply this
range-sine Douglas estimate.

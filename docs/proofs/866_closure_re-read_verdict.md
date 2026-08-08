# 866 - Gate-3U closure audit: which fronts are structurally live vs need a Peter sign-off

Status: strategic/closure audit, no new Lean asserted. Date: 2026-08-07.
Lane: the three moves I proposed last session, checked against what is actually true.

## One-line read

Two of the three proposed "next closes" are **not mechanical**: the A2 carrier
swap is structurally impossible at the `SourceTestAlgebra` boundary (probe `A2`
already proved it), and the archimedean sign `Re[Gamma(a+i/2)^4] >= 0` needs a
compact-interval Stirling *argument* bound the repo's mathlib v4.30 does not
ship (862 numerical verdict).  The third (1A readout invariance) depends on the
first, so it is likewise not closable yet.  The honest closed edge today is the
finite-band Route-A Gate (`bandTerminalGate`), which is on main and axiom-clean.

## Why each proposed step cannot be slammed shut

```
Proposed step              Reduced to                                                Verdict
─────────────────────────  ────────────────────────────────────────────────────────  ──────────────
1. 1A carrier re-point     SourceTestAlgebra needs  decode: TestFunction -> Test,    Blocked: A2
   (CompactLogTest)         whose decode must make every Schwartz f compact-         proves the
                            supported; CompactLogTest is the strict compact-support   bijection
                            subtype, so no such bijection exists.                     cannot exist.
                          The real unblock is the operator/trace-class gate
                            (windowedBoundaryDetector IsPositive, A1 Seam-B bridge),
                            already materially closed in A3.

2. readout invariance         requires a re-point in (1) to exist                    depends on (1)

3. archimedean sign           Re[Gamma(a+i/2)^4] >= 0 ; 862: asymptotic arg false;   genuine gap:
   (normalization row)        needs compact-interval Stirling argument bound;         mathlib v4.30
                              mathlib lacks arg-Gamma asymptotics.                    has no such bound
```

## What the operator gate empties vs contains

A0's single-point window (`(0,0)`, traceClass = supportInWindow) is an *empty
producer* (only the zero test passes), the AGENTS §6 §11 forbidden shape.
A3's nonzero `CompactLogTest` witness shows the *operator* form of the gate is
nonempty and nonnegative: `windowedBoundaryDetector nonzeroTest a c` is
`IsSelfAdjoint` and `IsPositive`, HS-trace-class along a Hilbert basis
(`signedBoundaryOperator_*_isTraceClassAlong`).  So the *content* needed by the
"re-point the gate to non-trivial" story is already provable; what is missing is
a `SourceTestAlgebra`-level carrier whose `legacy` bijection is a *compact-support
shell*, which is a model/architecture decision, not a lemma.

## The finite-band Route-A gate is the honest closed edge

Already on main, axiom-clean:

- `finiteBand_tail_trace_le`: real-part ordinary trace of the library tail
  operator <= `(card rho) * C0 * exp(-B/4) * prod` (RouteATailBandBound).
- `finiteBandSupport_le` and the split via
  `inverseLowerFactorPhysicalRenewalTrace_split_bound` and
  `canonicalRealGate3UAt_of_tailNormBound` close `bandTerminalGate`.
- Axioms = `[propext, Classical.choice, Quot.sound]` only.

## What would genuinely unblock each front (decision gate for Peter)

| Front | Exact certificate needed | Who must decide |
|-------|--------------------------|-----------------|
| 1. Carrier non-trivial gate | an operator/trace-class gate used as `traceClass`/`cyclicLegal` (already-made witness in A3) plus a `SourceAlgebra` whose `legacy.decode` is a compact-support shell (or move the gate to operator form and drop the legacy bijection) | architecture (AGENTS §6 MUST-ASK) |
| 2. Read-only after re-point | same-owner invariance proof `old_readout = new_readout` on the swapped carrier | follows (1) |
| 3. Archimedean sign (Gamma) | a compact-validated Stirling *argument/phase* bound with explicit error on `a in [0.9,1.2]`; mathlib has no asymptotic-arg-Gamma | real analysis formalization effort |

## Recommendation

Stay honest: keep the finite-band Route-A gate as the record, do NOT manufacture
a `SourceTestAlgebra` re-point (it would either be unprovable or require an owner
change AGENTS §6 blocks without your sign-off), and do NOT claim the
archimedean sign without the Stirling-argument bound.  The two live threads are
(a) an explicit *architecture go/no-go* you give once for the operator-gate
carrier, and (b) a funded effort to ship (or extend mathlib with) the compact
Gamma-argument bound.




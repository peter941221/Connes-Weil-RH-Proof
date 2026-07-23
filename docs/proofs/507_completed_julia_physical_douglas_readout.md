# Proof 507: completed-Julia physical Douglas readout

## Result

Proof 507 turns Proof 506's physical ambient-plus-boundary domination into a
bounded readout of the complete signed mismatch adjoint. It also proves the
converse, so this readout is an exact reformulation of the still-open
domination producer. It does not prove Gate 3U, the finite-S sign, Burnol's
identity, or RH.

```text
+------------------------------------------------------+------------------+
| item                                                 | status           |
+------------------------------------------------------+------------------+
| physical analysis carrier                           | reused exactly   |
| Douglas readout under physical domination            | proved           |
| readout * physicalAnalysis = mismatch^dagger         | proved           |
| physicalAnalysis^dagger * readout^dagger = mismatch  | proved           |
| adjoint readout norm bound                           | proved           |
| physical zero-mode cancellation                      | proved           |
| readout existence <-> physical domination            | proved           |
| physical domination producer                         | still open       |
| Gate 3U / finite-S sign / Burnol identity / RH        | still open       |
+------------------------------------------------------+------------------+
```

The Lean owner is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaPhysicalDouglasReadout.lean
```

## What the readout is

Let

```text
A_phys x
  = (Q_p^dagger oldFrame x, boundary^dagger x)
```

be Proof 506's genuine orthogonal two-channel analysis column, and let

```text
J = PolarJ - RawJ
```

be Proof 505's complete signed mismatch intertwinement. The physical Douglas
condition is

```text
||J^dagger x||^2 <= C^2 ||A_phys x||^2
```

for every source-Sonin vector `x`. The operator-level Douglas theorem then
constructs

```text
readout : ambientBoundaryCarrier -> sourceSoninCarrier
```

with

```text
||readout|| <= C,
readout A_phys = J^dagger.
```

The construction extends the induced map from the range of `A_phys` to the
closure of that range and precomposes it with the orthogonal projection onto
the closure. It therefore does not assume that the physical range is closed.

## Why the adjoint direction matters

Taking adjoints gives the exact synthesis identity

```text
A_phys^dagger readout^dagger = J,
||readout^dagger|| <= C.
```

Thus the complete mismatch is synthesized from the same physical coordinates
whose Gram operator is the adjacent Julia co-defect. In particular,

```text
A_phys x = 0  ->  J^dagger x = 0.
```

No information is gained by merely postulating this readout. Proof 507 proves
the reverse implication as well: any readout with the displayed factorization
and norm bound reconstructs the original physical domination inequality.

## Remaining source theorem

The missing producer must establish a family-independent bound for the
complete row `J^dagger` against the summed physical energy

```text
||Q_p^dagger oldFrame x||^2 + ||boundary^dagger x||^2.
```

Proof 500 supplies the source-specific raw normal form

```text
Raw(S) = J0^dagger C3 H_S - G_S^dagger C3 J0.
```

The next identification must pull the complete adjacent raw intertwinement
into the same physical analysis owner. The ambient and boundary energies, and
the signed difference `PolarJ - RawJ`, must remain intact before any norm
estimate.

## Verification

The focused audit is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaPhysicalDouglasReadoutAudit.lean
```

The Ubuntu 24.04 WSL2 verification batch passed:

```text
+------------------------------------------+-------+--------+
| target                                   | jobs  | result |
+------------------------------------------+-------+--------+
| Proof 507 source build                   |  3323 | PASS   |
| Proof 507 focused axiom audit             |   n/a | PASS   |
| CCM25Concrete aggregate                  |  3784 | PASS   |
| full repository                          |  3865 | PASS   |
+------------------------------------------+-------+--------+
```

All six audited principal declarations use exactly
`[propext, Classical.choice, Quot.sound]`. The new source and audit contain no
`sorry`, `admit`, or user axiom declaration, have no line longer than 100
characters, and emit no new linter warning. Existing repository warnings are
unchanged; the WSL localhost-proxy notice is external. No commit, push, PR,
issue comment, or other public outbound action was performed.

The family-uniform physical domination, Gate 3U, the finite-S sign, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.

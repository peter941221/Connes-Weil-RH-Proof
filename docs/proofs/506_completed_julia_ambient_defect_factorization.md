# Proof 506: completed-Julia ambient-defect factorization

## Result

Proof 506 replaces the abstract ambient term in Proof 505's adjacent Schur
ledger by an explicit antiresonant translation factor and packages it with
the moving boundary in one orthogonal two-channel column. It does not prove
the physical Douglas domination, Gate 3U, the finite-S sign, Burnol's
identity, or RH.

```text
+------------------------------------------------------+------------------+
| item                                                 | status           |
+------------------------------------------------------+------------------+
| normalized Euler adjoint                             | proved           |
| ambient antiresonant product                         | proved           |
| genuine square-root loss factor                      | proved           |
| source-frame ambient pullback                        | proved           |
| ambient + boundary Gram equality                     | proved           |
| two-channel / Julia zero-kernel equivalence          | proved           |
| physical Douglas condition = Proof 505 condition     | proved           |
| physical Douglas domination itself                  | still open       |
| Gate 3U / finite-S sign / Burnol identity / RH       | still open       |
+------------------------------------------------------+------------------+
```

The Lean owner is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaAmbientDefectFactorization.lean
```

## Antiresonant ambient loss

Put

```text
a_p = p^(-1/2),
U_- = U_(-log p),
U_+ = U_(log p),
T_p = (1+a_p)^(-1)(I-a_p U_-).
```

The genuine translation adjoint is `U_-^dagger=U_+`. Lean proves

```text
I-T_p T_p^dagger
  = a_p/(1+a_p)^2 (I+U_-)(I+U_+).
```

The signs matter. The loss is concentrated in the antiresonant channel
`I+U_-`, not the resonant Euler factor `I-a_p U_-` itself.

Define

```text
s_p = sqrt(a_p)/(1+a_p),
Q_p = s_p (I+U_-).
```

The scalar identity `s_p^2=a_p/(1+a_p)^2` gives the genuine Gram
factorization

```text
I-T_p T_p^dagger = Q_p Q_p^dagger.
```

No positivity premise is stored by hand. The square root uses the proved
nonnegativity of `a_p`.

## Actual source-frame owner

Let `oldFrame` be the actual preceding suffix polar frame and let `boundary`
be the moving-frame boundary row from the adjacent Schur step. Proof 506
defines

```text
ambientColumn = Q_p^dagger oldFrame,
physicalAnalysis x = (ambientColumn x, boundary^dagger x).
```

The pair is carried by an `L2` product, so its coordinates are orthogonal.
Substitution into Proof 505's ledger gives

```text
physicalAnalysis^dagger physicalAnalysis = D^dagger D,

||D x||^2
  = ||ambientColumn x||^2 + ||boundary^dagger x||^2,
```

where `D` is the actual adjacent left Julia co-defect. Hence

```text
D x = 0
  <-> ambientColumn x = 0 and boundary^dagger x = 0.
```

This is stronger bookkeeping than the earlier one-way boundary kernel
statement, but it is still not an estimate for the complete mismatch row.

## Remaining Douglas gate

Proof 505 asks for

```text
||J^dagger x||^2 <= C^2 ||D x||^2,
```

where `J` is the complete signed polar/raw mismatch intertwinement. Proof 506
proves that this is exactly

```text
||J^dagger x||^2
  <= C^2 (
       ||Q_p^dagger oldFrame x||^2
       + ||boundary^dagger x||^2).
```

The sum on the right is one physical owner. The two channels must not be
estimated separately before the complete `RawJ^dagger` row has been pulled
into these coordinates. Proof 500's outer, reflected-outer, second-support,
and prolate normal form remains the source for that next identification.

## Verification

The focused audit is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaAmbientDefectFactorizationAudit.lean
```

Every audited theorem must remain axiom-clean with exactly

```text
[propext, Classical.choice, Quot.sound]
```

The Ubuntu 24.04 WSL2 verification batch passed:

```text
+------------------------------------------+-------+--------+
| target                                   | jobs  | result |
+------------------------------------------+-------+--------+
| Proof 506 source build                   |  3322 | PASS   |
| Proof 506 focused axiom audit             |   n/a | PASS   |
| CCM25Concrete aggregate                  |  3783 | PASS   |
| full repository                          |  3864 | PASS   |
+------------------------------------------+-------+--------+
```

All fourteen audited principal declarations use exactly
`[propext, Classical.choice, Quot.sound]`. The new source and audit contain
no `sorry`, `admit`, or user axiom declaration, have no line longer than 100
characters, and emit no new linter warning. Existing repository warnings are
unchanged; the WSL localhost-proxy notice is external. No commit, push, PR,
issue comment, or other public outbound action was performed.

The finite-S sign, Gate 3U, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.

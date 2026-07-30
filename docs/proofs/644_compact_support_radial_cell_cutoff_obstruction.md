# Proof 644: compact-support radial-cell cutoff obstruction

## Result

The result is negative at the support-only level.

Compact support can make a sufficiently translated crossing have zero scalar
trace.  It does not make the complete crossing operator zero, and therefore
does not force Proof 641's complete coupled cofactor to depend on finitely many
Euler radial cells.

The distinction is

```text
compact root support
        |
        +--> distant autocorrelation = 0
        |         |
        |         v
        |     scalar trace = 0
        |
        X--> completed crossing operator = 0
                  |
                  X--> finite radial-prefix factorization
```

The last two arrows require a new source-specific cancellation theorem.  They
do not follow from support.

## Actual CCM24 kernel guard

For the full Proof 641 cofactor, Lean now proves the direct contrapositive:
if one source vector `x` satisfies

```text
finiteRadialColumn_(p,S,N) x = 0,
completeCoupledCofactor_(p,S) x != 0,
```

then no bounded readout through the first `N` cells exists, at any norm bound.
The theorem is

```text
not_nonempty_finiteRadialReadoutData_of_tail_witness
```

This treats the complete cofactor as one operator.  Its outer, reflected,
second-support, and prolate branches are never separated.

## Exact finite crossing obstruction

The support-only failure is not merely a missing proof.  On any finite carrier
with distinct labels `input` and `output`, define the whole crossing matrix

```text
K(i,j) = 1  if (i,j) = (output,input),
         0  otherwise.
```

Let `P_input` and `P_output` be the singleton coordinate projections.  Lean
proves

```text
P_output K P_input = K,
Tr(K) = 0,
K != 0.
```

Thus the input and output supports are disjoint, so the diagonal correlation
and trace vanish exactly, but the completed off-diagonal crossing survives.
For every finite coordinate window `A` which omits `input`, Lean also proves

```text
not exists F, F P_A = K.
```

Indeed `P_A e_input = 0` while `K e_input = e_output`.  This is precisely the
kernel mechanism behind Proof 641's finite-column condition.

The relevant theorem names are

```text
singletonProjection_mul_crossing_mul_singletonProjection
trace_supportSeparatedCrossing_eq_zero
supportSeparatedCrossing_ne_zero
supportSeparatedCrossing_not_factor_through_coordinateProjection
separated_singleton_support_trace_zero_but_no_operator_cutoff
```

## Route judgment

```text
+------------------------------------------------------+----------------------+
| statement                                            | status               |
+------------------------------------------------------+----------------------+
| compact support cuts off distant scalar correlation | proved/model-exact   |
| zero distant scalar trace                            | proved/model-exact   |
| completed distant crossing is zero                   | false abstractly     |
| support alone gives finite radial-prefix ownership   | false abstractly     |
| actual CCM24 cofactor has a tail witness             | open                 |
| actual CCM24 cofactor has a finite-cell collapse     | open                 |
| Bone 1                                               | open                 |
| Gate 3U / finite-S sign / Burnol identity / RH       | open                 |
+------------------------------------------------------+----------------------+
```

The finite model does not assert that the actual CCM24 branches fail to cancel
after their complete signed recombination.  It proves the sharper logical
boundary needed here: compact root support by itself cannot be the producer of
an operator-level finite radial cutoff.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorCompactSupportCellCutoffObstruction.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorCompactSupportCellCutoffObstructionAudit.lean
```

## Verification

The independent Ubuntu-24.04 WSL2 ext4 build passed under the shared Lake
lock:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| compact-support cutoff source        |  3393 | PASS   |
| focused eight-declaration audit      |  3394 | PASS   |
+--------------------------------------+-------+--------+
```

All eight audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, `admit`, or user axiom
was added.

Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.

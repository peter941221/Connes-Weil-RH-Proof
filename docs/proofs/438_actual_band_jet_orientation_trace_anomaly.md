# Proof 438: actual band-jet orientation and trace-anomaly owner

Date: 2026-07-20

Status: exact Lean identification of the actual normalized-inverse band jet,
its difference from Proof 436's paired jet, and the residual commutator which
must not be removed by an unaudited infinite-dimensional trace cycle.

The result is good as a direction repair.  It does not bound the orientation
commutator or the quadratic endpoint remainder, close Gate 3U, prove the
finite-`S` sign, prove Burnol's identity, or prove RH.

## 1. Verdict

```text
+----------------------------------------------------------+----------------------+
| statement                                                | judgment             |
+----------------------------------------------------------+----------------------+
| actual target projection has one ambient Gram owner      | Lean proved          |
| actual band jet is `B_0 N_S R_0+R_0 N_S^* B_0`          | Lean proved          |
| Proof 436 uses the opposite paired orientation           | exact                |
| their operator difference is a compressed-skew commutator| Lean proved          |
| detector multiplication has fixed + residual commutators | Lean proved          |
| commuting detector cancels the finite-matrix trace       | probe confirms       |
| noncommuting detector can see an order-one trace gap      | probe confirms       |
| the residual infinite-dimensional trace is zero          | not proved           |
| Gate 3U / finite-S sign / Burnol / RH                    | open                 |
+----------------------------------------------------------+----------------------+
```

## 2. What the direction issue is

On the literal CCM24 common-log carrier put

```text
E   =radialSupportProjection,
R_0 =sourceSoninProjection,
B_0 =E-R_0,
N_S =normalizedFiniteEulerInverse.                         (AB.1)
```

The common-support splitting is

```text
E=B_0+R_0,       B_0 R_0=0,       R_0 B_0=0.              (AB.2)
```

Proof 436 and the actual band endpoint point in opposite directions:

```text
                 source range              target range
                       |                         |
Proof 436 pair:        R_0 ---- N_S ----> B_0   + adjoint

actual band pair:      B_0 ---- N_S ----> R_0   + adjoint. (AB.3)
```

In formulas,

```text
J_436 =R_0 N_S B_0+B_0 N_S^* R_0,
J_band=B_0 N_S R_0+R_0 N_S^* B_0.                         (AB.4)
```

Both are Hermitian, but they are not the same operator.  Hermitian completion
adds the adjoint of one crossing; it does not reverse the direction of the
underlying `N_S` block.

## 3. Exact commutator owner

Define the compressed skew part

```text
K_S=E N_S E-(E N_S E)^*.                                  (AB.5)
```

Expanding `E=B_0+R_0` and using `(AB.2)` gives

```text
[R_0,K_S]
 =R_0 N_S B_0+B_0 N_S^* R_0
  -B_0 N_S R_0-R_0 N_S^* B_0
 =J_436-J_band.                                           (AB.6)
```

Lean proves `(AB.6)` first over an arbitrary noncommutative ring, then on the
actual Hilbert carrier.  It also proves that the concrete `K_S` in `(AB.5)`
is genuinely an operator minus its Hilbert adjoint.

The actual endpoint ledger is therefore

```text
B_S-B_0
 =J_band-Q_S
 =J_436-[R_0,K_S]-Q_S,                                   (AB.7)
```

where `Q_S` is the exact sum of the two-factor gauge correction and Proof
437's Gram quadratic remainder.  The orientation commutator is first order;
it must not be relabeled as part of the quadratic remainder.

## 4. Why finite trace cancellation is not enough

For any detector `W`, Lean proves the operator identity

```text
W[R_0,K_S]=[W,R_0]K_S+[R_0,W K_S].                       (AB.8)
```

This is the exact trace-anomaly ledger:

```text
W times orientation defect
        |
        +-- [W,R_0] K_S       fixed source commutator
        |
        +-- [R_0,W K_S]       residual commutator
                                  |
                                  +-- finite matrices: trace is zero
                                  +-- infinite carrier: legality required.
```

In finite dimension cyclicity gives

```text
Tr(W[J_436-J_band])=Tr([W,R_0]K_S).                       (AB.9)
```

If `W` commutes with `R_0`, the right side vanishes.  A noncommuting detector
can give a nonzero value.  On the actual infinite carrier, deleting the final
commutator in `(AB.8)` requires the relevant products to be trace class in an
order for which cyclicity is valid.  Proof 264 already guards against assuming
that conclusion from finite sections.  Proof 438 proves `(AB.8)` only as an
operator identity and makes no trace-zero claim.

## 5. Finite certificate

The interrupted direction screen first reported the unnormalized sample

```text
operator_gap=2.885868507798552e+00
commuting_detector_trace_gap=4.427030979816108e-16
noncommuting_detector_trace_gap=9.063460424889641e+00.     (AB.10)
```

The permanent probe uses a separately generated sample and normalizes the
inverse candidate by its operator norm.  It therefore tests the same
identities without claiming that the magnitudes in `(AB.10)` are invariant.

Command:

```text
python3 docs/proofs/438_actual_band_jet_orientation_trace_anomaly_probe.py
```

Default output:

```text
Proof 438 actual band-jet orientation certificate
orientation_identity_error=0.000000000000000e+00
detector_ledger_error=1.156345336599160e-16
compressed_skew_adjoint_error=0.000000000000000e+00
operator_gap=1.153858294936112e+00
commuting_detector_trace_gap=0.000000000000000e+00
noncommuting_detector_trace_gap=6.865275161227135e-01
finite_trace_cycle_error=0.000000000000000e+00
paired_operators=DIFFERENT
finite_commuting_detector_trace=CANCELS
infinite_trace_cycle=NOT_AUTHORIZED
gate_3u=OPEN
RH=UNPROVED                                                (AB.11)
```

The operator gap is order one, so the directions are genuinely different.
The two algebraic identities hold to floating-point precision.  The
commuting detector cancels only after the finite-dimensional trace, while the
noncommuting detector retains a visible response.

## 6. Lean ownership and axioms

The source and focused audit are

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualBandJetOrientation.lean

ConnesWeilRH/Dev/
  CCM24FiniteSActualBandJetOrientationAudit.lean.          (AB.12)
```

The central declarations are

```text
quotientPairedFirstJet_sub_normalizedInverseBandPair_eq_commutator
sourceFiniteEulerCompressedSkew_eq_compression_sub_adjoint
sourceFiniteEulerPairedFirstJet_sub_actualBandPair_eq_orientation
detector_comp_orientationCommutator_eq_fixed_add_residual
soninBandDifference_eq_proof436Pair_sub_orientation_sub_quadratic.
```

The two generic ring identities use exactly `[propext]`.  Every audited
actual-carrier theorem uses exactly

```text
[propext, Classical.choice, Quot.sound].                   (AB.13)
```

No project axiom, trace premise, or proof placeholder is introduced.

The isolated Ubuntu 24.04 ext4 acceptance batch passes:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| actual band-jet focused axiom audit                  |  3261 | PASS   |
| CCM25Concrete aggregate                              |  3711 | PASS   |
| full repository                                      |  3792 | PASS   |
+------------------------------------------------------+-------+--------+
```

The focused audit has `18` `#check` commands and `18` matching
`#print axioms` commands.  The new source and audit contain no `sorry`,
`admit`, or `sorryAx`, add no line longer than 100 characters, and introduce
no new warning.  Aggregate and full builds replay only pre-existing warnings.

## 7. Remaining bottom

Proof 436 uniformly controls the fixed source commutator `[W,R_0]`, and
`norm(K_S)<=2` follows formally from the normalized inverse contraction and
support projections.  This controls the first summand of `(AB.8)` at the
trace-ideal level.  It does not remove the residual commutator trace.

The next accepted result must do both of the following on the actual
root-smoothed ordinary-trace owner:

```text
1. prove a legal cancellation or a source-specific bound for
   Tr([R_0,W K_S]);

2. bound the complete quadratic ledger Q_S without separating the physical
   detector bracket before the first absolute value.                       (AB.14)
```

Until those two terms are controlled uniformly in the visible finite family,
Gate 3U and RH remain open.

# Proof 750: Gate Physical Normalized Anomaly Boundary Readout

## Result

The result is good: Proof 750 identifies Proof 749's abstract pure-imaginary
Gram-order anomaly with an actual two-sided physical coframe boundary.  It
does not close Gate 3U or prove that the anomaly vanishes.

Use the notation

```text
J      = sourceInclusion,
R      = J J^dagger,
Hhat_S = c_S^(-2) H_S,
Ahat_S = c_S^2 G_S^(-1),
Phat_S = J Ahat_S J^dagger,
D      = [W,R],
M_S    = [R,Hhat_S],
L_S    = sourcePhysicalCoframeLeakage_S.
```

Lean proves

```text
Phat_S M_S-M_S Phat_S
  =J L_S^dagger+L_S J^dagger,                       (AB.1)

Tr_source(Anom_S)
  =1/2 Tr_ambient(D (J L_S^dagger+L_S J^dagger)).   (AB.2)
```

The right side of `(AB.2)` is trace legal for every fixed finite family via
the completed four-branch Hilbert--Schmidt pair.  It is one signed object,
not permission to estimate the two leakage orientations separately.

```text
+----------------------------------------+----------------------------------+
| layer                                  | result                           |
+----------------------------------------+----------------------------------+
| source anomaly                         | exact double-boundary commutator |
| lifted normalized inverse Gram         | self-adjoint                     |
| lifted metric commutator               | bidirectional physical leakage   |
| source-to-ambient rectangular cycle    | legal through completed S2 pair  |
| ambient anomaly readout trace legality | closed for each fixed family     |
| anomaly cancellation                   | not proved                       |
| family-uniform signed estimate         | open                             |
| Gate 3U / finite-S sign / RH           | open                             |
+----------------------------------------+----------------------------------+
```

## 1. What It Is

Proof 748 writes the anomaly as the inverse normalized source Gram applied to
the difference of the left- and right-ordered normalized boundaries.  Proof
750 first makes both ambient orders explicit:

```text
Left_S  =J^dagger M_S D J,
Right_S =J^dagger D M_S J,

Anom_S
  =1/2 Ahat_S J^dagger (M_S D-D M_S) J.              (AB.3)
```

Both `D` and `M_S` are skew-adjoint.  Their two negatives cancel when the
left boundary is adjointed, which is why the right numerator has the reverse
order in `(AB.3)` rather than an extra sign.

The scalar gauges also cancel before any estimate:

```text
Hhat_S J Ahat_S
  =(c_S^(-2) H_S) J (c_S^2 G_S^(-1))
  =H_S J G_S^(-1)
  =finiteEulerMetricCoframe_S.                       (AB.4)
```

The complete coframe is

```text
finiteEulerMetricCoframe_S=J+L_S.                    (AB.5)
```

Here `L_S` still contains the outer, reflected second-support, and prolate
branches.  No branch has been removed or bounded separately.

## 2. Why The Lifted Commutator Is Physical

Let `C_S=J+L_S` be the metric coframe.  Biorthogonality gives

```text
J^dagger C_S=I,
C_S^dagger J=I.
```

Using `(AB.4)`, Lean derives

```text
Hhat_S Phat_S=C_S J^dagger,
Phat_S Hhat_S=J C_S^dagger.
```

The source-range identities `Phat_S R=Phat_S` and `R Phat_S=Phat_S` then
give

```text
Phat_S M_S-M_S Phat_S
  =Phat_S Hhat_S+Hhat_S Phat_S-2R
  =J C_S^dagger+C_S J^dagger-2J J^dagger
  =J L_S^dagger+L_S J^dagger.
```

This proves `(AB.1)`.  The anomaly is therefore not an unnamed failure of
cyclicity: it is the detector paired with the two orientations of the actual
off-Sonin coframe.

## 3. Why The Rectangular Trace Cycle Is Legal

The existing completed physical pair owns the ambient detector boundary:

```text
data.traceProduct=D=[W,R].
```

The minus sign converting the CC20 orientation `[R,W]` to `[W,R]` stays in
the pair's right Hilbert--Schmidt leg.  For rectangular bounded maps
`Left,Right : source -> ambient`, Proof 750 constructs the pulled pair

```text
left leg  =data.left  Left,
right leg =data.right Right.
```

Its source trace product is

```text
Left^dagger D Right.
```

Cycling both this pair and the corresponding ambient bounded sandwich to the
same compact boundary carrier proves

```text
Tr_source(Left^dagger D Right)
  =Tr_ambient(D Right Left^dagger).                   (AB.6)
```

Apply `(AB.6)` twice:

```text
Tr_source(Ahat_S J^dagger M_S D J)
  =Tr_ambient(D Phat_S M_S),

Tr_source(Ahat_S J^dagger D M_S J)
  =Tr_ambient(D M_S Phat_S).                         (AB.7)
```

Fixed-family trace additivity and `(AB.1)` turn `(AB.7)` into `(AB.2)`.
This cycle is backed by concrete square-summable factors on both cuts; no
generic `Tr(AB)=Tr(BA)` rule for arbitrary bounded operators is used.

## 4. What It Does Not Prove

Equation `(AB.2)` does not imply zero.  It replaces the missing source versus
ambient endpoint trace identity from Proof 749 with the exact boundary term
that the old cycle omitted.

The two summands

```text
D J L_S^dagger,
D L_S J^dagger
```

must remain recombined.  Separate trace-norm estimates would forget the
compact-root signed cancellation and can recover the rejected Euler condition
number.  Likewise, fixed-family trace legality does not provide constants
uniform in the visible prime set.

```text
Proof 749: anomaly is pure imaginary
                  |
                  v
Proof 750: anomaly = actual two-sided physical boundary
                  |
                  | missing detector-specific signed estimate
                  v
Gate 3U: still open.                                  (AB.8)
```

The next valid producer must estimate the complete scalar in `(AB.2)`, with
compact-root support applied before the first absolute value, or prove a
source-specific cancellation of that same scalar.  Abstract self-adjointness,
separate Hilbert--Schmidt norms, and finite-dimensional trace cyclicity do not
supply either conclusion.

## 5. Lean Ownership

The source module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSGatePhysicalNormalizedAnomalyBoundaryReadout.lean
```

The import-facing audit is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSGatePhysicalNormalizedAnomalyBoundaryReadoutAudit.lean
```

The principal declarations are

```text
finiteEulerNormalizedGramSimilarityAnomaly_eq_doubleBoundaryCommutator
finiteEulerNormalizedInverseGramLift
normalizedAmbientGram_comp_inclusion_comp_sourceGramInv
finiteEulerMetricCoframe_eq_inclusion_add_physicalLeakage
sourceBidirectionalPhysicalCoframeBoundary
normalizedInverseGramLift_metricBoundary_commutator_eq_physical
finiteEulerNormalizedPhysicalAnomalyBoundaryReadout
finiteEulerNormalizedPhysicalAnomalyBoundaryReadout_isTraceClassAlong
ordinaryTraceAlong_normalizedGramSimilarityAnomaly_eq_physicalBoundary
```

## 6. Verification

The accepted Ubuntu 24.04 WSL2 ext4 batches were:

```text
+-------------------+-----------+
| batch             | result    |
+-------------------+-----------+
| focused + audit   | 3394/3394 |
| aggregate + audit | 4019/4019 |
| full repository   | 4099/4099 |
+-------------------+-----------+
```

The aggregate batch built
`ConnesWeilRH.Source.CCM25Concrete` together with the Proof 750 audit.  The
full batch ran `lake build`.  Existing repository warnings were replayed;
the new source and audit introduced no warning.

All twelve audited public theorems have exactly the following axiom set:

```text
[propext, Classical.choice, Quot.sound]
```

The final Windows/WSL SHA-256 values match byte for byte:

```text
+-----------+------------------------------------------------------------------+
| artifact  | SHA-256                                                          |
+-----------+------------------------------------------------------------------+
| source    | 6cf47059ff4fd4e7e0f47e7bb7a2b349640b43b016ddc90eac52172f3b5cdb29 |
| audit     | 96db7f8bdf734e713c4eb4f908e3f60f846353384f1cb60a974517d9eef7d19c |
| aggregate | 637aa39fa10f5b39e1102760e6ed5c05de18b97eb8d96af78cee4a8b20eb4957 |
+-----------+------------------------------------------------------------------+
```

Static checks found no `sorry`, `admit`, user axiom, heartbeat increase,
recursion-limit increase, unsafe declaration, line over 100 characters, or
trailing whitespace in the new source and audit.

Gate 3U, the finite-S sign, the arithmetic same-object identity, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.

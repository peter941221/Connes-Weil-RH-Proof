# Proof 403: ambient nested-band first-variation guard

Date: 2026-07-18

Status: exact first-variation identity for a simultaneous ambient transport
of two nested projections.  For `R<=E`, the coherent
`R`--outer-complement channel cancels algebraically.  The surviving derivative
is the outer `C`--`B` crossing minus the inner `R`--`B` crossing.

This is an ambient-path guard, not the first derivative of Proof 343's fixed
quotient path.  The earlier route interpretation of this identity was too
strong and is withdrawn below.  Nesting, detector positivity, and transport
commutation do not make the ambient derivative vanish abstractly.  Gate 3U,
the finite-`S` sign, Burnol's identity, and RH remain open.

## 1. Projection variation

Let `U` be a unitary and

```text
P_a=projection onto (I-aU)^(-1)Ran(P).           (NV.1)
```

Differentiating the canonical Gram projection at `a=0` gives

```text
P_0'
 =(I-P)UP+PU*(I-P).                              (NV.2)
```

This is the off-diagonal tangent of the Grassmannian.  It has no diagonal
part relative to `P`.

## 2. Two nested supports

Let

```text
R<=E,
B=E-R,
C=I-E.                                          (NV.3)
```

Apply `(NV.2)` to `E` and `R`.  Direct expansion gives

```text
E_0'-R_0'

 =CUB+BU*C-BUR-RU*B.                             (NV.4)
```

The `C`--`R` terms cancel exactly.  Equation `(NV.4)` has the physical form

```text
outer boundary C <-> B
  minus
inner Sonin boundary R <-> B.                    (NV.5)
```

For a self-adjoint detector `W`, the first derivative of the relative
response is

```text
d/da Tr[W(E_a-R_a)] at a=0
 =Tr[W(CUB+BU*C-BUR-RU*B)].                      (NV.6)
```

The root-completed infinite-dimensional version of `(NV.6)` uses the same
two-sided crossing legality as Proofs 385--387.

## 3. Carrier boundary

Proof 343 does not transport both `E` and `R` by the same ambient operator.
It fixes the quotient carrier `E H`, puts

```text
P=E-R,
A_a=E(I-aU)^(-1)E |_EH,                         (NV.7)
```

and transports only `P` inside `E H`.  Its infinitesimal compressed generator
is

```text
X=EUE |_EH.                                      (NV.8)
```

The corresponding quotient derivative is

```text
P_0'=RXP+PX*R.                                   (NV.9)
```

Equation `(NV.9)` is generally different from `(NV.4)`.  In particular,
`(NV.4)` contains the motion of the outer carrier `E`, while `(NV.9)` keeps
that carrier fixed.  Proofs 365--368 explain how compression produces
mandatory detector commutators; they do not identify the two projection
paths.

Therefore `(NV.4)` may not be substituted into Proof 400's local trace
cocycle without a separate coordinate-equivalence theorem.  No such theorem
is currently proved.

## 4. What does not follow abstractly

Even when

```text
W>0,
[W,U]=0,
R<=E,                                           (NV.10)
```

the scalar in `(NV.6)` need not vanish.  A finite spectral model in the
companion probe satisfies all three conditions and has a nonzero two-boundary
derivative.  Therefore no theorem based only on positivity, commutation, and
nesting can remove the `p^(-1/2)` channel.

This guard applies to the ambient path only.  It does not decide whether the
actual quotient derivative `(NV.9)` vanishes or has an extra half-power.

## 5. Correct next target

The next step is an ownership theorem, not an estimate of `(NV.6)`:

```text
differentiate Proof 343's fixed-quotient Gram projection
  -> retain Proof 365's compressed-detector commutator
  -> substitute R=E Q_f E-K_prol inside the resulting scalar
  -> identify the actual signed first-variation owner.          (NV.11)
```

Only after `(NV.11)` is closed may one ask whether the quotient first
variation cancels, telescopes, or satisfies a compact-support estimate.

## 6. Reproducible certificate

The companion probe checks `(NV.2)--(NV.6)` against symmetric finite
differences for a random commuting spectral detector.  It also verifies
nesting and positivity while requiring the surviving derivative to be
nonzero.

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/403_nested_band_first_variation_probe.py
```

## 7. Route judgment

```text
+-----------------------------------------------+---------------------------+
| layer                                         | judgment                  |
+-----------------------------------------------+---------------------------+
| ambient nested first variation                 | exact `(NV.4)`          |
| coherent `C`--`R` channel                     | cancels exactly          |
| abstract vanishing from nesting/positivity     | false                    |
| fixed-quotient route ownership                 | not supplied here       |
| quotient first-variation theorem `(NV.11)`     | open, active producer   |
| Gate 3U / finite-S sign / Burnol / RH          | open / open / open / open|
+-----------------------------------------------+---------------------------+
```

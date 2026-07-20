# Proof 427: Weighted-boundary resolvent collapse

Date: 2026-07-20

Status: exact noncommutative reduction of Proof 415's two normalized weighted
boundary semicommutators to one relative weight crossing.  The reduction
closes an operator-ownership ambiguity, but the Proof 417 rank-one family
shows that it does not by itself give the polynomial Gate 3U estimate.

This proof does not close Gate 3U, prove the finite-`S` sign, prove Burnol's
identity, or prove RH.

## 1. Result

```text
+------------------------------------------------------+----------------------+
| statement                                            | judgment             |
+------------------------------------------------------+----------------------+
| fixed-complement retraction resolvent                 | exact                |
| moving-complement retraction resolvent                | exact                |
| two normalized boundary terms have one owner          | exact                |
| weight difference occurs exactly once                 | exact                |
| endpoint Gram amplification disappears                | false exactly        |
| Proof 416 `(EN.7)`                                    | still open           |
| Gate 3U / RH                                          | open / unproved      |
+------------------------------------------------------+----------------------+
```

The useful change in bookkeeping is

```text
two separately normalized boundary forms
  -> cancel their common source compression
  -> one relative weight crossing through one complement.       (WR.1)
```

The remaining obstruction is visible in the same formula: the new endpoint
Gram inverse remains on the left, and the complete weight difference can
amplify a small detector crossing.

## 2. Weighted frame algebra

Let `J : K -> H` be a source frame, let `J*` denote its displayed adjoint, and
let `H_i` be two ambient weights.  Put

```text
G_i=J* H_i J,
R_i=G_i^(-1)J*H_i,
O_i=J R_i,
deltaH=H_1-H_0.                                      (WR.2)
```

Assume the displayed Gram inverses are two-sided.  Then

```text
R_i J=I,
O_i^2=O_i,
(I-O_i)J=0.                                          (WR.3)
```

Thus `O_i` is the weighted oblique projection onto the fixed frame range.
It is not asserted to be orthogonal or self-adjoint.

The exact fixed-complement resolvent is

```text
R_1-R_0
 =G_1^(-1)J* deltaH (I-O_0).                         (WR.4)
```

Indeed, expanding only in the displayed order gives

```text
G_1^(-1)J*deltaH(I-JR_0)
 =G_1^(-1)J*deltaH
  -G_1^(-1)(G_1-G_0)G_0^(-1)J*H_0
 =R_1-R_0.                                           (WR.5)
```

The symmetric moving-complement identity is

```text
R_1-R_0
 =G_0^(-1)J* deltaH (I-O_1).                         (WR.6)
```

Equations `(WR.4)` and `(WR.6)` are noncommutative resolvent identities.  No
trace cycle, determinant, positivity, or limiting argument is used.

## 3. Collapse of Proof 415's boundary difference

For a detector `W`, define the ordered boundary semicommutator

```text
mathcalB_(H_i)(W)
 =J*H_i WJ-G_i J*WJ.                                 (WR.7)
```

Left Gram inversion gives

```text
G_i^(-1)mathcalB_(H_i)(W)
 =R_i WJ-J*WJ.                                       (WR.8)
```

The second term in `(WR.8)` is independent of the weight.  It therefore
cancels algebraically before any trace is formed:

```text
G_1^(-1)mathcalB_(H_1)(W)
 -G_0^(-1)mathcalB_(H_0)(W)
 =(R_1-R_0)WJ

 =G_1^(-1)J*deltaH(I-O_0)WJ                         (WR.9)

 =G_0^(-1)J*deltaH(I-O_1)WJ.                        (WR.10)
```

For Proof 415, take

```text
H_1=M_(h_S),       h_S=|g_0 tau_S|^2,
H_0=M_(h_0),       h_0=|g_0|^2,
W=M_(w_F).                                             (WR.11)
```

At the form level, `(WR.9)` is the single relative owner of

```text
Lambda_S(F)
 =Tr[G_S^(-1)mathcalB_(h_S)(w_F)
     -G_0^(-1)mathcalB_(h_0)(w_F)].                  (WR.12)
```

Equation `(WR.12)` continues to mean one already completed trace-class
difference.  It does not assert that either summand or either unbounded
ambient multiplication operator exists separately on Burnol's carrier.

## 4. Proof 417 pressure test

The collapse does not remove endpoint amplification.  Reuse Proof 417's
rank-one family on `C^2`:

```text
epsilon=exp(-M),
p=(sqrt(1-epsilon),sqrt(epsilon)),
J z=z p,

H_0=I,
H_1=diag(1,epsilon^(-1)),
W=diag(0,1).                                         (WR.13)
```

Then

```text
G_0=1,
G_1=2-epsilon,
O_0=|p><p|.                                          (WR.14)
```

Direct substitution into the new fixed-complement owner gives

```text
G_1^(-1)J*(H_1-H_0)(I-O_0)WJ
 =(1-epsilon)^2/(2-epsilon)
 =1/(2-epsilon)-epsilon
 ->1/2.                                              (WR.15)
```

The detector crossing before the weight is small, but
`H_1-H_0=diag(0,epsilon^(-1)-1)` restores an order-one response.  Notice that
`G_1` itself is uniformly bounded away from zero in this example.  Therefore
the obstruction is not merely an ill-conditioned finite Gram matrix; it is
the coupled weighted crossing retained by `(WR.9)`.

This proves that the implication

```text
one occurrence of `deltaH`
  -> polynomial endpoint bound                              (WR.16)
```

is false without source-specific cancellation.  A valid estimate must keep
the full outer-minus-Sonin/prolate Burnol geometry and exploit the canonical
Euler family before taking an absolute value.

## 5. Lean ownership

The module

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSWeightedBoundaryResolvent.lean
```

formalizes `(WR.3)--(WR.10)` over an arbitrary noncommutative ring.  The
rectangular Hilbert-space frame can be read in a common block-operator ring;
the theorem itself needs only ordered multiplication and two-sided Gram
inverse identities.  The audit module is

```text
ConnesWeilRH/Dev/CCM24FiniteSWeightedBoundaryResolventAudit.lean.
```

The abstraction deliberately contains no trace or analytic claim.  The next
producer must identify Proof 415's form-level objects with `(WR.9)` and prove
the support-polynomial signed estimate on the complete canonical family.

## 6. Route verdict

```text
What is closed:
  exact relative weighted-boundary ownership;
  fixed and moving oblique-complement resolvents;
  cancellation of the common source compression.

What remains open:
  continuous form-level realization of the single owner;
  canonical-family support-polynomial bound `(EN.7)`;
  Gate 3U and the finite-S sign;
  same-object arithmetic trace identity;
  negative-owner integration and Burnol's all-zero identity;
  unconditional RH.
```

The correct successor is not another generic resolvent inequality.  It is a
source-specific estimate for the whole signed operator in `(WR.9)`, with
`h_S-h_0` retained once and the outer/Sonin/prolate branches recombined before
the first absolute value.

## 7. Verification

The Windows source was copied one way into the isolated Ubuntu 24.04 ext4
verification directory.  The batched Lean acceptance is

```text
+----------------------------------------------+------+
| target                                       | jobs |
+----------------------------------------------+------+
| focused Proof 427 axiom audit                | 1408 |
| `ConnesWeilRH.Source.CCM25Concrete` aggregate | 3702 |
| full repository                              | 3783 |
+----------------------------------------------+------+
```

All nine audited public theorems depend exactly on `[propext]`.  No `sorryAx`,
new project axiom, placeholder proof, or new warning was introduced.  The
warnings replayed by the aggregate and full build belong to existing modules.

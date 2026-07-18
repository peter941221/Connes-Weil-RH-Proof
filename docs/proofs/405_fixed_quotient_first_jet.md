# Proof 405: fixed-quotient first jet

Date: 2026-07-18

Status: exact first derivative of Proof 343's fixed-quotient Gram projection.
After taking the legal compact-root scalar, the full detector correction
collapses to one commutator corner.  The CC20 identity then reduces that corner
to a reflected second-support crossing plus one prolate-root leg.

This repairs the carrier overclaim in the original interpretation of Proof
403 and closes the first-jet ownership problem.  It does not estimate the
remaining two branches uniformly, prove Gate 3U, the finite-`S` sign, Burnol's
identity, or RH.

## 1. Result

```text
+-----------------------------------------------+---------------------------+
| layer                                         | judgment                  |
+-----------------------------------------------+---------------------------+
| fixed quotient carrier `E H`                  | retained                 |
| Gram-corrected first derivative               | exact                    |
| scalar detector correction                    | one commutator corner   |
| CC20 outer/second/prolate ledger               | inserted exactly        |
| scalar first-jet branches                     | second support + prolate|
| complete first-jet bound                      | open                    |
| Gate 3U / finite-S sign / Burnol / RH          | open / open / open / open|
+-----------------------------------------------+---------------------------+
```

## 2. Actual quotient path

Work on the fixed quotient carrier `E H`.  Put

```text
R<=E,
P=E-R,
P=U_0 U_0*.                                      (FQ.1)
```

Let the ambient inverse Euler factor have expansion

```text
V_a=I+aU+O(a^2),                                  (FQ.2)
```

and compress it before transporting the quotient band:

```text
A_a=E V_a E |_EH=I_(EH)+aX+O(a^2),
X=E U E |_EH.                                     (FQ.3)
```

The canonical moving projection is

```text
P_a
 =A_a U_0(U_0*A_a*A_aU_0)^(-1)U_0*A_a*.          (FQ.4)
```

Differentiating `(FQ.4)` at zero gives

```text
P_0'=R X P+P X* R.                                (FQ.5)
```

The diagonal terms cancel against the derivative of the Gram inverse.  This
is the fixed-carrier analogue of the graph-projection tangent.

Equation `(FQ.5)` is not Proof 403 `(NV.4)`: that formula transports both
`E` and `R` in the ambient carrier.  Proof 343 fixes `E` and transports only
`P` by the compressed block `(FQ.3)`.

## 3. Completed scalar corner

Let

```text
W_E=E W E                                           (FQ.6)
```

be the self-adjoint compact-root detector.  Under Proofs 261 and 398's
trace-legality contract, `(FQ.5)` gives

```text
d/da Tr[W_E(P_a-P)] at a=0
 =2 Re Tr[W_E R X P].                              (FQ.7)
```

Cycle only the completed trace-class product.  Since `P^2=P`, `R^2=R`, and
`PR=0`,

```text
Tr[W_E R X P]
 =Tr[P W_E R X P]
 =Tr[P[W_E,R]R X P].                              (FQ.8)
```

Thus the actual first jet is

```text
q_quot'(0)
 =2 Re Tr[P[W_E,R]R X P].                         (FQ.9)
```

On the quotient carrier, `R=I-P`.  The same scalar is the ordered Toeplitz
semicommutator

```text
P W_E R X P
 =P W_E X P-(P W_E P)(P X P).                    (FQ.9a)
```

Consequently

```text
q_quot'(0)/2
 =Re Tr[T_(W_E X)^P-T_(W_E)^P T_X^P].            (FQ.9b)
```

This is the literal mixed gradient object controlled by Proofs 345--346 on
finite Blaschke model spaces.  It is not Proof 339's rejected path-emission
Hankel corner.  The missing passage is the continuous root-relative Burnol
limit, where only the completed derivative is trace class.

Proof 365's quotient compression corrections remain mandatory for the
finite-`a` moving crossing.  Equation `(FQ.9)` says that, after differentiating
the complete Gram projection and forming the legal scalar, those corrections
recombine into the single fixed commutator corner.  It does not authorize
dropping them at the operator-row level.

## 4. Insert the physical CC20 ledger

Use the actual source identity

```text
R=E Q_f E-K_prol.                                  (FQ.10)
```

Proof 368 gives

```text
[W_E,R]
 =E[W,E]Q_fE+E[W,Q_f]E+E Q_f[W,E]E
  -E[W,K_prol]E.                                  (FQ.11)
```

Substituting `(FQ.11)` inside `(FQ.9)` retains every physical sign before the
trace.  This is the exact four-branch readback of the quotient first jet.

There is a stronger scalar compression.  The Sonin range satisfies

```text
Q_f R=R.                                          (FQ.12)
```

Therefore

```text
P W_E R
 =P Q_f W_E R
  +P(I-Q_f)[W_E,Q_f]R.                            (FQ.13)
```

Indeed the second term equals `P(I-Q_f)W_E R`; adding the `Q_f` part gives
`P W_E R`.  Moreover

```text
(P Q_f)(P Q_f)*=P Q_f P=K_prol.                  (FQ.14)
```

Equations `(FQ.8)` and `(FQ.13)--(FQ.14)` reduce the scalar first jet to

```text
q_quot'(0)/2

 =Re Tr[
    (P Q_f W_E R
      +P(I-Q_f)[W_E,Q_f]R)
    X P].                                         (FQ.15)
```

The two surviving analytic species are

```text
prolate-root leg `P Q_f`;
reflected second-support commutator `[W_E,Q_f]`.   (FQ.16)
```

No outer-boundary term survives as an independent scalar branch.

## 5. Analytic boundary

Proof 336 already controls the corresponding completed fixed-source far lane
after the half-density residue is removed.  Equation `(FQ.15)` identifies the
near fixed-quotient first jet that must remain inside the complete prime/path
telescope.

The remaining theorem is not a branchwise trace-norm bound.  It must show that
the signed sum of the two terms in `(FQ.15)`, with the actual moving prefix
history retained, has polynomial compact-support cost uniformly in finite
`S`.  Proof 278's zero-prolate guard prevents charging the entire response to
`K_prol` alone.

There is also a range-side guard.  If the Euler translation preserves the
second support in the source orientation, then

```text
R X P=R Q_f U P
     =R(U Q_f P+[Q_f,U]P).                        (FQ.17)
```

The first summand contains the common prolate root `Q_f P`; the second is the
genuine causal second-boundary crossing.  Proof 258 gives an exact model in
which these two summands are individually large and cancel.  Therefore
`(FQ.17)` must stay whole: Proof 405 does not by itself construct the common
Julia input left open by Proof 378.

## 6. Reproducible certificate

The companion probe constructs the exact two-support geometry, commuting
ambient transport/detector multipliers, and the compressed quotient path.  It
checks

```text
the Gram derivative `(FQ.5)` by symmetric finite differences;
the scalar corner `(FQ.7)--(FQ.9)`;
the Toeplitz semicommutator `(FQ.9a)`;
the physical four-branch ledger `(FQ.11)`;
the two-branch collapse `(FQ.13)`;
the prolate Gram identity `(FQ.14)`;
a nonzero completed quotient first jet.           (FQ.18)
```

The probe is queued for the next five-substantive-batch WSL2 acceptance run.

## 7. Route judgment

```text
+-----------------------------------------------+---------------------------+
| layer                                         | judgment                  |
+-----------------------------------------------+---------------------------+
| Proof 403 as fixed-quotient owner              | withdrawn                |
| fixed-quotient Gram first jet                  | closed `(FQ.5)`         |
| scalar commutator corner                      | closed `(FQ.9)`         |
| fixed-quotient semicommutator                 | closed `(FQ.9a)`        |
| physical four-branch insertion                | closed `(FQ.11)`        |
| scalar two-branch collapse                    | closed `(FQ.15)`        |
| uniform near two-branch estimate               | open, active producer   |
| Gate 3U / finite-S sign / Burnol / RH          | open / open / open / open|
+-----------------------------------------------+---------------------------+
```

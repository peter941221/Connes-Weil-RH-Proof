# Proof 370: moving-frame detector variance

Date: 2026-07-18

Status: exact condition-number-free readback of Proof 369's corrected
covariance.  Once the quotient frame is Gram normalized, the complete
positive operator is the multiplicative defect, or UCP variance, of the
detector under compression by the moving isometry.

This removes the explicit Gram inverse from the analytic owner.  It does not
bound the trace of that variance uniformly.  Gate 3U, the finite-`S` sign,
Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| corrected covariance from Proof 369           | retained                 |
| normalized moving frame                       | isometry                 |
| explicit Gram inverse in final owner           | eliminated algebraically|
| detector covariance                           | UCP variance             |
| positivity                                    | automatic                |
| uniform trace/HS bound                        | open                     |
| finite certificate                            | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Normalized frame

Let `V:X->H` be an isometry and put

```text
V*V=I,
P=V V*.                                            (DV.1)
```

For the route, `V` is the literal quotient frame

```text
V_j=A_j U_0 H_j^(-1/2),
H_j=U_0* A_j* A_j U_0.                             (DV.2)
```

Thus every occurrence of the compressed Gram inverse in Proof 369 is already
inside an isometry before the detector is applied.

## 3. Detector defect

For a bounded detector `W`, define the rectangular defect

```text
delta_V(W)=(I-P)W V.                                (DV.3)
```

Its covariance is

```text
delta_V(W)* delta_V(W)
 =V* W*(I-P)W V.                                   (DV.4)
```

Define the unital completely positive compression

```text
Phi_V(T)=V* T V.                                    (DV.5)
```

Using `P=VV*`, equation `(DV.4)` becomes

```text
delta_V(W)* delta_V(W)
 =Phi_V(W*W)-Phi_V(W*)Phi_V(W).                    (DV.6)
```

The right side is the multiplicative-domain defect of `Phi_V`.  It is
positive because the left side is `delta*delta`.

## 4. Identification with Proof 369

Proof 368 gives

```text
(I-P_j)Y_jU_0H_j^(-1/2)=(I-P_j)W_E V_j.           (DV.7)
```

Therefore Proof 369 `(NC.10)` is exactly

```text
H_j^(-1/2)U_0*Y_j*(I-P_j)Y_jU_0H_j^(-1/2)

 =Phi_(V_j)(W_E*W_E)
   -Phi_(V_j)(W_E*)Phi_(V_j)(W_E).                 (DV.8)
```

No norm of `H_j^(-1/2)` appears in `(DV.8)`.  The quotient compression
correction and the mixed covariance terms from Proof 369 are not discarded;
they are resummed inside the single isometry `V_j`.

## 5. Self-adjoint detector

For the selected positive detector `W=W*`,

```text
delta_V(W)*delta_V(W)
 =Phi_V(W^2)-Phi_V(W)^2.                            (DV.9)
```

Whenever `delta_V(W)` is Hilbert--Schmidt,

```text
norm(delta_V(W))_2^2
 =Tr_X(Phi_V(W^2)-Phi_V(W)^2).                     (DV.10)
```

Equation `(DV.10)` is the exact detector-row energy required by Proofs
354--359.  It is a relative variance, not either generally infinite trace on
the right taken separately.

## 6. Remaining analytic theorem

The near Gate problem can now be stated without a naked inverse:

```text
sum_(log(p_j)<=L) 1/(p_j-1) *
 Tr(Phi_(V_j)(W^2)-Phi_(V_j)(W)^2)

 <=C(1+L+B_root)^d norm(g)_(H^r)^4.                (DV.11)
```

The trace in `(DV.11)` must be formed through the root-localized defect
`delta_(V_j)(W)`.  Writing it as a difference of two nonsummable traces is
forbidden.

## 7. Reproducible certificate

The companion probe checks

```text
the isometry/projection identities `(DV.1)`;
the defect covariance `(DV.4)`;
the UCP variance identity `(DV.6)`;
positivity of the variance;
invariance under a nonorthonormal source-frame coordinate. (DV.12)
```

Run only in the unified five-batch verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/370_moving_frame_detector_variance_probe.py
```

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| corrected Gram covariance                     | exact variance `(DV.8)`  |
| explicit condition-number factor              | absent                   |
| positivity                                    | closed                   |
| root-local trace estimate                     | next batch              |
| weighted variance bound `(DV.11)`              | open                    |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

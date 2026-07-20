# Proof 408: weighted first-jet same-object certificate

Date: 2026-07-19

Status: finite-dimensional same-object certificate.  The detector derivative
of the weighted relative Gram determinant is exactly the trace of the
Gram-corrected transported projection difference.  Its transport first jet is
the Proof 405 commutator corner.  This is algebraic evidence for the source
owner, not a continuous Gate 3U estimate.

## 1. What is checked

Let `U` be an orthonormal source frame, let `D_g` be the fixed Burnol carrier
multiplier, and put

```text
J       = D_g U,
P_0     = J (J*J)^(-1) J*,
R_0     = I-P_0.
```

For a transport path `D_(tau_t)` with
`tau_t=1+t x`, define `J_t=D_(tau_t)J` and `P_t` as the orthogonal
projection onto `Ran(J_t)`.  For a real detector `w`, the weighted relative
Gram derivative is

```text
q(t)
 = Tr[(J_t*J_t)^(-1) J_t* D_w J_t]
   -Tr[(J*J)^(-1) J* D_w J]
 = Tr[D_w(P_t-P_0)].
```

The probe differentiates `q(t)` at `t=0` and compares it with

```text
q'(0)=2 Re Tr[P_0 [D_w,R_0] R_0 D_x P_0].          (WF.1)
```

The first equality is the weighted version of the Proof 407 relative
determinant owner.  The second is exactly the fixed-carrier Gram first jet
used by Proof 405.

## 2. Relation to the physical two branches

Proof 405 then substitutes its source identity for `[W_E,R]` and obtains

```text
P Q_f W_E R
  +P(I-Q_f)[W_E,Q_f]R,
```

where the first term is the prolate-root leg and the second is the reflected
second-support commutator.  Proof 408 does not estimate these branches
separately.  It verifies the upstream weighted determinant-to-first-jet
identity before that physical substitution.

## 3. Finite certificate result

The companion probe uses a nonconstant positive `D_g`, a nontrivial source
frame, a commuting diagonal transport generator, and a real detector.  It
checks:

```text
weighted determinant detector derivative = projection response;
transport derivative = fixed-quotient first jet;
weighted response differs from raw unweighted response;
the source frame remains full rank under transport.
```

The calculation is finite-dimensional and uses direct linear solves.  It does
not assert trace-class convergence, Burnol's source formula, or Gate 3U.

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/408_weighted_firstjet_same_object_probe.py
```

## 4. Route judgment

```text
weighted Gram response                  exact finite model;
projection readback                     exact finite model;
Proof 405 first-jet match               exact finite model;
actual Burnol continuous identification source-specific and open;
near weighted gradient                  open;
Gate 3U / RH                            open / unproved.
```

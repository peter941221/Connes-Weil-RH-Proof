# Proof 753: Target Hermitian Real Prefix

## Result

Proof 753 gives the real full-kernel scalar its own physical Hermitian
(self-adjoint) finite-prefix owner.  This is the correct prefix object for a
future support-first real estimate; it is not the older Gate prefix.

With

```text
T_S = L_S^* W J,
```

where `L_S` is the complete physical coframe leakage and `J` is the source
inclusion, Lean defines

```text
H_S = (T_S + T_S^*) / 2
    = (L_S^* W J + J^* W L_S) / 2.                     (HP.1)
```

`H_S` is self-adjoint.  For every source vector `x`,

```text
<x, H_S x> = Re <x, T_S x>.                            (HP.2)
```

Since the target diagonal is the complete physical full-kernel scalar
`K_S(x)`, the literal `Fin N` compression satisfies

```text
Tr(P_N H_S P_N) = sum_(i < N) Re K_S(e_i).             (HP.3)
```

The outer compact-root, reflected second-support, and prolate terms remain
inside every `K_S(e_i)` before `Re` is applied.

```text
target response T_S
       |
       v
Hermitian crossing H_S = (T_S + T_S^*) / 2
       |
       v
Tr(P_N H_S P_N) = sum_(i<N) Re K_S(e_i)
       |
       v
abs(Re FullKernelTrace_S) <= C
```

The last arrow is formalized for each fixed finite family: if

```text
forall N, abs(sum_(i<N) Re K_S(e_i)) <= C,
```

then

```text
abs(Re(finiteEulerObliqueShearFullKernelTrace_S)) <= C. (HP.4)
```

The proof uses fixed-family trace legality and `HasSum.tendsto_sum_nat`; it
does not require bounds for arbitrary finite subsets.

## Critical Separation

Proof 735--741 concern an ordered prefix of the full lower-factor Gate
response.  That response also contains the first jet.  The first-jet majorant
is only an ordinary-trace bound, so it cannot be applied prefixwise to turn the
old Gate prefix into `(HP.3)`.

```text
Gate prefix                       target Hermitian prefix
-------------------------------   ---------------------------------
contains first jet                contains only Re target diagonal
does not equal Re K_S prefix      equals sum_(i<N) Re K_S(e_i)
cannot use trace-only M per N     is the real analytic target
```

This distinction prevents an invalid transfer of the first-jet support bound
to finite prefixes.

## Scope

Proof 753 constructs the owner and the exact handoff.  It does not prove the
uniform bound in `(HP.4)`.  In particular, it does not estimate `L_S`, its
inverse-Gram coordinates, the outer branch, the reflected second-support
branch, or the prolate branch separately.

The remaining analytic target is therefore exactly

```text
forall finite S and N,
  abs(sum_(i<N) Re K_S(e_i))
    <= C(1 + support_radius)^d * SobolevNorm(root)^2,
```

with the full physical scalar retained until compact-root support has acted.
Gate 3U, the finite-S sign, the arithmetic same-object identity, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.

The source module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSGatePhysicalTargetHermitianPrefix.lean
```

The audit module is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSGatePhysicalTargetHermitianPrefixAudit.lean
```

## Verification

The Windows truth files were copied to the Ubuntu-24.04 WSL2 ext4 verification
tree before each build.

```text
+------------------------+-----------+
| batch                  | result    |
+------------------------+-----------+
| focused source + audit | 3396/3396 |
| aggregate + audit      | 4021/4021 |
| full repository        | 4102/4102 |
+------------------------+-----------+
```

The audit checks eleven public theorems.  Each reports exactly

```text
[propext, Classical.choice, Quot.sound]
```

Static checks found no `sorry`, `admit`, user axiom, unsafe declaration,
heartbeat override, recursion-limit override, line over 100 characters, or
trailing whitespace in the new source and audit.

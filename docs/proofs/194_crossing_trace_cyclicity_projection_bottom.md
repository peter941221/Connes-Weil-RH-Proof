# Proof 194: Crossing trace cyclicity and the surviving projection

Status: partial. Genuine Hilbert--Schmidt trace cyclicity is proved, but the
named whole-line crossing trace still requires an adjoint-convolution theorem
and a same-object support-range theorem. RH remains unproved.

## What changed

`PositiveTrace.lean:168` proves absolute summability of the two-basis matrix
coefficients for two operators that are square summable on the same source
basis. The proof uses Bessel's inequality and `2ab <= a^2+b^2`; it therefore
justifies exchanging the two infinite sums instead of accepting a free
`cyclicLegal` proposition.

`PositiveTrace.lean:228` then proves the actual cyclic trace identity

```text
Tr_H(A†B) = Tr_G(BA†).
```

The pair-data specialization is at `PositiveTrace.lean:273`. Its import audit
is `GlobalLogCrossingTraceClassAudit.lean:20-35` and reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Application to the selected crossing

The compact crossing already had the exact operator order

```text
E† C† J_b C E.
```

Cycling its two Hilbert--Schmidt factors does not directly produce the earlier
whole-line order. `SelectedCrossingOperatorBridge.lean:1523` names the
orthogonal compression `P_K=E E†`, and the theorem at line 1558 proves that
the compact trace is the source-window trace of

```text
S C P_K C† T_b S†.                                     (194.1)
```

Here `S` restricts to `[0,b]`, `E` zero-extends the kernel interval
`[a-b,c+b]`, and `T_b` is the project's translation convention. The focused
audit is `SelectedCrossingOperatorBridgeAudit.lean:80-83,149-152`.

## Route verdict

The old shortcut was:

```text
trace cyclicity
  -> silently drop E E†
  -> commute J_b with convolution
  -> claim Tr(C† C J_b).
```

Equation (194.1) rejects that shortcut. Cyclicity is now legal, but it exposes
rather than removes the compression. The next admissible bridge must prove on
the same objects:

```text
(C_(g*))† = C_g,
range(C_g T_b S†) subset range(E),
C_g C_(g*) = C_(g*) C_g.
```

The second statement is the exact support theorem that makes `P_K` act as the
identity. The first and third statements identify the adjoint and normality of
the Plancherel multiplier extension. Without all three, the existing compact
finite-prime coefficient cannot be advertised as the named whole-line
`C_h† C_h J_b` trace.

## Verification

In an isolated WSL ext4 verification copy:

```text
lake build ConnesWeilRH.Source.CC20Concrete.PositiveTrace
  2355/2355 passed

lake build ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge
  2978/2978 passed

lake build ConnesWeilRH.Dev.GlobalLogCrossingTraceClassAudit
           ConnesWeilRH.Dev.SelectedCrossingOperatorBridgeAudit
  2981/2981 passed
```

Focused axioms: `propext`, `Classical.choice`, `Quot.sound` only.

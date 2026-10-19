# Absolute-tail reduction for the selected joint symbol (record 3058)

Date: 2026-10-19.

Status: same-owner analytic reduction. It is not a sign estimate, Lean theorem,
or RH result. Whether its explicit tail allowance is useful at the constructed
owner remains to be priced.

## Same-owner setup

Use the joint-symbol identity of record 1738 for one selected geometry:

```text
qw(g) = (1/(2*pi))*integral_R m_S(t)*|G(t)|^2 dt,
G(t) = laplaceAt g (i*t).
```

Here `S` is that geometry's actual visible-prime set. Put

```text
C_S = 2*sum_(p in S) log(p)*p^(-1/2)/(1-p^(-1/2)),
K = log(8*pi) + EulerGamma + pi/2,
T* = max(T, 1, 2*|Im rho|),
```

where `T` and `epsilon` are the same geometry's fourth-order tail parameters.
The tail estimate from record 3054 gives

```text
|G(t)| <= 4*epsilon/|t|^2,  |t| >= T*.
```

## Bound the signed tail as a whole

Record 1738 gives `m_S(t)=A(t)-prime_S(t)`, with `A(t)>=-K`. Record 3057
proves `A(t)<=8+log(1+t)` for `t>=1`, and `|prime_S(t)|<=C_S`. Thus for
`t>=T*>=1`,

```text
|m_S(t)| <= K + 8 + C_S + log(1+t)
           <= K + 8 + C_S + log(2) + log(t).
```

Define the full signed tail contribution

```text
Q_tail(T*) = (1/(2*pi))*integral_(|t|>=T*) m_S(t)*|G(t)|^2 dt.
```

Using both signs of `t` and the fourth-order tail,

```text
|Q_tail(T*)|
  <= (16*epsilon^2)/(3*pi*T*^3)
       * (K + 8 + C_S + log(2) + log(T*) + 1/3).
```

The constant follows directly from
`integral_T^infinity t^(-4)dt = 1/(3*T^3)` and
`integral_T^infinity log(t)*t^(-4)dt = (log(T)/3+1/9)/T^3`.

Consequently the exact whole-line target has the sufficient finite-window
form

```text
Q_core(T*) >= E_tail(T*),
Q_core(T*) = (1/(2*pi))*integral_(|t|<=T*) m_S(t)*|G(t)|^2 dt,
```

where `E_tail(T*)` is the displayed upper bound. The negative contribution
between `T*` and the conservative sign threshold `T_S` is absorbed into this
absolute error instead of being included in a window extending to
`max(T*,T_S)`.

## Scope and gate

This reorganization avoids needing to prove that `m_S` is nonnegative on the
tail. It does not produce positive credit: `Q_core` is still signed and must
be bounded below for the same geometry. It also does not establish that
`E_tail` is small. In particular, `C_S` depends on the full visible-prime
owner and may make the allowance too large. Before using this reduction as a
route improvement, price `E_tail(T*)` against an independently established
same-owner core margin; no such margin is currently recorded.

Evidence:

- `docs/proofs/1738_selected_orbit_joint_symbol_and_tail_sampling.md` gives
  the exact same-owner symbol and the bound by `C_S`.
- `docs/proofs/3054_fourth_order_tail_to_derivative_energy.md` gives the
  pointwise transform tail used here.
- `docs/proofs/3057_joint_symbol_far_tail_credit_upper.md` gives the
  archimedean-symbol bound and the conservative threshold `T_S`.

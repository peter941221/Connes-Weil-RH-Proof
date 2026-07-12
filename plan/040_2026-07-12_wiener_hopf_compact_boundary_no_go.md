# 040 Wiener--Hopf Compact Boundary No-Go

Date: 2026-07-12

Status: compact half-line correction route rejected by a translated Weyl
sequence.

## Claim

Let `V_S(D)` be the translation multiplier carrying the selected finite-prime
Weil modes, and suppose a proposed positive half-line owner has the form

```text
P(c I+V_S(D))P + K,
```

where `K` is compact or a boundary-local operator compact after the common test
smoothing.  Then positivity still requires

```text
c >= -inf_t V_S(t).
```

## Proof Mechanism

Choose a long wave packet with central frequency `t_0` and translate its
physical support arbitrarily far into the positive half-line.  On this Weyl
sequence:

```text
P acts as I;
the multiplier expectation tends V_S(t_0);
every compact/boundary-local K expectation tends 0.
```

Positivity therefore gives `c+V_S(t_0)>=0`.  Taking the infimum recovers the
sharp compensation from Plan 037.  A compact Schur, Hankel, or Toeplitz
boundary term cannot alter this essential lower symbol.

For the prime symbol, rational independence of the `log p` phases gives

```text
-inf_t V_S(t)
  = sum_(p in S_f) 2 log(p)/(sqrt(p)+1),
```

which grows without bound with `S`.

## Verdict

```text
direct positive multiplier: rejected (037)
termwise positive differences: rejected (039)
compact Wiener--Hopf boundary repair: rejected
remaining reopen shape: noncompact pre-read-off cancellation only
```

Such a noncompact cancellation must remove every unwanted principal channel
before the compactness claim; it cannot be called a remainder. See proof 118.


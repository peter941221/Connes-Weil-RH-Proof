# 959 - Wall-A 1.4 prime-pairing spec and whether a model reframe (A) is worth it

Date: 2026-08-10.  Status: decision/spec (evidence = numeric probe docs/958 + this); NOT a proof.
RH NOT claimed.  See docs/955 (mandatory), 957 (arch nonzero), 958 (balance probe).

## The question

Wall-A 1.4 target (SCB) reduces to

    2*arch(f*f) + (globalSum - restrictedSum) = 0

with arch(Eq.3.7) = (log(4pi)+euler)*(f*f)(0) + Integral_{y>0}[ e^(y/2)(f*f(y)+f*f(-y)) - 2(f*f)(0) ]/(e^y - e^-y) dy.

Two finite-prime conventions exist in the source (PrimePowerArithmetic vs SelectedWeilSquare):

| conv | atom | behaviour on the route proxy bump |
|---|---|---|
| valueAt | (1/sqrt n)*(valueAt(f*f,n)+valueAt(f*f,1/n)), valueAt=point eval | conv(n)=0 for integer n>=2, conv(1/n)~|f|^2; partials 0.55/1.9/4.8/9.1/16/26 -> DIVERGES |
| Connes-log (Laplace/Mellin) | (1/sqrt n)*( (f*f)(log n)+(f*f)(-log n) ) | only n=2 survives, sum = +0.000043 |

## Decisive measurement

On the Connes-log (mathematically the correct adelic/Mellin choice) the residual is

    2*arch(fwf) + sum_{prime powers} term  =  +0.5884344...

So `2*arch + (P-R) = 0` needs the model to also carry a LEN +0.588 term that NO pairing
supplies here.  In the full Weil/assumption formula that +0.588 IS the contribution
carried by the non-trivial zeros / the implied zero-sum datum.  The SC `weilValue =
poleTerm - arch - prime` structure has NO zero-sum term; it asserts that the prime and
arch sides alone balance to zero.

## Conclusion (which path A gives)

1) Pairing-swap (valueAt <-> log) does NOT fix the identity: the log-convention
   already balances only up to +0.588, the valueAt-convention is inconsistent
   (diverges).  The "wrong convention" is not the root cause.
2) Root cause = the model omits a term of size ~ +0.588 (the nontrivial-zero /
   explicit-formula datum).  As-stated, `2*arch+(P-R)=0` is FALSE on every
   non-degenerate compactly-supported smooth test (arch>0 -positive 3.11|f|^2).
3) Therefore a pure model/prime re-frame (path A as "re-derive the finite side")
   does NOT close Wall-A 1.4; it would still assert a false equality unless it
   reintroduces the zero-sum / explicit-formula term.  That term is exactly the
   real Weil bridge (the long open piece).

## Consequence / recommendation

- A "convention reframe" is NOT sufficient; investing heat build budget in a
  re-paired-LHS helper (docs/958 path "A") is not justified.
- The genuine step is OFF-the arch-only identity: either
   (a) formalise the missing +0.588-term as `sum_rho (fStf)(rho)` and prove it
       balances (that is the full Weil explicit formula) - big, real analysis; or
   (b) switch lanes to the independent (RH-equivalent) C1 criterion (docs/955).

Scope note: numbers are a proxy-port bump (route commonBump is Classical.choose), so
this is evidence, not a proof.  But `(log(4pi)+euler)>0` and (f*f)(0)=|f|^2>0 make
the positivity of the leading arch term rigorous for any nonzero compact test, so the
"model must carry an extra term" conclusion is robust.
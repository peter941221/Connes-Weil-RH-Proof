# 1002 - V_arch is nonempty: the scattering-factorization route (sub-target C core)

Status: analytic verdict POSITIVE (V_arch is nontrivial), but the concrete
nonzero witness construction remains OPEN (new analysis). This document does
NOT lend a Lean closure; it is the correct first-principles reduction and the
existence route. RH not claimed. No sorry / axiom.

## 0. TL;DR

C is not dead and not an eigen-route. Unwinding the two half-line annihilations
in the Fourier / Paley-Wiener dual gives a single condition, independent of the
scale lambda:

```
  want nonzero phi in H- (lower Hardy):       u radial
  and   m(xi) * phi(-xi) in H-           :   (HT u) radial
  m(x) = Gamma_R(1/2 - i 2 pi x) / conj(Gamma_R(1/2 + i 2 pi x)),  |m(x)| = 1.
```

The two exp(+/-2 pi i xi log lambda) factors cancel exactly, so membership is
identical at every scale: the open leaf "exists nonzero u in V_arch(lambda)"
is scale-independent.

## 1. The reduction (lambda cancels)

Let u in Radial(lambda) (support on t >= log lambda). Put w(t) = u(t + log lambda),
so w in Radial(0). The elementary Fourier shift gives
   F(u)(xi) = exp(2 pi i xi log lambda) * F(w)(xi),   with F(w) in H- (lower).
The HT image readback (in the repo) is  F(HT u) = m(xi) * (F u)(-xi). Then
   HT u in Radial(lambda)
     <=>  exp(2 pi i xi log lambda) * F(HT u)(xi) in H-
     <=>  m(xi) * (F w)(-xi) in H-.
Set phi = F w in H-. The whole claim is the pair

   phi in H-  and  m(xi) * phi(-xi) in H-.                     (C*)

No lambda left. This is the exact 'interior' contract at every scale.

## 2. Existence route: simplify by an inner/outer (Wiener-Hopf) split

Let psi(xi) = phi(-xi). Since phi in H-, psi is in H+ (upper Hardy). Condition
(C*) is exactly

    psi in H+,   and   m * psi in H-.                        (C*')

Now suppose we can factor the unimodular symbol m as a ratio

    m = Q / P,   with P in H+ (upper), and Q in H- (lower),  |P| = |Q| = 1.

Then taking psi = P gives: psi in H+ (true), and m * psi = (Q/P) * P = Q in H-.
So both halves of (C*) hold.  Back-translating psi=P gives the nonzero
Fourier-side witness, hence a nonzero u = F^{-1}(exp(-...log lambda)*...)...).
The existence of such a P / Q factorization of m is exactly the
inner / outer (Beurling-functional) split of the archimedean scattering phase,
which is classical and expected to hold for this Gamma_R ratio.

## 3. What remains (the actual new analysis)

Matter: a controller needs the explicit, closed form outer factor of the
specific Gamma_R scattering phase, then the L2 placement of the built phi. This
is (a) not in mathlib v4.30.0 and (b) a genuine multi-session paper-level
procedure; the typed gate `vArch_mem_iff_support_ae` awaits a concrete phi.

## 4. Not dead, no counterexample

- The exact +-1 eigenvector path (Gamma multipliers level-set thin) is void,
  but that only rules out that sub-family (docs/1000).
- The factor route is an existence proof: once the Gamma_R scattering is
  factorable (inner/outer holds), V_arch is rich (not just nonzero).
- No documented counterexample; numerics are a separate check, not a proof.

## 5. Next closed step (proposal)

1. Write the explicit inner / outer (or Gamma-R) factorization of
   ccm24ArchimedeanScatteringPhase (the Gamma-R ratio).
2. Lift the built phi to a non-zero L2 witness through the existing typed gate
   `vArch_mem_iff_support_ae`.
3. Prove the window mass (sub-target D) and lift twoOuterNonzeroObligation
   (sub-target E), then flip AGENTS 998/999.
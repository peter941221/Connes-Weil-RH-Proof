# 090 Schwartz Ambient Owner Probe Pass

Date: 2026-07-12

## Lean evidence

`ConnesWeilRH/Dev/SchwartzAmbientOwnerProbe.lean` defines:

```text
AmbientTest := SchwartzMap ℝ ℂ
ambientConvolution
ambientInvolution
ambientConvolution_fourier
```

The convolution is Mathlib's `SchwartzMap.convolution` with complex
multiplication. The involution composes with the real negation continuous
linear equivalence and then with complex conjugation. The probe proves

```text
fourier (ambientConvolution f g)
  = fun x => fourier f x * fourier g x.
```

The file compiles in the WSL ext4 verification mirror after building the
required Mathlib Fourier-convolution module.

## Verdict

```text
ambient Schwartz carrier type: pass
genuine convolution type: pass
reflection/conjugation involution type: pass
Fourier multiplication theorem: pass
compact witness encoding: structurally available
CC20/CCM25 same-square transport: still open
```

This does not create a final route owner and proves no RH-facing statement. It
removes the API/type objection to the escape in proof 089.


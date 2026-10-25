# 3086 - Route A Laplace/Fourier normalization bridge

The exact Fourier convention was already proved in the prime-power readback
leaf. Record 3086 transports it to the actual orbit owner:
`routeAOrbitTransform geometry xi` equals the selected-source Laplace value,
then equals `fourierLaplace g.test xi`, and finally equals the Mathlib Fourier
transform at `-(xi/(2*pi))`. The bridge is axiom-clean; analyticity and the
negative symbol neighbourhood remain separate obligations.

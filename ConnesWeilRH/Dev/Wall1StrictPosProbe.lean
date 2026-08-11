/-!
WIP NOTE (no sorry, no claim, does not build as a route module).

The strict-positivity seed for fullWeilPositivity on the healthy CompactLog carrier
reduces to ONE clean operator statement:

  theorem conv_nonzero (h : SchwartzMap Real Complex) (hne : h != 0) :
      cc20GlobalLogConvolution h != 0

Proof route (Fourier-multiplier model, ref GlobalLogConvolution.lean):
  cc20GlobalLogConvolution h = FT.symm o (multiply (FT h)) o FT,
  with FT = Lp.fourierTransformLi (a real Hilbert isometry -> injective).
  So it suffices to show the multiplier (FT h) is a nonzero operator on L2,
  i.e. exists v, (FT h) dot v != 0.  Take v = (FT h) itself: then
  (FT h) dot (FT h) = (FT h)^2 and (FT h) != 0 in Linfty because the Fourier
  transform is injective and h != 0.  This yields the nonzero seed; combined with
  cc20GlobalLogConvolution_toLp it also gives nonzero image on the dense
  Schwartz core.

Follow with fullBoundaryRootFactor_eq_globalConvolution + strict window to get
exists u, norm (F ncTest a c u) > 0 and hence a populated diagonal.  RH not claimed.
-/

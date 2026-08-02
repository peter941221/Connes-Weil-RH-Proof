# Proof 725: Physical Cancellation Endpoint Split

Proof 724 rewrote the active cancellation target as

~~~text
sourceOuterCoframeLeakage
  + (sourceActualBandForwardCoframe + sourceBandMetricCoframeLeakage)
  = 0.
~~~

Proof 725 removes the remaining artificial split between the raw forward
coframe and the source-band metric coframe.  Lean proves

~~~text
sourceBandProjection o sourceActualBandForwardEndpointCoframe
  = sourceActualBandForwardCoframe + sourceBandMetricCoframeLeakage.
~~~

It also proves that the raw forward coframe already lands in the radial band:

~~~text
(I - radialSupportProjection) o sourceActualBandForwardCoframe = 0.
~~~

Therefore the active cancellation target is the endpoint-only equation

~~~text
sourceOuterCoframeLeakage
  + sourceBandProjection o sourceActualBandForwardEndpointCoframe
  = 0.
~~~

Equivalently, this is exactly the complete off-Sonin endpoint leakage:

~~~text
sourceOuterCoframeLeakage
  + sourceBandProjection o sourceActualBandForwardEndpointCoframe
  = sourceActualBandCombinedCoframeLeakage.
~~~

The structural picture is:

~~~text
        sourceActualBandForwardEndpointCoframe
                       |
          +------------+-------------+
          |                          |
       I - E                        B = E - R
          |                          |
 outer metric leakage        forward + band metric
          |                          |
          +------------+-------------+
                       |
         complete off-Sonin endpoint leakage
~~~

This is not a cancellation theorem.  It does not prove either endpoint channel
vanishes, does not prove Gate 3U, does not prove the finite-S sign, does not
prove Burnol's identity, and does not prove _root_.RiemannHypothesis.

The point is stricter: the next source theorem should attack the two endpoint
channels of one completed coframe, not the older separated
forward-plus-bandMetric bookkeeping.

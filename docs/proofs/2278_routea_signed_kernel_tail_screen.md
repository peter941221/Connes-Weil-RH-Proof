# 2278 - Signed-kernel oscillatory tail screen

Date: 2026-09-30

Result: the corrected owner requires 41136 visible prime powers when the physical convolution support is used. A finite FFT screen over 40 <= xi <= 500 reads a tiny signed tail, but refinement is unstable: signed movement is 6.315x and absolute movement is 5.191x. The instrument is therefore marked FFT-TAIL-UNTRUSTED and cannot close hgap.

## What was tested

The script forms the corrected width-a^2 physical profiles, applies the centered annihilator polynomial, constructs the support-derived prime-power kernel, and integrates the signed product directly on the FFT frequency grid. This preserves the signs that the elementary absolute envelope discards.

The corrected convolution support is 13.107200000000006, producing 41136 prime-power terms. The earlier 52-term kernel was tied to the legacy width-a support and cannot be transferred to this owner.

The coarse screen reads signed integral 1.2613203193834267e-24 and absolute integral 2.752383215865085e-24. The fine screen reads signed integral 1.724260726689975e-25 and absolute integral 4.44554133047801e-25. These values are diagnostic only.

## Decision

The signed-kernel idea remains mathematically relevant, but this FFT implementation is rejected as a certificate path. The large refinement movement shows that roundoff, frequency sampling, or transform aliasing dominates the displayed scale. More FFT nodes would not be accepted without a trust-horizon experiment that changes the rule and proves an independent enclosure.

The next tail implementation must use direct oscillatory quadrature or a certified panel rule with an independently measured trust horizon. It must also bind the 41136-term support-derived kernel to the selected owner. hgap remains explicit.

No Lean file or manifest-bound producer source changed. Five focused controls pass. No producer GO or RH claim is made.

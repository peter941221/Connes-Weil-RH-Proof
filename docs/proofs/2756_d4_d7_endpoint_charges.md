# 2756 - D4/D7 endpoint integral charges

Status: Lean-verified endpoint integration consumer.

The theorem `d4d7_endpoint_integral_charges2756` combines the existing endpoint majorant with the exact interval-integral theorem at orders 4 and 7. It proves both

```text
4 * integral_[0,1/4096] ||(d^4/dx^4) smoothTransition|| <= seedEndpointCharge2733 4
4 * integral_[0,1/4096] ||(d^7/dx^7) smoothTransition|| <= seedEndpointCharge2733 7
```

The companion theorem proves both charges are below 10^-1000. Verification: Linux-native audit build 3656/3656, zero errors, standard axiom trio only.

This is an endpoint charge, not the finite interior-cell replay or full D4/D7 numerical integral bound. Producer GO, SourceRH and RH remain open.

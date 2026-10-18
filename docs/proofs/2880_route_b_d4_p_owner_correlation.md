# 2880 Route B D4 P owner correlation

A direct rectangular enclosure for `P(t,z)` is too loose: the independent
`t` and `z` box contains both signs on the left outer region, while sampling
the owner curve `z = tanh(2t/(1-t^2))/t` keeps one sign. The formal enclosure
must preserve this correlation, for example by substituting a certified Taylor
model for `z(t)` or by using a monotone rational envelope.

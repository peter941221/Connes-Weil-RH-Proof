# CC20 Same-Object L2 Owner

Date: 2026-07-12

`RegularKernelL2Data` binds the concrete kernel, its compact real-coordinate
domain, the kernel/domain equalities, and the actual square-integrability proof
in one object. The constructor is `cc20RegularKernelL2Data`.

`cc20RegularKernelL2Data_hasFiniteSquareIntegral` derives finite square mass
from the proved `IntegrableOn` field. No integral operator, Hilbert--Schmidt
continuous linear map, or CC20 action identity is stored; those remain genuine
next obligations.

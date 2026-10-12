"""Exercise directed MPFR-to-binary64 conversion on an exact dyadic input."""

from __future__ import annotations

import ctypes as C
import json
import struct
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "results/2674_binary64_endpoint_control.json"
PRECISION = 256
RNDD = 3
RNDU = 2


class MpfrStruct(C.Structure):
    _fields_ = [
        ("prec", C.c_long),
        ("sign", C.c_int),
        ("exp", C.c_long),
        ("digits", C.POINTER(C.c_ulong)),
    ]


class MpfrValue:
    def __init__(self, library):
        self._library = library
        self.value = MpfrStruct()
        library.mpfr_init2(C.byref(self.value), PRECISION)

    def clear(self):
        self._library.mpfr_clear(C.byref(self.value))


def binary64_bits(value: float) -> str:
    return f"0x{struct.unpack('>Q', struct.pack('>d', value))[0]:016x}"


def main() -> None:
    library = C.CDLL("libmpfr.so.6")
    pointer = C.POINTER(MpfrStruct)
    library.mpfr_init2.argtypes = [pointer, C.c_long]
    library.mpfr_clear.argtypes = [pointer]
    library.mpfr_set_d.argtypes = [pointer, C.c_double, C.c_int]
    library.mpfr_add.argtypes = [pointer, pointer, pointer, C.c_int]
    library.mpfr_get_d.argtypes = [pointer, C.c_int]
    library.mpfr_get_d.restype = C.c_double

    one = MpfrValue(library)
    epsilon = MpfrValue(library)
    exact = MpfrValue(library)
    try:
        library.mpfr_set_d(C.byref(one.value), 1.0, RNDD)
        library.mpfr_set_d(C.byref(epsilon.value), 2.0 ** -200, RNDD)
        library.mpfr_add(C.byref(exact.value), C.byref(one.value),
                         C.byref(epsilon.value), RNDD)
        exact_fraction = Fraction(1) + Fraction(1, 2**200)

        lower = library.mpfr_get_d(C.byref(exact.value), RNDD)
        upper = library.mpfr_get_d(C.byref(exact.value), RNDU)
        lower_fraction = Fraction.from_float(lower)
        upper_fraction = Fraction.from_float(upper)
        if not lower_fraction <= exact_fraction <= upper_fraction:
            raise AssertionError("directed conversions failed exact containment")
        if binary64_bits(lower) != "0x3ff0000000000000":
            raise AssertionError("unexpected RNDD endpoint")
        if binary64_bits(upper) != "0x3ff0000000000001":
            raise AssertionError("unexpected RNDU endpoint")

        result = {
            "record": 2674,
            "status": "MPFR-DIRECTED-BINARY64-CONTROL-PASS",
            "precision_bits": PRECISION,
            "exact_value": str(exact_fraction),
            "round_down_bits": binary64_bits(lower),
            "round_down_exact": str(lower_fraction),
            "round_up_bits": binary64_bits(upper),
            "round_up_exact": str(upper_fraction),
            "exact_containment": True,
            "scope": "one exact dyadic MPFR value and its two binary64 directed conversions",
            "nonclaims": [
                "does not verify MPFR internals or its operation implementation",
                "does not certify the 2242 interval evaluator or any 2670 cell",
                "does not close owner transfer, the infinite tail, Producer GO, or RH",
            ],
        }
        OUTPUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(result, indent=2))
    finally:
        one.clear()
        epsilon.clear()
        exact.clear()


if __name__ == "__main__":
    main()

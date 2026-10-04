"""Exact check of the 2570 assembly inequality from the emitted literals."""
from fractions import Fraction as Q
import re

DEV = "ConnesWeilRH/Dev/"


def load(module):
    return open(DEV + module + ".lean").read()


def clean(body):
    body = body.replace(": ℝ", "").replace("\n", " ")
    return body.replace("* 10^", "*Q(10)**").replace("/ 10^", "/Q(10)**")


def scalar(text, name):
    m = re.search(r"noncomputable def " + name + r" : ℝ :=\s*(.+?)\n\n", text, re.S)
    return eval(clean(m[1]))


def chunked(text, name):
    m = re.search(r"noncomputable def " + name + r" : ℝ :=\n(.+?)\n\n", text, re.S)
    return eval(clean(m[1]))


asm = load("C1RouteACorrectionSecondCell2700MinusCorr2570")
mid_text = load("C1RouteACorrMidpointBounds2700Minus2570")
jet_text = load("C1RouteACorrFirstJetMidpointMinus2570")
n0l_text = load("C1RouteACorrSharedN02700Minus2570")
n0r_text = load("C1RouteACorrSharedN02701Minus2570")

bound = scalar(asm, "corrSecondCell2700MinusUpper2570")
mid = scalar(mid_text, "corrC02700MinusSignedMidpointUpper2570")
l1 = chunked(asm, "corrThirdL1Upper2570")
jet = scalar(jet_text, "fjcmUpper2570")
n0l = scalar(n0l_text, "corrSharedN02700MinusUpper2570")
n0r = scalar(n0r_text, "corrSharedN02701MinusUpper2570")
print("bound", bound, float(bound))
print("mid  ", mid, float(mid))
print("l1   ", float(l1))
print("jet  ", jet, float(jet))
print("n0l  ", n0l, float(n0l))
print("n0r  ", n0r, float(n0r))

R = Q(65536001, 10 ** 7)
step = 2 * R / 10240
half = step / 2
sigma = Q(-1, 2)
C = mid + l1 * half
total = (step * C
         + 2 * abs(sigma) * step * (jet + C * half)
         + sigma ** 2 * (half * (n0l + n0r) + C * step ** 3 / 12))
print("assembled total", total, float(total))
print("bound - total  =", float(bound - total))
print("VERDICT", "HOLDS" if bound >= total else "VIOLATED")

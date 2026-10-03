"""2525: directed node-box evaluation; all owner and endpoint gates stay explicit."""
import hashlib, importlib.util, json, math
from fractions import Fraction
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
OUT = ROOT / "results/2525_owner_panel_node_mpfr.json"
spec = importlib.util.spec_from_file_location("routea_mpfr_2286", ROOT / "scripts/routea_mpfr_owner_atom_preflight_2286.py")
mpfr = importlib.util.module_from_spec(spec); spec.loader.exec_module(mpfr)

def frac(s):
    a = s.split("/")
    return Fraction(int(a[0]), int(a[1])) if len(a) == 2 else Fraction(int(a[0]))

def iv_frac(x):
    v = float(x); return (math.nextafter(v, -math.inf), math.nextafter(v, math.inf))

def iv_float(x):
    v = float(x); return (math.nextafter(v, -math.inf), math.nextafter(v, math.inf))

def add(x,y): return mpfr.add(x,y)
def sub(x,y):
    return (mpfr.sub((x[0],x[0]),(y[1],y[1]))[0], mpfr.sub((x[1],x[1]),(y[0],y[0]))[1])
def mul(x,y): return mpfr.mul(x,y)
def div(x,y): return mpfr.div(x,y)
def neg(x): return (-x[1], -x[0])
def add_iv(a,b): return add(a,b)
def sub_iv(a,b): return sub(a,b)
def add_rect(a,b): return (add_iv(a[0],b[0]), add_iv(a[1],b[1]))
def rect_mul(a,b):
    ar, ai = a; br, bi = b
    return (sub_iv(mul(ar,br),mul(ai,bi)), add_iv(mul(ar,bi),mul(ai,br)))
def rect_norm_upper(z):
    return math.nextafter(max(abs(z[0][0]),abs(z[0][1])) + max(abs(z[1][0]),abs(z[1][1])), math.inf)

def main():
    repair = json.loads(REPAIR.read_text())
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    families = []
    for row, pair in zip(repair["coefficient_rows"], capture["families_hex"]):
        re = (iv_frac(frac(row["ideal_base_coefficient"]["real"]["lower_exact"]))[0], iv_frac(frac(row["ideal_base_coefficient"]["real"]["upper_exact"]))[1])
        im = (iv_frac(frac(row["ideal_base_coefficient"]["imag"]["lower_exact"]))[0], iv_frac(frac(row["ideal_base_coefficient"]["imag"]["upper_exact"]))[1])
        width = float.fromhex(pair[0]); mod = float.fromhex(pair[1])
        radius = Fraction.from_float(width)**2
        families.append({"coef": (re, im), "radius_exact": radius, "radius": iv_frac(radius), "mod": iv_float(mod)})
    radius = frac("65536001/10000000")
    cells = 640
    step = radius / 320
    rows = {"-0.5": [], "0.5": []}
    for index in range(cells + 1):
        x = -radius + index * step
        x0 = x - step / 2; x1 = x + step / 2
        total = ((0.0,0.0),(0.0,0.0))
        for f in families:
            r = f["radius_exact"]
            if x0 >= 0:
                if x0 < r:
                    t = div(iv_frac(x0), f["radius"]); q = sub(iv_frac(1),mul(t,t)); bump = mpfr.unary("mpfr_exp",div(iv_frac(-30),q))[1]
                else: bump = 0.0
            elif x1 <= 0:
                if -r < x1:
                    t = div(iv_frac(x1), f["radius"]); q = sub(iv_frac(1),mul(t,t)); bump = mpfr.unary("mpfr_exp",div(iv_frac(-30),q))[1]
                else: bump = 0.0
            else:
                bump = mpfr.unary("mpfr_exp",iv_frac(-30))[1]
            mid = mul(f["mod"], iv_frac((x0+x1)/2))
            rho = math.nextafter(abs(float(f["mod"][1])) * float(step) / 2, math.inf)
            cosmid = mpfr.unary("mpfr_cos", mid); sinmid = mpfr.unary("mpfr_sin", mid)
            phase = ((cosmid[0]-rho, cosmid[1]+rho),(sinmid[0]-rho,sinmid[1]+rho))
            bump_rect = ((0.0, bump),(0.0,0.0))
            total = add_rect(total, rect_mul(rect_mul(f["coef"], bump_rect), phase))
        norm = rect_norm_upper(total)
        for sigma in ("-0.5","0.5"):
            weight = mpfr.unary("mpfr_exp", mul(iv_frac(Fraction(sigma)), iv_frac(x)))
            weighted = mpfr.mul((norm,norm), weight)[1]
            rows[sigma].append({"index": index, "x": str(x), "norm_upper": repr(norm), "weighted_upper": repr(weighted)})
    composite = {}
    for sigma in rows:
        total = (0.0,0.0)
        for i in range(cells):
            pair = add((0.5*float(rows[sigma][i]["weighted_upper"]),0.5*float(rows[sigma][i]["weighted_upper"])), (0.5*float(rows[sigma][i+1]["weighted_upper"]),0.5*float(rows[sigma][i+1]["weighted_upper"])))
            total = add(total, pair)
        composite[sigma] = mpfr.mul(iv_frac(step), total)[1]
    payload = {"record":2525,"status":"MPFR_DIRECTED_640_NODE_SUM_NOT_LEAN_CERTIFICATE","backend":{"library":"libmpfr.so.6","precision_bits":mpfr.PREC,"rounding":"RNDD/RNDU"},"cells":cells,"node_count":cells+1,"radius":str(radius),"step":str(step),"composite_node_upper":composite,"rows":rows,"repair_sha256":hashlib.sha256(REPAIR.read_bytes()).hexdigest(),"capture_sha256":hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),"nonclaims":["no Lean literal import","no strip certificate","no producer GO","no RH"]}
    OUT.write_text(json.dumps(payload, indent=2)+"\n")
    print(json.dumps({"record":2525,"status":payload["status"],"composite_node_upper":composite,"artifact":str(OUT)}))
if __name__ == "__main__": main()

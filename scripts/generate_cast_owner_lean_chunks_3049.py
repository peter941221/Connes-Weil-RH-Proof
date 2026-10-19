#!/usr/bin/env python3
import json
from fractions import Fraction
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def q(s):
    a=Fraction(s); return f"({a.numerator} : ℚ) / {a.denominator}"
def main():
    d=json.loads((ROOT/'results/3048_cast_owner_chunk_sums.json').read_text())
    lines=['import ConnesWeilRH.Dev.C1RouteAItem5Arithmetic','', 'namespace ConnesWeilRH.Dev','', '/-- Record 3049: exact chunk arithmetic projection for cast-owner 3047. -/']
    names=[]
    for sig in ('-1/2','1/2'):
        ident='minus' if sig.startswith('-') else 'plus'; vals=[c['sum_exact'] for c in d['chunks'] if c['sigma']==sig]
        name=f'record3049_{ident}_chunks'; names.append(name)
        lines += [f'def {name} : List ℚ :=', '  [' + ',\n   '.join(q(v) for v in vals) + ']', '']
        target=q(d['endpoint_chunk_sums'][sig])
        lines += [f'theorem {name}_sum : ({name}).sum = {target} := by', f'  norm_num [{name}]', '']
    total=Fraction(d['endpoint_chunk_sums']['-1/2'])+Fraction(d['endpoint_chunk_sums']['1/2'])
    lines += ['theorem record3049_both_sums :', f'    ({names[0]}).sum + ({names[1]}).sum = {q(str(total))} := by', f'  rw [{names[0]}_sum, {names[1]}_sum]', '  norm_num', '', 'end ConnesWeilRH.Dev', '']
    out=ROOT/'ConnesWeilRH/Dev/C1RouteARepairedOwnerChunkArithmetic3049.lean'; out.write_text('\n'.join(lines),encoding='utf-8'); print(out)
if __name__=='__main__': main()

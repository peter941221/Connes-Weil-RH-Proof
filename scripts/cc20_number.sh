#!/bin/bash
# Map target CC20 tex lines to rendered equation numbers (count of numbered
# equation environments up to each line).
F=/home/peter/cc20/x/weil-compo.tex
O=/mnt/c/Projects/Connes-Weil-RH-Proof/tmp_cc20_number.txt
awk '
/begin\{equation\}$/ { n++ }
/begin\{equation\}\\label/ { n++; lab[n]=$0 }
/begin\{equation\}[ ]*$/ { }
{ if (NR==100 || NR==108 || NR==118) {} }
END { }
' "$F" >/dev/null
# robust: single awk pass over unstarred begin{equation} occurrences
awk 'index($0,"\\begin{equation}")==0 && index($0,"\\begin{equation}") { } { }' "$F" >/dev/null
python3 - "$F" > "$O" <<'PY'
import re, sys
f = sys.argv[1]
lines = open(f, encoding="latin1").read().split("\n")
n = 0
targets = {}
starts = []
for i, ln in enumerate(lines, 1):
    # count unstarred \begin{equation} (not \begin{equation*})
    for m in re.finditer(r"\\begin\{equation\}", ln):
        after = ln[m.end():m.end()+1]
        if after != "*":
            n += 1
            lab = re.search(r"\\label\{([^}]*)\}", ln)
            starts.append((n, i, lab.group(1) if lab else ""))
print("total numbered equations:", n)
print("=== numbered equations with tex line in 1400..1830 (num, line, label) ===")
for t in starts:
    if 1400 <= t[1] <= 1830:
        print(*t, sep="\t")
PY
wc -c "$O"

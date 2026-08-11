set -e
cd /home/peter/verify/cwr-lanb-archlift
cat > /tmp/axsn.lean <<'EOF'
import ConnesWeilRH.Dev.ScabNormalForm
#print axioms ConnesWeilRH.Source.CCM25Concrete.ScabNormalForm.scab_iff_pole_arch_target
EOF
flock -w 1800 /tmp/connes-weil-rh-lake.lock lake env lean /tmp/axsn.lean 2>&1 | tail -8

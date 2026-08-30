#!/bin/bash
# Fetch and unpack arXiv:2006.13771 (CC20) source under WSL2.
# localhost proxies are not mirrored into WSL NAT mode (WSL startup banner),
# so point http(s)_proxy at the Windows host as seen via the default gateway.
# Override the port with CC20_PROXY_PORT when the local proxy differs.
set -x
GW=$(ip route show default | awk '{print $3}')
PORT="${CC20_PROXY_PORT:-7897}"
export https_proxy="http://${GW}:${PORT}"
export http_proxy="http://${GW}:${PORT}"
OUT=/home/peter/cc20
mkdir -p "$OUT"
curl -sSL --retry 2 https://arxiv.org/e-print/2006.13771 -o "$OUT/cc20.bin"
wc -c "$OUT/cc20.bin"
file "$OUT/cc20.bin"
cd "$OUT" || exit 1
rm -rf x
mkdir x
if tar xzf cc20.bin -C x 2>/dev/null; then
  echo TAR_OK
else
  if zcat cc20.bin > x/main.tex 2>/dev/null && [ -s x/main.tex ]; then
    echo SINGLE_TEX_OK
  else
    echo UNPACK_FAIL
  fi
fi
ls x

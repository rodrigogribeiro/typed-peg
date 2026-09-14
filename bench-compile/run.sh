#!/usr/bin/env bash
# Time GHC on generated grammars of growing size.
#
#   ./bench-compile/run.sh                 # the four cheap modes, N = 16 32 48 64
#   ./bench-compile/run.sh wild 16 32      # inference, which now scales
#   ./bench-compile/run.sh minipython 0    # examples/MiniPython.hs, as it is
#
# Besides the wall-clock time it reports GHC's peak heap, in MiB, as the RTS
# measures it ("total memory in use"): the cost that used to make a large
# grammar not compile at all.
#
# HEAP caps GHC's heap (default 8G) so a mode that does not scale fails fast.
#   ./bench-compile/run.sh dense 16 32     # one mode, chosen sizes
#
# What is being measured is type-checking, not code generation, so the
# compiler runs with -fno-code.  -freduction-depth=0 lifts the reduction-stack
# limit, which a dense grammar of this size otherwise hits before it gets slow.
set -u

cd "$(dirname "$0")/.." || exit 1
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

modes=${1:-"dense qq-grammar qq-grammar-expr lookup-witness lookup-key"}
[ $# -gt 0 ] && shift
sizes=${*:-"16 32 48 64"}

cabal build -v0 lib:typed-peg || exit 1

printf '%-18s %6s %10s %10s\n' mode N ms heap-MiB
for mode in $modes; do
  for n in $sizes; do
    case $mode in
      # The lookup modes stand alone; the rest need the library, and need it
      # named: whether `cabal exec` leaves it exposed in the environment file
      # it writes has changed under us before.
      lookup-*) src=$out/Lk.hs;  compile=(ghc) ;;
      minipython) src=$out/MiniPython.hs
                compile=(cabal exec -v0 -- ghc -package typed-peg) ;;
      *)        src=$out/Big.hs
                compile=(cabal exec -v0 -- ghc -package typed-peg) ;;
    esac
    if [ "$mode" = minipython ]; then
      cp examples/MiniPython.hs "$src"
    else
      runghc bench-compile/Gen.hs "$mode" "$n" > "$src" || exit 1
    fi
    start=$(date +%s%N)
    # A heap cap, so that a mode which does not scale fails in seconds with
    # "heap overflow" instead of taking the machine down with it.  The `wild`
    # mode reaches tens of gigabytes at N = 16.
    "${compile[@]}" -fno-code -fforce-recomp -freduction-depth=0 \
      -outputdir "$out/o" "$src" +RTS -M"${HEAP:-8G}" -s"$out/rts" -RTS \
      > "$out/log" 2>&1
    rc=$?
    end=$(date +%s%N)
    if [ $rc -ne 0 ]; then
      printf '%-18s %6s %10s\n' "$mode" "$n" "FAILED"
      tail -5 "$out/log"
    else
      printf '%-18s %6s %10s %10s\n' "$mode" "$n" \
        "$(( (end - start) / 1000000 ))" \
        "$(awk '/total memory in use/ { print $1 }' "$out/rts")"
    fi
  done
done

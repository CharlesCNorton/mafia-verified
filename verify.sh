#!/bin/bash
# Verification gate for mafia.v (TODO 49): fails if the development does not
# compile under Rocq 9.2, if any flagship theorem depends on an axiom, or if any
# Admitted/Axiom/admit remains in the source. Toolchain-agnostic: it drives the
# official rocq/rocq-prover:9.2 container, so it runs the same on a laptop or CI.
set -e
IMG=rocq/rocq-prover:9.2
WORK="$(cd "$(dirname "$0")" && pwd)"

echo "== gate 1: no axiomatic constructs in source =="
# Section-local Variable/Hypothesis are discharged (not axioms) and are caught,
# if they ever leaked, by the Print Assumptions gate below. Here we reject only
# the unambiguous ones.
if grep -nE '^[[:space:]]*(Admitted|Axiom|Conjecture|Postulate)\b|\badmit\b' "$WORK/mafia.v"; then
  echo "GATE FAIL: axiomatic construct found in source"; exit 1
fi
echo "ok"

echo "== gate 2: compiles and flagship theorems are axiom-free =="
docker run --rm -v "$WORK":/work -w /work "$IMG" bash -lc '
  set -e
  rocq compile mafia.v
  cat > /tmp/gate.v <<EOF
Require Import mafia.
Print Assumptions all_members_fully_consistent.
Print Assumptions canonical_person_bijection.
Print Assumptions commission_governance.
Print Assumptions succession_invariants.
Print Assumptions member_index_sound.
Print Assumptions wf_test_suite_passes.
EOF
  n=$(rocq compile -R /work "" /tmp/gate.v 2>&1 | grep -c "Closed under the global context")
  echo "closed-under-global-context: $n / 6"
  [ "$n" -ge 6 ] || { echo "GATE FAIL: axioms detected"; exit 1; }
'
echo "GATE PASS: mafia.v compiles under Rocq 9.2 and is axiom-free"

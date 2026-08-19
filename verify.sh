#!/bin/bash
# Verification gate for mafia.v: fails if the development does not compile under
# Rocq 9.2, if any flagship theorem depends on an axiom, if any Admitted/Axiom/
# admit remains in the source, if the member-definition count disagrees with the
# count the development proves against, or if any member definition never
# reaches an aggregate. Toolchain-agnostic: it drives the official
# rocq/rocq-prover:9.2 container, so it runs the same on a laptop or CI.
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

echo "== gate 2: member definition count matches the declaration proved against =="
# database_is_exhaustive proves |all_members_extended| = declared_member_definitions
# and that record keys are unique. Together with this count, every member
# definition in the source is reachable from all_members_extended.
n_defs=$(grep -cP '^Definition [A-Za-z_0-9]+ : Member :=' "$WORK/mafia.v")
n_decl=$(grep -oP '^Definition declared_member_definitions : nat := \K[0-9]+' "$WORK/mafia.v")
if [ "$n_defs" != "$n_decl" ]; then
  echo "GATE FAIL: $n_defs member definitions in source, $n_decl declared"; exit 1
fi
echo "ok ($n_defs)"

echo "== gate 3: every member definition is referenced outside its own definition =="
orphans=0
for name in $(grep -oP '^Definition \K[A-Za-z_0-9]+(?= : Member :=)' "$WORK/mafia.v"); do
  lines=$(grep -cP "(?<![A-Za-z_0-9])${name}(?![A-Za-z_0-9])" "$WORK/mafia.v")
  if [ "$lines" -lt 2 ]; then echo "ORPHAN: $name"; orphans=$((orphans + 1)); fi
done
if [ "$orphans" -ne 0 ]; then
  echo "GATE FAIL: $orphans member definitions never reach an aggregate"; exit 1
fi
echo "ok"

echo "== gate 4: compiles and flagship theorems are axiom-free =="
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
Print Assumptions same_id_same_person.
Print Assumptions same_name_same_id_or_declared.
Print Assumptions database_is_exhaustive.
Print Assumptions all_members_docket_case_consistent.
Print Assumptions initiation_field_matches_table.
Print Assumptions all_members_evidence_sufficient_effective.
Print Assumptions murder_orders_wf.
Print Assumptions uniqueness_holds_off_historical_exceptions.
EOF
  n=$(rocq compile -R /work "" /tmp/gate.v 2>&1 | grep -c "Closed under the global context")
  echo "closed-under-global-context: $n / 14"
  [ "$n" -ge 14 ] || { echo "GATE FAIL: axioms detected"; exit 1; }
'
echo "GATE PASS: mafia.v compiles under Rocq 9.2 and is axiom-free"

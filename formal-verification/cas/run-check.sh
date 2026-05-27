#!/usr/bin/env bash
# Run every CAS script under formal-verification/cas/ and surface any FAILs.
#
# Each script is expected to print "OK" / "FAIL" for each invariant it
# probes; this runner greps for FAIL and exits non-zero if any appear.

set -u
cd "$(dirname "$0")"

# As CAS witness scripts land, add them to this list. The path is
# relative to this directory (cas/).
scripts=(
  proposer_throttle/charge_evolution.gp
  unstaking_manager/lock_lifecycle.gp
  selector_registry/membership_consistency.gp
  staking_vault/exchange_rate.gp
  staking_vault/multi_token_rewards.gp
  staking_vault/dual_delegation_independence.gp
  proposal_lib/proposal_lifecycle.gp
  governor/escalation.gp
  timelock/scheduling_ordering.gp
  reward_token_registry/registration_lifecycle.gp
)

if [[ ${#scripts[@]} -eq 0 ]]; then
  echo "No CAS scripts registered yet. Add probes to cas/ and list them"
  echo "in cas/run-check.sh as the verification effort grows."
  exit 0
fi

fail=0
for s in "${scripts[@]}"; do
  if [[ ! -f "$s" ]]; then
    echo "==> $s                                     MISSING"
    fail=1
    continue
  fi
  out=$(gp -q "$s" 2>&1)
  if echo "$out" | grep -q FAIL; then
    echo "==> $s                                     FAIL"
    echo "$out"
    fail=1
  else
    printf "==> %-50s ok\n" "$s"
  fi
done

if [[ $fail -ne 0 ]]; then
  echo
  echo "Some CAS scripts failed."
  exit 1
fi

echo
echo "All ${#scripts[@]} scripts passed."

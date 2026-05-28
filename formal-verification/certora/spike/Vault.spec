/* Certora spike spec for Vault.sol.

   Rules:
     - depositIncreasesBalance: after `deposit`, the sender's balance
       grows by exactly msg.value, and `totalDeposited` does too.
     - withdrawDecreasesBalance: after `withdraw`, sender's balance
       drops by `amount`, and `totalDeposited` drops by `amount`.
     - totalDepositedEqualsBalance_safe: for the single-user case,
       totalDeposited equals balances[msg.sender]. Holds for the safe
       deposit/withdraw pair.
     - totalDepositedEqualsBalance_buggy: same invariant, but routed
       through `withdrawBuggy`. Expected to FAIL — the buggy variant
       decrements totalDeposited without touching balances.
*/

methods {
    function balances(address) external returns (uint256) envfree;
    function totalDeposited() external returns (uint256) envfree;
    function deposit() external;
    function withdraw(uint256) external;
    function withdrawBuggy(uint256) external;
}

rule depositIncreasesBalance {
    env e;
    require e.msg.value > 0;
    require e.msg.sender != currentContract;

    uint256 balBefore = balances(e.msg.sender);
    uint256 totBefore = totalDeposited();

    require balBefore + e.msg.value <= max_uint256;
    require totBefore + e.msg.value <= max_uint256;

    deposit(e);

    assert balances(e.msg.sender) == balBefore + e.msg.value;
    assert totalDeposited() == totBefore + e.msg.value;
}

rule withdrawDecreasesBalance {
    env e;
    uint256 amount;
    require amount > 0;
    require balances(e.msg.sender) >= amount;
    require totalDeposited() >= amount;

    uint256 balBefore = balances(e.msg.sender);
    uint256 totBefore = totalDeposited();

    withdraw(e, amount);

    assert balances(e.msg.sender) == balBefore - amount;
    assert totalDeposited() == totBefore - amount;
}

/* Single-user invariant — the safe path. Start from a state where the
   only depositor is `user`, so totalDeposited == balances[user]; show
   that deposit/withdraw preserve that equality.

   We restrict to deposit and withdraw (not withdrawBuggy) so the rule
   should pass. */
rule totalDepositedEqualsBalance_safe(method f)
    filtered { f -> f.selector == sig:deposit().selector ||
                     f.selector == sig:withdraw(uint256).selector } {
    env e;
    calldataarg args;
    require balances(e.msg.sender) == totalDeposited();

    f(e, args);

    assert balances(e.msg.sender) == totalDeposited();
}

/* Same invariant routed through withdrawBuggy — should FAIL, because
   the buggy variant decrements totalDeposited without touching
   balances. This proves the prover actually catches the bug. */
rule totalDepositedEqualsBalance_buggy {
    env e;
    uint256 amount;
    require balances(e.msg.sender) == totalDeposited();
    require amount > 0;
    require balances(e.msg.sender) >= amount;

    withdrawBuggy(e, amount);

    assert balances(e.msg.sender) == totalDeposited();
}

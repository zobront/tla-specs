------------------------ MODULE typedefs --------------------------------
(*
  Type definitions for the module Staking.

  An account address, in our case, simply an uninterpreted string:
  @typeAlias: ADDR = Str;

  @typeAlias: DURATION = Int;

  @typeAlias: TIMESTAMP = Int;

  A transaction
  @typeAlias: TX = [
    id: Int,
    fail: Bool,
    sender: ADDR,
    amount: Int,
    oldDuration: DURATION,
    newDuration: DURATION
  ];

  A state of the state machine:
  @typeAlias: STATE = [
    owners: Int -> ADDR,
    balances: ADDR -> Int,
    tokenApprovals: Int -> ADDR,
    addressApprovals: ADDR -> ADDR,
    mempool: Set(TX),
    lastTx: TX,
    nextTxId: Int
  ];

  Below is a dummy definition to introduce the above type aliases.
 *) 
ERC721_typedefs == TRUE
===============================================================================
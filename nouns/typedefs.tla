------------------------ MODULE typedefs --------------------------------
(*
  Type definitions for the module TEMPLATE.

  An account address, in our case, simply an uninterpreted string:
  @typeAlias: ADDR = Int;
  @typeAlias: BLOCK = Int;

  A transaction
  @typeAlias: TX = [
    id: Int,
    fail: Bool,
    sender: ADDR
  ];

  A state of the state machine:
  @typeAlias: STATE = [
    mempool: Set(TX),
    lastTx: TX,
    nextTxId: Int
  ];

  Below is a dummy definition to introduce the above type aliases.
 *) 
typedefs == TRUE
===============================================================================
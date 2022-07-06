------------------------ MODULE typedefs --------------------------------
(*
  Type definitions for the module TEMPLATE.

  An account address, in our case, simply an uninterpreted string:
  @typeAlias: ADDR = Str;
  @typeAlias: HASH = Int;
  @typeAlias: TOKEN = Str;
  @typeAlias: HASH = Set(<<ADDR, Int>>);

 
  An order
  @typeAlias: ORDER = [
    hash: HASH,
    maker: ADDR,
    isCall: Bool,
    isLong: Bool,
    premium: Int,
    strike: Int,
    baseAsset: TOKEN,
    asset: Set(<<TOKEN, Int>>),
    filled: Bool,
    cancelled: Bool,
    exercised: Bool
  ];

  Below is a dummy definition to introduce the above type aliases.
 *) 
typedefs == TRUE
===============================================================================
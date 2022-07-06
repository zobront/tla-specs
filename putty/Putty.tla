---------------- MODULE Putty -----------------

EXTENDS Integers, Sequences, FiniteSets, typedefs, Apalache

VARIABLES 
    \* @type: Set(ORDER);
    orders,
    \* @type: HASH -> Int;
    expirations,
    \* @type: Int -> ADDR;
    nft_owners,
    \* @type: <<TOKEN, ADDR>> -> Int;
    balances,
    \* @type: Int;
    timestamp

\* @type: () => Set(TOKEN);
ASSETS == { "weth", "erc20-1", "erc20-2", "erc20-3" }

\* @type: () => Set(ADDR);
USERS == { "user1", "user2", "user3" }

\* @type: () => Set(ADDR);
ADDRESSES == USERS \union { "contract", "treasury" }

\* @type: (ORDER, ADDR) => ORDER;
OppositeOrder(order, sender) == [ order EXCEPT !.isLong = ~@, !.hash = <<sender, @[2]>> ]

Init ==
    /\ orders = {}    
    /\ expirations = [ pos \in orders |-> 10 ]
    /\ nft_owners = [ hash \in {x.hash: x \in orders} |-> "0" ]
    /\ balances \in [ ASSETS \X ADDRESSES -> Nat ]
    /\ timestamp = 0

CreateOrder(sender, call, long, premium, strike, baseAsset, asset, amount) ==
    LET new_order == [
        hash |-> <<sender, timestamp>>,
        maker |-> sender,
        isCall |-> call,
        isLong |-> long,
        premium |-> premium,
        strike |-> strike,
        baseAsset |-> baseAsset,
        asset |-> <<asset, amount>>,
        filled |-> FALSE,
        cancelled |-> FALSE,
        exercised |-> FALSE
    ] IN 
    /\ orders' = orders \union {new_order}
    /\ UNCHANGED <<expirations, nft_owners, balances>>

FillOrder(order, sender) ==
    \* require(!cancelledOrders[orderHash], "Order has been cancelled");
    /\ ~order.cancelled
    /\ nft_owners[order.hash] = "0"
    
    \* _mint(order.maker, uint256(orderHash));
    \* _mint(msg.sender, posiuint256(oppositeOrderHash)tionId);
    /\ nft_owners' = [nft_owners EXCEPT ![order.hash] = order.maker, ![OppositeOrder(order, sender).hash] = sender]

    \* positionExpirations[order.isLong ? uint256(orderHash) : positionId] = block.timestamp + order.duration;
    /\ expirations' = [expirations EXCEPT ![order.hash] = timestamp + 10]

    \* // transfer premium to whoever is short from whomever is long
        
        \* // filling long call: transfer assets from taker to contract
    /\  \/  /\ order.isLong /\ order.isCall
            /\ balances' = [balances EXCEPT ![<<order.baseAsset, order.maker>>] = @ - order.premium,
                                            ![<<order.baseAsset, sender>>] = @ + order.premium,
                                            ![<<order.asset[1], sender>>] = @ - order.asset[2],
                                            ![<<order.asset[1], "contract">>] = @ + order.asset[2]]

        \* // filling long put: transfer strike from taker to contract
        \/  /\ order.isLong /\ ~order.isCall
            /\ balances' = [balances EXCEPT ![<<order.baseAsset, order.maker>>] = @ - order.premium,
                                            ![<<order.baseAsset, sender>>] = @ + order.premium - order.strike,
                                            ![<<order.baseAsset, "contract">>] = @ + order.strike]

        \* // filling short call: transfer asset from maker to contract
        \/  /\ ~order.isLong /\ order.isCall
            /\ balances' = [balances EXCEPT ![<<order.baseAsset, sender>>] = @ - order.premium,
                                            ![<<order.baseAsset, order.maker>>] = @ + order.premium,
                                            ![<<order.asset[1], order.maker>>] = @ - order.asset[2],
                                            ![<<order.asset[1], "contract">>] = @ + order.asset[2]]
        
        \* filling short put: transfer strike from maker to contract
        \/  /\ ~order.isLong /\ ~order.isCall
            /\ balances' = [balances EXCEPT ![<<order.baseAsset, sender>>] = @ - order.premium,
                                            ![<<order.baseAsset, order.maker>>] = @ + order.premium - order.strike,
                                            ![<<order.baseAsset, "contract">>] = @ + order.strike]        


Exercise(order, sender) ==
    \* require(ownerOf(uint256(orderHash)) == msg.sender, "Not owner");
    /\ nft_owners[order.hash] = sender
    \* require(order.isLong, "Can only exercise long positions");
    /\ order.isLong
    \* require(block.timestamp < positionExpirations[uint256(orderHash)], "Position has expired");
    /\ timestamp < expirations[order.hash]

    /\ nft_owners' = [nft_owners EXCEPT ![order.hash] = "0xdead"]
    /\ order' = [ order EXCEPT !.exercised = TRUE ]

        \* // -- exercising a call option: transfer strike from exerciser to putty
    /\  \/  /\ order.isCall
            /\ balances' = [balances EXCEPT ![<<order.baseAsset, sender>>] = @ - order.strike,
                                            ![<<order.baseAsset, "contract">>] = @ + order.strike,
                                            ![<<order.asset[1], "contract">>] = @ - order.asset[2],
                                            ![<<order.asset[1], sender>>] = @ + order.asset[2]]
        \* // -- exercising a put option: save the floor asset token ids to the short position
        \/  /\ ~order.isCall
            /\ balances' = [balances EXCEPT ![<<order.baseAsset, sender>>] = @ + order.strike,
                                            ![<<order.baseAsset, "contract">>] = @ - order.strike,
                                            ![<<order.asset[1], "contract">>] = @ + order.asset[2],
                                            ![<<order.asset[1], sender>>] = @ - order.asset[2]]
            
Withdraw(order, sender) ==
    \* require(!order.isLong, "Must be short position");
    /\ ~order.isLong
    \* require(ownerOf(uint256(orderHash)) == msg.sender, "Not owner");
    /\ nft_owners[order.hash] = sender
    \* require(block.timestamp > positionExpirations[longPositionId] || isExercised, "Must be exercised or expired");
    /\  \/ order.exercised
        \/ timestamp > expirations[OppositeOrder(order, sender).hash]
    
    /\ nft_owners' = [nft_owners EXCEPT ![order.hash] = "0xdead"]

        \* // transfer strike to owner if put is expired or call is exercised
    /\  \/  /\ order.isCall = order.exercised
            /\ balances' = [balances EXCEPT ![<<order.baseAsset, "contract">>] = @ - order.strike,
                                            ![<<order.baseAsset, "treasury">>] = @ + 1,
                                            ![<<order.baseAsset, sender>>] = @ + order.strike - 1]

        \* // transfer assets from putty to owner if put is exercised or call is expired
        \/  /\ order.isCall # order.exercised
            /\ balances' = [balances EXCEPT ![<<order.asset[1], "contract">>] = @ - order.asset[2],
                                            ![<<order.asset[1], sender>>] = @ + order.asset[2]]
    /\ UNCHANGED <<orders, expirations>>

Cancel(order, sender) ==
    /\ order.maker = sender
    /\ order' = [ order EXCEPT !.cancelled = TRUE ]
    /\ UNCHANGED <<orders, expirations, nft_owners, balances>>
    
Next == 
    /\  \/  \E  user \in USERS,
                call, long \in BOOLEAN, 
                premium, strike, amount \in Int,
                baseAsset, asset \in ASSETS:
            CreateOrder(user, call, long, premium, strike, baseAsset, asset, amount)

        \/ \E order \in orders, user \in USERS: 
            \/ FillOrder(order, user)
            \/ Exercise(order, user)
            \/ Withdraw(order, user)
            \/ Cancel(order, user)
    /\ timestamp' = timestamp + 1

==================================================
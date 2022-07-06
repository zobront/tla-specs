---------------- MODULE Staking -----------------

EXTENDS Integers, Sequences, FiniteSets, typedefs, Apalache

VARIABLES
    \* @type: <<ADDR, DURATION>> -> <<Int, TIMESTAMP>>;
    userStakedAmounts,

    \* @type: ADDR -> Int;
    balances,

    \* @type: Int;
    balancesInitTotal,

    \* @type: TIMESTAMP;
    blockTimestamp,

    \* @type: DURATION -> Int;
    penalties,

    \* @type:  [fx: Str, sender: ADDR, amount: Int, dur: DURATION, oldDur: DURATION, newDur: DURATION];
    lastTx

\* @type: () => Set(ADDR);
USERS == { "user1", "user2" }

\* @type: () => Set(ADDR);
ADDRESSES == USERS \union { "contract", "treasury" }

\* @type: () => Set(DURATION);
DURATIONS == { 0, 3, 6, 12 }

Init ==
    /\ userStakedAmounts = [ pair \in USERS \X DURATIONS |-> <<0, 0>> ]
    /\ balances \in [ ADDRESSES -> Nat ]
    /\ balances.contract = 0
    /\ \A user \in USERS: balances[user] > 0
    /\ LET AddBalances(a, b) == a + balances[b] IN balancesInitTotal = FoldSet( AddBalances, 0, ADDRESSES )
    /\ blockTimestamp = 1
    /\ penalties = [ duration \in DURATIONS |-> duration ]
    /\ lastTx = [fx |-> "none"]

Stake(sender, amt, dur) ==
    /\ balances[sender] > amt
    /\ amt > 0
    /\ userStakedAmounts' = [ userStakedAmounts EXCEPT ![sender, dur] = <<@[1] + amt, blockTimestamp>> ]
    /\ balances' = [ balances EXCEPT ![sender] = @ - amt, !.contract = @ + amt ]
    /\ blockTimestamp' = blockTimestamp + 1
    /\ lastTx' = [fx |-> "stake", sender |-> sender, amt |-> amt, dur |-> dur]

ChangeDuration(sender, amt, oldDur, newDur) ==
    /\ amt > 0
    /\ userStakedAmounts[sender, oldDur][1] >= amt
    /\ newDur > oldDur
    /\ LET remainingAmt == userStakedAmounts[sender, oldDur][1] - amt IN 
        IF remainingAmt = 0 THEN
            userStakedAmounts' = [ userStakedAmounts EXCEPT ![sender, oldDur] = <<0, 0>>,
                                                               ![sender, newDur] = <<@[1] + amt, blockTimestamp>> ]
        ELSE
            userStakedAmounts' = [ userStakedAmounts EXCEPT ![sender, oldDur] = <<remainingAmt, @[2]>>,
                                                               ![sender, newDur] = <<@[1] + amt, blockTimestamp>> ]
    /\ blockTimestamp' = blockTimestamp + 1
    /\ lastTx' = [fx |-> "changeDuration", sender |-> sender, amt |-> amt, oldDur |-> oldDur, newDur |-> newDur]
    /\ UNCHANGED balances


Unstake(sender, amt) ==
    /\ amt > 0
    /\ LET AddVestedDurations(a, b) == a + userStakedAmounts[sender, b][1] IN 
       LET totalVested == FoldSet( AddVestedDurations, 0, DURATIONS ) IN 
       totalVested > amt
    /\ LET noVesting == userStakedAmounts[sender, 0][1] IN 
         IF noVesting > amt THEN
              userStakedAmounts' = [ userStakedAmounts EXCEPT ![sender, 0] = <<noVesting - amt, @[2]>> ]
         ELSE
              userStakedAmounts' = [ userStakedAmounts EXCEPT ![sender, 0] = <<0, 0>> ]
         /\ LET threeVesting == userStakedAmounts[sender, 3][1] IN
            IF threeVesting > amt - noVesting THEN
                userStakedAmounts' = [ userStakedAmounts EXCEPT ![sender, 3] = <<threeVesting - amt, @[2]>> ]
            ELSE
                userStakedAmounts' = [ userStakedAmounts EXCEPT ![sender, 3] = <<0, 0>> ]
            /\ LET sixVesting == userStakedAmounts[sender, 6][1] IN
                IF sixVesting > amt - noVesting - threeVesting THEN
                    userStakedAmounts' = [ userStakedAmounts EXCEPT ![sender, 6] = <<sixVesting - amt, @[2]>> ]
                ELSE
                    userStakedAmounts' = [ userStakedAmounts EXCEPT ![sender, 6] = <<0, 0>> ]
                /\ LET twelveVesting == userStakedAmounts[sender, 12][1] IN
                    IF twelveVesting > amt - noVesting - threeVesting - sixVesting THEN
                        userStakedAmounts' = [ userStakedAmounts EXCEPT ![sender, 12] = <<twelveVesting - amt, @[2]>> ]
                    ELSE
                        userStakedAmounts' = [ userStakedAmounts EXCEPT ![sender, 12] = <<0, 0>> ]
    /\ balances' = [ balances EXCEPT ![sender] = @ + amt, !.contract = @ - amt ]
    /\ lastTx' = [fx |-> "unstake", sender |-> sender, amt |-> amt]
    /\ blockTimestamp' = blockTimestamp + 1

Ragequit(sender) ==
    /\  LET amountInZero == userStakedAmounts[sender, 0][1] IN
        LET amountInThree == userStakedAmounts[sender, 3][1] IN
        LET threeExpired == userStakedAmounts[sender, 3][2] <= blockTimestamp IN
        LET threePayout == IF threeExpired THEN amountInThree ELSE amountInThree \div penalties[3] IN
        LET amountInSix == userStakedAmounts[sender, 6][1] IN
        LET sixExpired == userStakedAmounts[sender, 6][2] <= blockTimestamp IN
        LET sixPayout == IF sixExpired THEN amountInSix ELSE amountInSix \div penalties[6] IN
        LET amountInTwelve == userStakedAmounts[sender, 12][1] IN
        LET twelveExpired == userStakedAmounts[sender, 12][2] <= blockTimestamp IN
        LET twelvePayout == IF twelveExpired THEN amountInTwelve ELSE amountInTwelve \div penalties[12] IN
        balances' = [ balances EXCEPT ![sender] = @ + amountInZero + threePayout + sixPayout + twelvePayout,
                                      !.contract = @ - amountInZero - amountInThree - amountInSix - amountInTwelve,
                                      !.treasury = @ + amountInThree - threePayout + amountInSix - sixPayout + amountInTwelve - twelvePayout ]
    /\ userStakedAmounts' = [ userStakedAmounts EXCEPT  ![sender, 0] = <<0, 0>>,
                                                        ![sender, 3] = <<0, 0>>,
                                                        ![sender, 6] = <<0, 0>>,
                                                        ![sender, 12] = <<0, 0>> 
                            ]
    /\ blockTimestamp' = blockTimestamp + 1
    /\ lastTx' = [fx |-> "ragequit", sender |-> sender]

Next == /\ \A addr \in ADDRESSES: 
            /\ balances[addr] >= 0
            /\ \A dur \in DURATIONS: userStakedAmounts[addr, dur][1] >= 0
        /\  \/ \E sender \in USERS, dur \in DURATIONS, amt \in Nat: Stake(sender, amt, dur)
            \/ \E sender \in USERS, oldDur, newDur \in DURATIONS, amt \in Nat: ChangeDuration(sender, amt, oldDur, newDur)
            \/ \E sender \in USERS, amt \in Nat: Unstake(sender, amt)
            \/ \E sender \in USERS: Ragequit(sender)
        /\ UNCHANGED <<penalties, balancesInitTotal>>


\* INVARIANTS *\

TotalBalancesNeverChanges == 
    LET AddBalances(a, b) == a + balances[b] IN
    FoldSet( AddBalances, 0, ADDRESSES ) = balancesInitTotal

UserStakedAmountsEqualsContractBalance == 
    LET AddStakedAmounts(a, b) == a + userStakedAmounts[b][1] IN
    FoldSet( AddStakedAmounts, 0, USERS \X DURATIONS ) = balances.contract
    
==================================================
---------------- MODULE Royal -----------------

EXTENDS Integers, Sequences, FiniteSets, Apalache

\* @typeAlias: ADDR = Str;
\* @typeAlias: TIER_ID = Int;
\* @typeAlias: DEPOSIT_ID = Int;
\* @typeAlias: TOKEN_ID = Int;
typedefs == TRUE

VARIABLES 
    \* @type: TIER_ID -> DEPOSIT_ID;
    latest_deposit_id,
    \* @type: TIER_ID -> DEPOSIT_ID;
    last_reclaimed_deposits,
    \* @type: <<TIER_ID, DEPOSIT_ID>> -> ADDR;
    deposit_to_depositor,
    \* @type: <<TIER_ID, DEPOSIT_ID>> -> Int;
    deposit_to_timestamp,
    \* @type: <<TIER_ID, DEPOSIT_ID>> -> Int;
    claims_by_deposit,
    \* @type: <<TIER_ID, DEPOSIT_ID>> -> Int;
    deposit_to_amount,
    \* @type: <<TIER_ID, DEPOSIT_ID>> -> Int;
    cumulative_deposits,
    \* @type: <<TIER_ID, ADDR>> -> DEPOSIT_ID;
    last_settled_deposits,
    \* @type: <<TIER_ID, ADDR>> -> DEPOSIT_ID;
    last_claimed_deposits,
    \* @type: <<TIER_ID, ADDR>> -> Int;
    claimable,
    \* @type: <<TOKEN_ID, TIER_ID>> -> DEPOSIT_ID;
    token_to_tier_to_last_claimed_deposit,
    \* @type: Int;
    timestamp,
    \* @type: ADDR -> Int;
    balances,
    \* @type: <<TIER_ID, TOKEN_ID>> -> ADDR;
    lda_tokens_by_tier,
    \* @type: [ fx: Str, sender: ADDR, to: ADDR, amount: Int, tier: TIER_ID, token: TOKEN_ID ];
    _last_called

MAX_DEPOSIT_ID == 3
USERS == { "user1", "user2", "user3" }
DEPOSITORS == { "dep1", "dep2" }
ADDRESSES == USERS \union DEPOSITORS \union { "contract" }
TIERS == (1..2)
TOKENS == (1..3)

Init == 
    /\ latest_deposit_id = [ tier \in TIERS |-> 0 ]
    /\ last_reclaimed_deposits = [ tier \in TIERS |-> 0 ]
    /\ deposit_to_depositor = [ tierDepositPair \in TIERS \X (0..MAX_DEPOSIT_ID) |-> "" ]
    /\ deposit_to_timestamp = [ tierDepositPair \in TIERS \X (0..MAX_DEPOSIT_ID) |-> 0 ]
    /\ claims_by_deposit = [ tierDepositPair \in TIERS \X (0..MAX_DEPOSIT_ID) |-> 0 ]
    /\ deposit_to_amount = [ tierDepositPair \in TIERS \X (0..MAX_DEPOSIT_ID) |-> 0 ]
    /\ cumulative_deposits = [ tierDepositPair \in TIERS \X (0..MAX_DEPOSIT_ID) |-> 0 ]
    /\ last_settled_deposits = [ tierUserPair \in TIERS \X USERS |-> 0 ]
    /\ last_claimed_deposits = [ tierUserPair \in TIERS \X USERS |-> 0 ]
    /\ claimable = [ tierUserPair \in TIERS \X USERS |-> 0 ]
    /\ token_to_tier_to_last_claimed_deposit = [ tokenTierPair \in TOKENS \X TIERS |-> 0 ]
    /\ timestamp = 0
    /\ balances = [ addr \in ADDRESSES |-> IF addr # "contract" THEN 1000000 ELSE 0 ]
    /\ lda_tokens_by_tier = [ tierTokenPair \in TIERS \X TOKENS |-> CHOOSE addr \in ADDRESSES: addr \in USERS ]
    /\ _last_called = [ fx |-> "Init" ]

Deposit(sender, tierId, amount) ==
    /\ balances[sender] >= amount
    /\ latest_deposit_id[tierId] < MAX_DEPOSIT_ID
    /\ latest_deposit_id' = [ latest_deposit_id EXCEPT ![tierId] = @ + 1]
    /\ deposit_to_timestamp' = [ deposit_to_timestamp EXCEPT ![<<tierId, (latest_deposit_id[tierId] + 1)>>] = timestamp ]
    /\ deposit_to_depositor' = [ deposit_to_depositor EXCEPT ![<<tierId, (latest_deposit_id[tierId] + 1)>>] = sender ]
    /\ deposit_to_amount' = [ deposit_to_amount EXCEPT ![<<tierId, (latest_deposit_id[tierId] + 1)>>] = amount ]
    /\ cumulative_deposits' = [ cumulative_deposits EXCEPT ![<<tierId, (latest_deposit_id[tierId] + 1)>>] = cumulative_deposits[<<tierId, (latest_deposit_id[tierId] + 1)>>] + amount ]
    /\ balances' = [ balances EXCEPT ![sender] = @ - amount, !["contract"] = @ + amount ]
    /\ _last_called' = [ fx |-> "deposit", sender |-> sender, amount |-> amount, tier |-> tierId ]
    /\ UNCHANGED <<last_reclaimed_deposits, claims_by_deposit, last_settled_deposits, last_claimed_deposits, claimable, token_to_tier_to_last_claimed_deposit, lda_tokens_by_tier>>

Claim(sender, tierId) ==
    /\ LET clearBalances == last_reclaimed_deposits[tierId] > last_settled_deposits[<<tierId, sender>>] IN
        LET settled_and_reclaimed == { last_reclaimed_deposits[tierId], last_settled_deposits[<<tierId, sender>>] } IN
        LET start_deposit_id == CHOOSE x \in settled_and_reclaimed: \A y \in settled_and_reclaimed : x >= y IN 
        LET GetUserTierTokenCount(a, b) == IF lda_tokens_by_tier[<<tierId, b>>] = sender THEN a + 1 ELSE a IN
        LET USER_TOKEN_COUNT == ApaFoldSet( GetUserTierTokenCount, 0, TOKENS ) IN
        LET new_payment_amount == (((cumulative_deposits[<<tierId, latest_deposit_id[tierId]>>] - cumulative_deposits[<<tierId, start_deposit_id>>]) * USER_TOKEN_COUNT) \div Cardinality(TOKENS)) IN
        LET payment_amount == IF clearBalances THEN new_payment_amount ELSE claimable[<<tierId, sender>>] + new_payment_amount IN
        balances' = [ balances EXCEPT ![sender] = @ + payment_amount, !["contract"] = @ - payment_amount ]
    /\ LET ownedTokens == { id \in TOKENS: lda_tokens_by_tier[<<tierId, id>>] = sender } IN
        /\ claims_by_deposit' = [ claims_by_deposit EXCEPT ![<<tierId, latest_deposit_id[tierId]>>] = @ + Cardinality(ownedTokens) ]
        /\ token_to_tier_to_last_claimed_deposit' = [ tokenTierPair \in TOKENS \X TIERS |-> IF tokenTierPair[1] \in ownedTokens THEN latest_deposit_id[tierId] ELSE token_to_tier_to_last_claimed_deposit[tokenTierPair] ]
    /\ last_claimed_deposits' = [ last_claimed_deposits EXCEPT ![<<tierId, sender>>] = latest_deposit_id[tierId] ]
    /\ last_settled_deposits' = [ last_settled_deposits EXCEPT ![<<tierId, sender>>] = latest_deposit_id[tierId] ]
    /\ claimable' = [ claimable EXCEPT ![<<tierId, sender>>] = 0 ]
    /\ _last_called' = [ fx |-> "claim", sender |-> sender, tier |-> tierId ]
    /\ UNCHANGED <<latest_deposit_id, last_reclaimed_deposits, deposit_to_depositor, deposit_to_timestamp, deposit_to_amount, cumulative_deposits, lda_tokens_by_tier>>

Reclaim(sender, tierId, depositId) ==
    /\ depositId <= latest_deposit_id[tierId]
    /\ depositId > last_reclaimed_deposits[tierId]
    /\ deposit_to_timestamp[<<tierId, depositId>>] + 5 < timestamp
    /\ LET GetUnclaimedSupply(a, b) == 
            IF b < last_reclaimed_deposits[tierId] \/ b > latest_deposit_id[tierId] 
            THEN a 
            ELSE a + (Cardinality(TOKENS) - claims_by_deposit[<<tierId, b>>])
        IN 
        LET UNCLAIMED_SUPPLY == ApaFoldSet( GetUnclaimedSupply, 0, (1..MAX_DEPOSIT_ID)) IN 
        LET GetTotalDepositAmounts(a, b) == a + deposit_to_amount[<<tierId, b>>] IN
        LET DepositsByRefundAddr(addr) == { depId \in (1..MAX_DEPOSIT_ID): deposit_to_depositor[<<tierId, depId>>] = addr } IN
        LET deposit_amounts == [ dep \in DEPOSITORS |-> ApaFoldSet( GetTotalDepositAmounts, 0, DepositsByRefundAddr(dep) )] IN
        LET total_deposit_amount == ApaFoldSet( GetTotalDepositAmounts, 0, (1..MAX_DEPOSIT_ID) ) IN
        balances' = [ addr \in ADDRESSES |-> IF addr \in DEPOSITORS
                                                THEN balances[addr] + deposit_amounts[addr]
                                                ELSE 
                                                    IF addr = "contract"
                                                    THEN balances[addr] - total_deposit_amount
                                                    ELSE balances[addr] ]
    /\ last_reclaimed_deposits' = [ last_reclaimed_deposits EXCEPT ![tierId] = depositId ]
    /\ _last_called' = [ fx |-> "reclaim", sender |-> sender, tier |-> tierId ]
    /\ UNCHANGED <<latest_deposit_id, deposit_to_depositor, deposit_to_timestamp, claims_by_deposit, deposit_to_amount, cumulative_deposits, last_settled_deposits, last_claimed_deposits, claimable, token_to_tier_to_last_claimed_deposit, lda_tokens_by_tier>>

Transfer(sender, to, tierId, tokenId) ==
    /\ lda_tokens_by_tier[<<tierId, tokenId>>] = sender
    /\ lda_tokens_by_tier' = [lda_tokens_by_tier EXCEPT ![<<tierId, tokenId>>] = to]
    /\ IF last_reclaimed_deposits[tierId] > last_settled_deposits[<<tierId, sender>>] 
        THEN 
            claimable' = [ claimable EXCEPT ![<<tierId, sender>>] = 0 ]
        ELSE 
            LET settled_and_reclaimed == { last_reclaimed_deposits[tierId], last_settled_deposits[<<tierId, sender>>] } IN
            LET start_deposit_id == CHOOSE x \in settled_and_reclaimed: \A y \in settled_and_reclaimed : x >= y IN 
            LET GetUserTierTokenCount(a, b) == IF lda_tokens_by_tier[<<tierId, b>>] = sender THEN a + 1 ELSE a IN
            LET USER_TOKEN_COUNT == ApaFoldSet( GetUserTierTokenCount, 0, TOKENS ) IN
            LET payment_amount == (((cumulative_deposits[<<tierId, latest_deposit_id[tierId]>>] - cumulative_deposits[<<tierId, start_deposit_id>>]) * USER_TOKEN_COUNT) \div Cardinality(TOKENS)) IN
            claimable' = [ claimable EXCEPT ![<<tierId, sender>>] = @ + payment_amount ]
    /\ last_settled_deposits' = [ last_settled_deposits EXCEPT ![<<tierId, sender>>] = latest_deposit_id[tierId], ![<<tierId, to>>] = latest_deposit_id[tierId] ]
    /\ _last_called' = [ fx |-> "transfer", sender |-> sender, to |-> to, tier |-> tierId, token |-> tokenId ]
    /\ UNCHANGED <<latest_deposit_id, last_reclaimed_deposits, deposit_to_depositor, deposit_to_timestamp, claims_by_deposit, deposit_to_amount, cumulative_deposits, last_claimed_deposits, token_to_tier_to_last_claimed_deposit, balances>>
    
Next == 
    /\  \/ \E depositor \in DEPOSITORS, amount \in Nat, tierId \in TIERS: Deposit(depositor, tierId, amount)
        \/ \E user \in USERS, tierId \in TIERS: Claim(user, tierId)
        \/ \E depositor \in DEPOSITORS, tierId \in TIERS, depositId \in (1..MAX_DEPOSIT_ID): Reclaim(depositor, tierId, depositId) 
        \/ \E from, to \in USERS, tierId \in TIERS, tokenId \in TOKENS: Transfer(from, to, tierId, tokenId)
    /\ timestamp' = timestamp + 1


\* INVARIANTS

ContractIsPositive == balances["contract"] >= 0


    
==================================================
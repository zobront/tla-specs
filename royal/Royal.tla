---------------- MODULE Royal -----------------

EXTENDS Integers, Sequences, FiniteSets, Apalache

\* @typeAlias: ADDR = Str;
\* @typeAlias: TIER_ID = Int;
\* @typeAlias: DEPOSIT_ID = Int;
\* @typeAlias: TOKEN_ID = Int;
typedefs == TRUE

\* CONSTANTS
\*     \* @type: DEPOSIT_ID;
\*     MAX_DEPOSIT_ID

VARIABLES 
    \* @type: TIER_ID -> DEPOSIT_ID;
    latest_deposit_id,
    \* @type: TIER_ID -> DEPOSIT_ID;
    last_reclaimed_deposits,
    \* @type: <<TIER_ID, DEPOSIT_ID>> -> ADDR;
    deposit_to_refund_address,
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
    lda_tokens_by_tier

MAX_DEPOSIT_ID == 10
TOKENS_PER_TIER == 1000
USERS == { "user1", "user2", "user3" }
DEPOSITORS == { "dep1", "dep2" }
ADDRESSES == USERS \union DEPOSITORS \union { "contract" }
TIERS == { 1, 2, 3 }
TOKENS == TIERS \union { 20 }

Init == 
    /\ latest_deposit_id = [ tier \in TIERS |-> 0 ]
    /\ last_reclaimed_deposits = [ tier \in TIERS |-> 0 ]
    /\ deposit_to_refund_address = [ tierDepositPair \in TIERS \X (0..MAX_DEPOSIT_ID) |-> "" ]
    /\ deposit_to_depositor = [ tierDepositPair \in TIERS \X (0..MAX_DEPOSIT_ID) |-> "" ]
    /\ deposit_to_timestamp = [ tierDepositPair \in TIERS \X (0..MAX_DEPOSIT_ID) |-> 0 ]
    /\ claims_by_deposit = [ tierDepositPair \in TIERS \X (0..MAX_DEPOSIT_ID) |-> 0 ]
    /\ deposit_to_amount = [ tierDepositPair \in TIERS \X (0..MAX_DEPOSIT_ID) |-> 0 ]
    /\ cumulative_deposits = [ tierDepositPair \in TIERS \X (0..MAX_DEPOSIT_ID) |-> 0 ]
    /\ last_settled_deposits = [ tierUserPair \in TIERS \X USERS |-> 0 ]
    /\ last_claimed_deposits = [ tierUserPair \in TIERS \X USERS |-> 0 ]
    /\ claimable = [ tierUserPair \in TIERS \X USERS |-> 0 ]
    /\ token_to_tier_to_last_claimed_deposit = [ tokenTierPair \in (0..TOKENS_PER_TIER) \X TIERS |-> 0 ]
    /\ timestamp = 0
    /\ balances = [ addr \in ADDRESSES |-> 1000000 ]
    /\ lda_tokens_by_tier = [ tierTokenPair \in TIERS \X (0..TOKENS_PER_TIER) |-> CHOOSE addr \in ADDRESSES: addr \in USERS ]

Deposit(sender, tierId, amount) ==
    /\ balances[sender] >= amount
    /\ latest_deposit_id' = [ latest_deposit_id EXCEPT ![tierId] = @ + 1]
    /\ deposit_to_refund_address' = [ deposit_to_refund_address EXCEPT ![<<tierId, (latest_deposit_id[tierId] + 1)>>] = sender ]
    /\ deposit_to_timestamp' = [ deposit_to_timestamp EXCEPT ![<<tierId, (latest_deposit_id[tierId] + 1)>>] = timestamp ]
    /\ deposit_to_depositor' = [ deposit_to_depositor EXCEPT ![<<tierId, (latest_deposit_id[tierId] + 1)>>] = sender ]
    /\ deposit_to_amount' = [ deposit_to_amount EXCEPT ![<<tierId, (latest_deposit_id[tierId] + 1)>>] = amount ]
    /\ cumulative_deposits' = [ cumulative_deposits EXCEPT ![<<tierId, (latest_deposit_id[tierId] + 1)>>] = cumulative_deposits[<<tierId, (latest_deposit_id[tierId] + 1)>>] + amount ]
    /\ balances' = [ balances EXCEPT ![sender] = @ - amount, !["contract"] = @ + amount ]
    /\ UNCHANGED <<last_reclaimed_deposits, claims_by_deposit, last_settled_deposits, last_claimed_deposits, claimable, token_to_tier_to_last_claimed_deposit, lda_tokens_by_tier>>

Claim(sender, tierId) ==
    /\ LET clearBalances == last_reclaimed_deposits[tierId] > last_settled_deposits[<<tierId, sender>>] IN
        LET settled_and_reclaimed == { last_reclaimed_deposits[tierId], last_settled_deposits[<<tierId, sender>>] } IN
        LET start_deposit_id == CHOOSE x \in settled_and_reclaimed: \A y \in settled_and_reclaimed : x >= y IN 
        LET GetUserTierTokenCount(a, b) == IF lda_tokens_by_tier[<<tierId, b>>] = sender THEN a + 1 ELSE a IN
        LET USER_TOKEN_COUNT == FoldSet( GetUserTierTokenCount, 0, (0..TOKENS_PER_TIER) ) IN
        LET new_payment_amount == (((cumulative_deposits[<<tierId, latest_deposit_id[tierId]>>] - cumulative_deposits[<<tierId, start_deposit_id>>]) * USER_TOKEN_COUNT) \div TOKENS_PER_TIER) IN
        LET payment_amount == IF clearBalances THEN new_payment_amount ELSE claimable[<<tierId, sender>>] + new_payment_amount IN
        balances' = [ balances EXCEPT ![sender] = @ + payment_amount, !["contract"] = @ - payment_amount ]
    /\ LET ownedTokens == { id \in (0..TOKENS_PER_TIER): lda_tokens_by_tier[<<tierId, id>>] = sender } IN
        /\ claims_by_deposit' = [ claims_by_deposit EXCEPT ![<<tierId, latest_deposit_id[tierId]>>] = @ + Cardinality(ownedTokens) ]
        \* igor used : in below instead of |->
        /\ token_to_tier_to_last_claimed_deposit' = [ tokenTierPair \in (0..TOKENS_PER_TIER) \X TIERS |-> IF tokenTierPair[1] \in ownedTokens THEN latest_deposit_id[tierId] ELSE token_to_tier_to_last_claimed_deposit[tokenTierPair] ]
    /\ last_claimed_deposits' = [ last_claimed_deposits EXCEPT ![<<tierId, sender>>] = latest_deposit_id[tierId] ]
    /\ last_settled_deposits' = [ last_settled_deposits EXCEPT ![<<tierId, sender>>] = latest_deposit_id[tierId] ]
    /\ claimable' = [ claimable EXCEPT ![<<tierId, sender>>] = 0 ]
    /\ UNCHANGED <<latest_deposit_id, last_reclaimed_deposits, deposit_to_refund_address, deposit_to_depositor, deposit_to_timestamp, deposit_to_amount, cumulative_deposits, lda_tokens_by_tier>>

Reclaim(sender, tierId) ==
    /\ LET maxDepositId == CHOOSE depId \in (0..latest_deposit_id[tierId]): last_reclaimed_deposits[tierId] < depId IN
        /\ deposit_to_timestamp[<<tierId, maxDepositId>>] + 5 < timestamp
        /\ LET DEPOSIT_IDS_TO_SCAN == ( last_reclaimed_deposits[tierId] .. latest_deposit_id[tierId] ) IN
            LET GetUnclaimedSupply(a, b) == a + (TOKENS_PER_TIER - claims_by_deposit[<<tierId, b>>]) IN 
            LET UNCLAIMED_SUPPLY == FoldSet( GetUnclaimedSupply, 0, DEPOSIT_IDS_TO_SCAN) IN 
            LET GetTotalDepositAmounts(a, b) == a + deposit_to_amount[<<tierId, b>>] IN
            LET DepositsByRefundAddr(addr) == { depositId \in (0..MAX_DEPOSIT_ID): deposit_to_refund_address[<<tierId, depositId>>] = addr } IN
            LET deposit_amounts == [ dep \in DEPOSITORS |-> FoldSet( GetTotalDepositAmounts, 0, DepositsByRefundAddr(dep) )] IN
            LET total_deposit_amount == FoldSet( GetTotalDepositAmounts, 0, (0..MAX_DEPOSIT_ID) ) IN
            balances' = [ addr \in ADDRESSES |-> IF addr \in DEPOSITORS
                                                    THEN balances[addr] + deposit_amounts[addr]
                                                    ELSE 
                                                        IF addr = "contract"
                                                        THEN balances[addr] - total_deposit_amount
                                                        ELSE balances[addr] ]
        /\ last_reclaimed_deposits' = [ last_reclaimed_deposits EXCEPT ![tierId] = maxDepositId ]
    /\ UNCHANGED <<latest_deposit_id, deposit_to_refund_address, deposit_to_depositor, deposit_to_timestamp, claims_by_deposit, deposit_to_amount, cumulative_deposits, last_settled_deposits, last_claimed_deposits, claimable, token_to_tier_to_last_claimed_deposit, lda_tokens_by_tier>>

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
            LET USER_TOKEN_COUNT == FoldSet( GetUserTierTokenCount, 0, (0..TOKENS_PER_TIER) ) IN
            LET payment_amount == (((cumulative_deposits[<<tierId, latest_deposit_id[tierId]>>] - cumulative_deposits[<<tierId, start_deposit_id>>]) * USER_TOKEN_COUNT) \div TOKENS_PER_TIER) IN
            claimable' = [ claimable EXCEPT ![<<tierId, sender>>] = @ + payment_amount ]
    /\ last_settled_deposits' = [ last_settled_deposits EXCEPT ![<<tierId, sender>>] = latest_deposit_id[tierId] ]
    /\ UNCHANGED <<latest_deposit_id, last_reclaimed_deposits, deposit_to_depositor, deposit_to_refund_address, deposit_to_timestamp, claims_by_deposit, deposit_to_amount, cumulative_deposits, last_claimed_deposits, token_to_tier_to_last_claimed_deposit, balances>>
    
Next == 
    /\  \/ \E depositor \in DEPOSITORS, amount \in (0..1000000), tierId \in TIERS: Deposit(depositor, tierId, amount)
        \/ \E user \in USERS, tierId \in TIERS: Claim(user, tierId)
        \/ \E depositor \in DEPOSITORS, tierId \in TIERS: Reclaim(depositor, tierId) 
        \/ \E from, to \in USERS, tierId \in TIERS, tokenId \in (0..1000): Transfer(from, to, tierId, tokenId)
    /\ timestamp' = timestamp + 1


\* INVARIANTS

ContractCantGoNegative == LET ContractPositive == balances["contract"] > 0 IN ~ContractPositive
    
==================================================
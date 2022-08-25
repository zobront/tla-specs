---------------- MODULE Nouns -----------------

EXTENDS Integers, Sequences, FiniteSets, typedefs, Apalache

VARIABLES 
    \* @type: Int;
    totalSupply,

    \* @type: ADDR -> Int;
    balances,

    \* @type: <<ADDR, Int>> -> <<BLOCK, Int>>;
    checkpoints,

    \* @type: ADDR -> Int;
    numCheckpoints,

    \* @type: ADDR -> ADDR;
    delegates,

    \* @type: BLOCK;
    block

\* @type: () => Set(ADDR);
USERS == { 1, 2, 3 }

CHECKPOINTS == { 1, 2, 3, 4 }

\* @type: () => Set(ADDR);
ADDRESSES == USERS \union { 0 }

Init == 
    /\ balances = [ x \in USERS |-> 0 ]
    /\ checkpoints = [ pair \in USERS \X CHECKPOINTS |-> <<0, 0>> ]
    /\ delegates \in [ USERS -> ADDRESSES ]
    /\ numCheckpoints = [ x \in USERS |-> 0 ]
    /\ block = 0
    /\ totalSupply = 0

MoveDelegates(fromDel, toDel, amt) == 
    \/  /\  \/ fromDel # toDel
            \/ fromDel = 0 /\ toDel = 0
        /\ UNCHANGED <<checkpoints, numCheckpoints>>
    \/  /\ fromDel # 0 /\ toDel = 0
        /\ checkpoints' = [ checkpoints EXCEPT ![<<fromDel, numCheckpoints[fromDel] + 1>>] 
            = <<block, checkpoints[<<fromDel, numCheckpoints[fromDel]>>][1] - amt>> ]
        /\ numCheckpoints' = [ numCheckpoints EXCEPT ![fromDel] = @ + 1 ]
    \/  /\ fromDel = 0 /\ toDel # 0
        /\ checkpoints' = [ checkpoints EXCEPT ![<<toDel, numCheckpoints[toDel] + 1>>] 
            = <<block, checkpoints[<<toDel, numCheckpoints[toDel]>>][1] + amt>> ]
        /\ numCheckpoints' = [ numCheckpoints EXCEPT ![toDel] = @ + 1 ] 
    \/  /\ fromDel # 0 /\ toDel # 0 /\ fromDel # toDel
        /\ checkpoints' = [ checkpoints EXCEPT 
            ![<<fromDel, numCheckpoints[fromDel] + 1>>] = <<block, checkpoints[<<fromDel, numCheckpoints[fromDel]>>][1] - amt>>,
            ![<<toDel, numCheckpoints[toDel] + 1>>] = <<block, checkpoints[<<toDel, numCheckpoints[toDel]>>][1] + amt>> ]
        /\ numCheckpoints' = [ numCheckpoints EXCEPT ![toDel] = @ + 1, ![fromDel] = @ + 1 ] 

MaybeUpdateBlock ==
    \/ block' = block + 1
    \/ UNCHANGED block

Transfer(from, to) ==
    \/  /\ from = 0 /\ to # 0
        /\ balances' = [ balances EXCEPT ![to] = @ + 1 ]
        /\ MoveDelegates(0, delegates[to], 1)
        /\ totalSupply' = totalSupply + 1
    \/  /\ to = 0 /\ from # 0
        /\ balances[from] > 0
        /\ balances' = [ balances EXCEPT ![from] = @ - 1 ]
        /\ MoveDelegates(delegates[from], 0, 1)
        /\ totalSupply' = totalSupply - 1
    \/  /\ to # 0 /\ from # 0
        /\ balances[from] > 0
        /\ balances' = [ balances EXCEPT ![from] = @ - 1, ![to] = @ + 1 ]
        /\ MoveDelegates(delegates[from], delegates[to], 1)
        /\ UNCHANGED totalSupply
    /\ MaybeUpdateBlock
    /\ UNCHANGED delegates

Delegate(sender, to) ==
    \* /\ to # 0 => redundant because selecting from USERS
    /\ delegates' = [ delegates EXCEPT ![sender] = to ]
    /\ MoveDelegates(delegates[sender], to, balances[sender])
    /\ MaybeUpdateBlock
    /\ UNCHANGED <<balances, totalSupply>>

Next == 
    \/ \E from, to \in ADDRESSES: Transfer(from, to)
    \/ \E from, to \in USERS: Delegate(from, to)


\* INVARIANTS *\

DelegatesVotesEqualsTotalSupply == 
    LET AddVotes(a, b) == a + checkpoints[<<b, numCheckpoints[b]>>][1] IN 
    ApaFoldSet( AddVotes, 0, USERS ) = totalSupply
    
DelegatedPowerShouldEqualBalancePlusDelegatees ==
    \A u \in USERS:
        LET AddBalances(a, b) == a + balances[b] IN 
        LET Delegatees == {x \in USERS : delegates[x] = u} IN
        LET DelegatedVotes = ApaFoldSet ( AddBalances, 0, Delegatees ) IN 
        balances[u] + DelegatedVotes = checkpoints[<<u, numCheckpoints[u]>>][1]

==================================================
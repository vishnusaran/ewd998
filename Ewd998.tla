---------------------- MODULE Ewd998 ---------------------
EXTENDS Naturals, Integers

\* * A constant is a parameter of a specification. In other words, it is a
 \* * "variable" that cannot change throughout a behavior, i.e., a sequence
 \* * of states. Below, we declares N to be a constant of this spec.
 \* * We don't know what value N has or even what its type is; TLA+ is untyped and
 \* * everything is a set. In fact, even 23 and "frob" are sets and 23="frob" is 
 \* * syntactically correct.  However, we don't know what elements are in the sets 
 \* * 23 and "frob" (nor do we care). The value of 23="frob" is undefined, and TLA+
 \* * users call this a "silly expression".
CONSTANT N 

\* * We should declare what we assume about the parameters of a spec--the constants.
 \* * In this spec, we assume constant N to be a (positive) natural number, by
 \* * stating that N is in the set of Nat (defined in Naturals.tla) without 0 (zero).
 \* * Note that the TLC model-checker, which we will meet later, checks assumptions
 \* * upon startup.
NIsPosNat == N \in Nat \ {0}

ASSUME NIsPosNat

Node == 0 .. N - 1 

White == "white"
Black == "black"
Colors == {White, Black}

VARIABLE    active,
            color,
            counter,

            network,
            token,
            terminationDetected

vars == <<active, color, counter, network, token, terminationDetected>>

terminated ==
    \A n \in Node: active[n] = FALSE /\ network[n] = 0

isTerminationDetected ==
     /\ token.pos = 0 
     /\ token.q = 0 
     /\ active[0] = FALSE
     /\ token.color = White

TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> Nat ]
    /\ color \in [Node -> Colors]
    /\ counter \in [Node -> Int]
    /\ token \in [ q: Int, color:Colors, pos:Node]
    /\ terminationDetected \in BOOLEAN

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> {0} ]
    /\ token \in [ q: {0}, color:{White}, pos:{0}]
    /\ color \in [Node -> Colors]
    /\ counter \in [Node -> {0}]
    /\ terminationDetected \in {isTerminationDetected, FALSE}

Terminates(n) ==
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ terminationDetected' \in {isTerminationDetected, terminationDetected}
    /\ UNCHANGED <<color,counter, network, token>>

SendMsg(snd, rcv) ==
    /\ active[snd] = TRUE
    /\ counter' = [counter EXCEPT ![snd] = @ + 1]
    /\ network' = [ network EXCEPT ![rcv] = @ + 1 ]
    /\ UNCHANGED <<active, color, token, terminationDetected>>

RecvMsg(rcv) ==
    /\ network[rcv] > 0
    /\ active' = [active EXCEPT ![rcv] = TRUE]
    /\ counter' = [counter EXCEPT ![rcv] = @ - 1]
    /\ color' = [color EXCEPT ![rcv] = "black"]
    /\ network' = [ network EXCEPT ![rcv] = network[rcv] - 1 ]
    /\ UNCHANGED <<token, terminationDetected>>

InitiateToken  == 
    /\ token.pos = 0
    /\ color' = [color EXCEPT ![0] = White]
    /\ terminationDetected = FALSE
    /\ token' = [q |-> 0, color |-> White, pos |->0]
    /\ UNCHANGED <<active, color, counter, network, terminationDetected>>

PassToken == 
    /\ token.nodesVisited < N
    /\ active[token.pos] = FALSE
    /\ color' = [color EXCEPT ![token.pos] = White]
    /\ token' = [token EXCEPT !.pos = (token.pos + 1) % N,
                              !.q = token.q + counter[token.pos],
                              !.color = IF color[token.pos] = Black THEN Black ELSE token.color]                              
    /\ UNCHANGED <<active, counter, network, terminationDetected>>

Next ==
    \E n,m \in Node:
        \/ Terminates(n)
        \/ SendMsg(n,m)
        \/ RecvMsg(n)
        \/ PassToken
        \/ InitiateToken

Spec ==
    Init /\ [] [Next]_vars /\ WF_vars(Next)

Safe ==
     [](terminationDetected => terminated)

Live ==
     [](terminated => <>terminationDetected)     


-------------------

Constraint ==
    \* /\ \A n \in Node: network[n] < 3 
    \* /\ \A n \in Node: counter[n] \in [-3 .. 3]
    \A n \in Node: network[n] < 3 /\ counter[n] \in -3 .. 3


================================
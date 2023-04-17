---------------------- MODULE DieHard ---------------------
\* * TLA+ is an expressive language and we usually define operators on-the-fly.
 \* * That said, the TLA+ reference guide "Specifying Systems" (download from:
 \* * https://lamport.azurewebsites.net/tla/book.html) defines a handful of
 \* * standard modules.  Additionally, a community-driven repository has been
 \* * collecting more modules (http://modules.tlapl.us). In our spec, we are
 \* * going to need operators for natural numbers.
EXTENDS Naturals, Integers

CONSTANT targetCap 

VARIABLES jug5GCap, jug3GCap

\* MIN(x,y) == IF x > y THEN y ELSE x 
\* MAX(x,y) == IF x > y THEN x ELSE y    

\* Init ==
\*     /\ jug5GCap = 0
\*     /\ jug3GCap = 0
    
\* set3GCap(cap) ==
\*     /\ jug3GCap' = cap
\*     /\ UNCHANGED jug5GCap

\* set5GCap(cap) == 
\*     /\ jug5GCap' = cap
\*     /\ UNCHANGED jug3GCap    

\* pourOut3G ==
\*     /\ jug3GCap' = 0
\*     /\ UNCHANGED jug5GCap

\* pourOut5G ==
\*     /\ jug5GCap' = 0
\*     /\ UNCHANGED jug3GCap

\* pourIntoJug3G ==
\*     /\ jug5GCap' = MAX(0, jug5GCap - jug3GCap)
\*     /\ jug3GCap' = 0


\* pourIntoJug5G ==     
\*     /\ jug3GCap' = MIN(0, jug3GCap - jug5GCap)
\*     /\ jug5GCap' = 0


\* Next ==
\*     \E n \in {1..3}:
\*         \E m \in {1..5}:
\*             /\ set3GCap(n)
\*             /\ set5GCap(m)
\*             \/
\*                 \/ pourOut3G
\*                 \/ pourOut5G
\*                 \/ pourIntoJug3G
\*                 \/ pourIntoJug5G



=============================================================================
\* Modification History

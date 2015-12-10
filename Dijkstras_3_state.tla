------------------------- MODULE Djikstras_3_state -------------------------
EXTENDS Integers
CONSTANT N
ASSUME N \in Nat \ {0}
Procs == 1..N

Not(S) == (S+1)%2

(* Dijkstra's stabilizing token ring 3-state with processes
--algorithm TokenRing {
  variable token = [k \in 0..N |-> (k%3)]; up = [k \in 1..N |-> 0] /\ up[0] = 1; 

   fair process (i \in {0})
    { I0: while (TRUE)
           { 
           }
    }
   fair process (k \in {N})
   {
      K0: while(TRUE)
            {  
            }    
   } 
   fair process (j \in {1..N-1})
    { J0: while (TRUE)
            { 
            }
            {
            }
    }
}
 ****************************************************************)
\* BEGIN TRANSLATION
VARIABLES token, up, pc

vars == << token, up, pc >>

ProcSet == ({0}) \cup ({N}) \cup ({1..N-1})

Init == (* Global variables *)
        /\ token = [k \in 0..N |-> (k%3)]
        /\ up = ([k \in 1..N |-> 0] /\ up[0] = 1)
        /\ pc = [self \in ProcSet |-> CASE self \in {0} -> "I0"
                                        [] self \in {N} -> "K0"
                                        [] self \in {1..N-1} -> "J0"]

I0(self) == /\ pc[self] = "I0"
            /\ token[self] = token[(self+1)] /\ Not(up[(self+1)]) = 0
            /\ token' = [token EXCEPT ![self] = Not(token[self])]
            /\ pc' = [pc EXCEPT ![self] = "I0"]
            /\ up' = up

i(self) == I0(self)

K0(self) == /\ pc[self] = "K0"
            /\ token[self] /= token[(self-1)]
            /\ token' = [token EXCEPT ![self] = token[(self-1)]]
            /\ pc' = [pc EXCEPT ![self] = "K0"]
            /\ up' = up

k(self) == K0(self)

J0(self) == /\ pc[self] = "J0"
            /\ token[self] /= token[(self-1)]
            /\ token' = [token EXCEPT ![self] = token [(self-1)]]
            /\ pc' = [pc EXCEPT ![self] = "J0"]
            /\ up' = up

j(self) == J0(self)

Next == (\E self \in {0}: i(self))
           \/ (\E self \in {N}: k(self))
           \/ (\E self \in {1..N-1}: j(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0} : WF_vars(i(self))
        /\ \A self \in {N} : WF_vars(k(self))
        /\ \A self \in {1..N-1} : WF_vars(j(self))

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Dec 09 17:53:31 EST 2015 by nishantr
\* Created Wed Dec 09 17:42:27 EST 2015 by nishantr

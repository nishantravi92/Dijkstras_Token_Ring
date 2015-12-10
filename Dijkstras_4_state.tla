------------------------- MODULE Djikstras_4_state -------------------------
EXTENDS Integers
CONSTANT N
ASSUME N \in Nat \ {0}
Procs == 1..N

Not(S) == (S+1)%2

(* Dijkstra's stabilizing token ring 4-state with processes
--algorithm TokenRing {
  variable token = [k \in 0..N |-> 0]; up = [k \in 1..N |-> 0] /\ up[0] = 1; 

   fair process (i \in {0})
    { I0: while (TRUE)
           { await token[self] = token[(self+1)] /\ Not(up[(self+1)]) = 0;
             token[self] := Not(token[self]);
           }
    }
   fair process (k \in {N})
   {
      K0: while(TRUE)
            {  await  token[self] /= token[(self-1)];
               token[self] := token[(self-1)]; 
            }    
   } 
   fair process (j \in {1..N-1})
    { J0: while (TRUE)
           either { await token[self] /= token[(self-1)];
              token[self] := token [(self-1)];
              up[self] := 1;
            }
         or { await token[self] = token[(self+1)] /\ up[self] = 1 /\ Not(up[(self+1)]) = 1;
             up[self] := 0;  
            }
    }
}
 ****************************************************************)
\* BEGIN TRANSLATION
VARIABLES token, up

vars == << token, up >>

ProcSet == ({0}) \cup ({N}) \cup ({1..N-1})

Init == (* Global variables *)
        /\ token = [k \in 0..N |-> 0]
        /\ up = ([k \in 1..N |-> 0] /\ up[0] = 1)

i(self) == /\ token[self] = token[(self+1)] /\ Not(up[(self+1)]) = 0
           /\ token' = [token EXCEPT ![self] = Not(token[self])]
           /\ up' = up

k(self) == /\ token[self] /= token[(self-1)]
           /\ token' = [token EXCEPT ![self] = token[(self-1)]]
           /\ up' = up

j(self) == \/ /\ token[self] /= token[(self-1)]
              /\ token' = [token EXCEPT ![self] = token [(self-1)]]
              /\ up' = [up EXCEPT ![self] = 1]
           \/ /\ token[self] = token[(self+1)] /\ up[self] = 1 /\ Not(up[(self+1)]) = 0
              /\ up' = [up EXCEPT ![self] = 0]
              /\ token' = token

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
\* Last modified Thu Dec 10 15:01:06 EST 2015 by nishantr
\* Created Wed Dec 09 17:41:40 EST 2015 by nishantr

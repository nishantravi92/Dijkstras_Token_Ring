------------------------------- MODULE 3state -------------------------------
EXTENDS Integers, FiniteSets
CONSTANT N
ASSUME N \in Nat \ {0}
Procs == 1..N-1

Not(S) == (S+1)%2

(* Dijkstra's stabilizing token ring 4-state with processes
--algorithm TokenRing {
  (*To make c random initialize as !->(K%3) *)
  variable c = [k \in 0..N |-> 0]; 

   fair process (i \in {0})
    { op:c[0] := 1;
      I0: while (TRUE)
           { await (c[self] + 1)%3 = c[(self+1)];
             c[self] := (c[(self+1)]+1)%3;        
           }
    }
   fair process (k \in {N})
   {
      K0: while(TRUE)
          { await c[(self-1)] = c[0] /\ c[self] /= (c[(self-1)]+1)%3;
              c[self] := (c[(self-1)]+1)%3;                   
          }    
   } 
   fair process (j \in Procs)
    { J0: while (TRUE)
           either { await (c[self]+1)%3 = c[(self-1)];
              c[self] := c[(self-1)];
            }
         or { await (c[self]+1)%3 = c[(self+1)];
                c[self] := c[(self+1)];  
            }
    }
}
 ****************************************************************)
\* BEGIN TRANSLATION
VARIABLES c, pc

vars == << c, pc >>

ProcSet == ({0}) \cup ({N}) \cup (Procs)

Init == (* Global variables *)
        /\ c = [k \in 0..N |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in {0} -> "op"
                                        [] self \in {N} -> "K0"
                                        [] self \in Procs -> "J0"]

op(self) == /\ pc[self] = "op"
            /\ c' = [c EXCEPT ![0] = 1]
            /\ pc' = [pc EXCEPT ![self] = "I0"]

I0(self) == /\ pc[self] = "I0"
            /\ (c[self] + 1)%3 = c[(self+1)]
            /\ c' = [c EXCEPT ![self] = (c[(self+1)]+1)%3]
            /\ pc' = [pc EXCEPT ![self] = "I0"]

i(self) == op(self) \/ I0(self)

K0(self) == /\ pc[self] = "K0"
            /\ c[(self-1)] = c[0] /\ c[self] /= (c[(self-1)]+1)%3
            /\ c' = [c EXCEPT ![self] = (c[(self-1)]+1)%3]
            /\ pc' = [pc EXCEPT ![self] = "K0"]

k(self) == K0(self)

J0(self) == /\ pc[self] = "J0"
            /\ \/ /\ (c[self]+1)%3 = c[(self-1)]
                  /\ c' = [c EXCEPT ![self] = c[(self-1)]]
               \/ /\ (c[self]+1)%3 = c[(self+1)]
                  /\ c' = [c EXCEPT ![self] = c[(self+1)]]
            /\ pc' = [pc EXCEPT ![self] = "J0"]

j(self) == J0(self)

Next == (\E self \in {0}: i(self))
           \/ (\E self \in {N}: k(self))
           \/ (\E self \in Procs: j(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {0} : WF_vars(i(self))
        /\ \A self \in {N} : WF_vars(k(self))
        /\ \A self \in Procs : WF_vars(j(self))

\* END TRANSLATION

Tokens == Cardinality({s \in Procs: (c[s]+1)%3 = c[(s-1)] \/ (c[s]+1)%3 = c[(s+1)]}) + 
          Cardinality({t \in {N}: c[(t-1)] = c[0] /\ c[t] /= (c[(t-1)]+1)%3}) +
          Cardinality({w \in {0}: (c[w] + 1)%3 = c[(w+1)]})
TypeOK == \A s \in 0..N : c[s] < 3
Stabilization == <>TypeOK 
NotIncrease == [][Tokens' <= Tokens]_vars
Decrease == \A p \in 1..N+1:[] <> (Tokens <= p)
LowerBound == Tokens = 1
(*There can be cases where there are 2 tokens in the system due to token at process N.
  Hence there will be different conditions as stipulated by Dijkstra in his conference
  papers which he proved mathematically. *)  

=============================================================================
\* Modification History
\* Last modified Fri Dec 11 23:59:24 EST 2015 by nishantr
\* Created Wed Dec 09 17:42:27 EST 2015 by nishantr

=============================================================================
\* Modification History
\* Created Fri Dec 11 23:59:12 EST 2015 by nishantr

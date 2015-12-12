------------------------------- MODULE 4state -------------------------------
EXTENDS Integers, FiniteSets
CONSTANT N
ASSUME N \in Nat \ {0}
Procs == 1..N-1
\*RECURSIVE Cardinality(_)
\*Cardinality(S) == IF S={} THEN 0 ELSE 1+Cardinality(S \ {CHOOSE x\in S : TRUE})
Not(S) == (S+1)%2

(* Dijkstra's stabilizing token ring 4-state with processes
--algorithm TokenRing {
(*To make c random initialize as !->(K%2) *)
  variable c = [k \in 0..N |-> 0]; up = [k \in 0..N |-> 0]; 
  
   fair process (i \in {0})
    { op:up[0] := 1;
    I0: while (TRUE)
           { await (c[self] = c[(self+1)] /\ up[(self+1)] = 0);
             c[self] := Not(c[self]);
           }
    }
   fair process (k \in {N})
   { op2: up[N] := 0;
      K0: while(TRUE)
            {  await  (c[self] # c[(self-1)]);
               c[self] := c[(self-1)]; 
            }    
   } 
   fair process (j \in Procs)
    { J0: while (TRUE)
           either { await (c[self] # c[(self-1)]);
              c[self] := c [(self-1)];
              up[self] := 1;
            }
         or { await (c[self] = c[(self+1)] /\ up[self] = 1 /\ up[(self+1)] = 0);
             up[self] := 0;  
            }
    }
}
 ****************************************************************)
\* BEGIN TRANSLATION
VARIABLES c, up, pc

vars == << c, up, pc >>

ProcSet == ({0}) \cup ({N}) \cup (Procs)

Init == (* Global variables *)
        /\ c = [k \in 0..N |-> 0]
        /\ up = [k \in 0..N |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in {0} -> "op"
                                        [] self \in {N} -> "op2"
                                        [] self \in Procs -> "J0"]

op(self) == /\ pc[self] = "op"
            /\ up' = [up EXCEPT ![0] = 1]
            /\ pc' = [pc EXCEPT ![self] = "I0"]
            /\ c' = c

I0(self) == /\ pc[self] = "I0"
            /\ (c[self] = c[(self+1)] /\ up[(self+1)] = 0)
            /\ c' = [c EXCEPT ![self] = Not(c[self])]
            /\ pc' = [pc EXCEPT ![self] = "I0"]
            /\ up' = up

i(self) == op(self) \/ I0(self)

op2(self) == /\ pc[self] = "op2"
             /\ up' = [up EXCEPT ![N] = 0]
             /\ pc' = [pc EXCEPT ![self] = "K0"]
             /\ c' = c

K0(self) == /\ pc[self] = "K0"
            /\ (c[self] # c[(self-1)])
            /\ c' = [c EXCEPT ![self] = c[(self-1)]]
            /\ pc' = [pc EXCEPT ![self] = "K0"]
            /\ up' = up

k(self) == op2(self) \/ K0(self)

J0(self) == /\ pc[self] = "J0"
            /\ \/ /\ (c[self] # c[(self-1)])
                  /\ c' = [c EXCEPT ![self] = c [(self-1)]]
                  /\ up' = [up EXCEPT ![self] = 1]
               \/ /\ (c[self] = c[(self+1)] /\ up[self] = 1 /\ up[(self+1)] = 0)
                  /\ up' = [up EXCEPT ![self] = 0]
                  /\ c' = c
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

Tokens == Cardinality({s \in Procs:c[s] /= c[(s-1)] \/ (c[s] = c[(s+1)] /\ up[s] = 1 /\ up[(s+1)] = 0)}) + 
          Cardinality({t \in {N}: c[t] /= c[(t-1)]}) +
          Cardinality({w \in {0}: c[w] = c[(w+1)] /\ up[(w+1)] = 0})
TypeOK == \A s \in 0..N : c[s] < 2 /\ up[s] < 2
Stabilization == <>TypeOK 
NotIncrease == [][Tokens' <= Tokens]_vars
Decrease == \A p \in 1..N+1:[] <> (Tokens <= p)
LowerBound == Tokens = 1   

=============================================================================
\* Modification History
\* Last modified Fri Dec 11 23:56:46 EST 2015 by nishantr
\* Created Wed Dec 09 17:41:40 EST 2015 by nishantr

=============================================================================
\* Modification History
\* Created Fri Dec 11 23:56:16 EST 2015 by nishantr

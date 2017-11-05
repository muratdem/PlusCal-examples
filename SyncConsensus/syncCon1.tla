--------------------- MODULE syncCon1 -----------------------------
(****************************************************************)
(* Synchronized consensus *)
(***************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS N, FAILNUM
ASSUME N=<5 /\ 0=<FAILNUM /\ FAILNUM=<2
Nodes == 1..N

(* 
--algorithm syncCon1
{variable FailNum=FAILNUM, \* Initialization block
         up=[n \in Nodes |-> TRUE]; \* nodes are up
         pt=[n \in Nodes |-> 0];  \* nodes are at round 0
         t=[n \in Nodes |-> FALSE]; \* nodes are not terminated  
         d=[n \in Nodes |-> -1]; \* nodes are not decided           
         mb=[n \in Nodes |-> {}]; \* nodes have mailbox as emptyset

  define{
  SetMin(S) == CHOOSE i \in S : \A j \in S : i =< j
  } 

  macro MaybeFail() {
      if (FailNum>0 /\ up[self]) 
         {either 
           {up[self]:=FALSE; FailNum:=FailNum-1;} \* Node may fail 
          or skip; }; \* or not
  }

  fair process (n \in Nodes)
  variable v=0, pv=0, Q={};  
  {
P: if (up[self]){
     v:=self; \* value is set to your id
     Q:=Nodes;
PS:  while (up[self] /\ Q # {}){ \* send vote to mb[p] one by one; this node can fail in between
         with (p \in Q) {
           mb[p]:= mb[p] \union {v}; \* skip for attacking generals impossibility
           Q:= Q \ {p};
           MaybeFail();
         };               
      };\* end_while
      if (up[self]) pt[self]:= pt[self]+1; \* move to next round
PR:   await (up[self] /\ (\A k \in Nodes: up[k] => pt[k]=pt[self])); \* wait for others to move
      d[self]:=SetMin(mb[self]);
      t[self]:=TRUE;
   }; \* end_if  
 }\* process
}
\* PR label critical for nonblocking;
\* Remove up in PR label, to show the FLP result with asynchronous rounds!
*)
\* BEGIN TRANSLATION
VARIABLES FailNum, up, pt, t, d, mb, pc

(* define statement *)
SetMin(S) == CHOOSE i \in S : \A j \in S : i =< j

VARIABLES v, pv, Q

vars == << FailNum, up, pt, t, d, mb, pc, v, pv, Q >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ up = [n \in Nodes |-> TRUE]
        /\ pt = [n \in Nodes |-> 0]
        /\ t = [n \in Nodes |-> FALSE]
        /\ d = [n \in Nodes |-> -1]
        /\ mb = [n \in Nodes |-> {}]
        (* Process n *)
        /\ v = [self \in Nodes |-> 0]
        /\ pv = [self \in Nodes |-> 0]
        /\ Q = [self \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ IF up[self]
                 THEN /\ v' = [v EXCEPT ![self] = self]
                      /\ Q' = [Q EXCEPT ![self] = Nodes]
                      /\ pc' = [pc EXCEPT ![self] = "PS"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << v, Q >>
           /\ UNCHANGED << FailNum, up, pt, t, d, mb, pv >>

PS(self) == /\ pc[self] = "PS"
            /\ IF up[self] /\ Q[self] # {}
                  THEN /\ \E p \in Q[self]:
                            /\ mb' = [mb EXCEPT ![p] = mb[p] \union {v[self]}]
                            /\ Q' = [Q EXCEPT ![self] = Q[self] \ {p}]
                            /\ IF FailNum>0 /\ up[self]
                                  THEN /\ \/ /\ up' = [up EXCEPT ![self] = FALSE]
                                             /\ FailNum' = FailNum-1
                                          \/ /\ TRUE
                                             /\ UNCHANGED <<FailNum, up>>
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << FailNum, up >>
                       /\ pc' = [pc EXCEPT ![self] = "PS"]
                       /\ pt' = pt
                  ELSE /\ IF up[self]
                             THEN /\ pt' = [pt EXCEPT ![self] = pt[self]+1]
                             ELSE /\ TRUE
                                  /\ pt' = pt
                       /\ pc' = [pc EXCEPT ![self] = "PR"]
                       /\ UNCHANGED << FailNum, up, mb, Q >>
            /\ UNCHANGED << t, d, v, pv >>

PR(self) == /\ pc[self] = "PR"
            /\ (up[self] /\ (\A k \in Nodes: up[k] => pt[k]=pt[self]))
            /\ d' = [d EXCEPT ![self] = SetMin(mb[self])]
            /\ t' = [t EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << FailNum, up, pt, mb, v, pv, Q >>

n(self) == P(self) \/ PS(self) \/ PR(self)

Next == (\E self \in Nodes: n(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(n(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Agreement == \A i,j \in Nodes: t[i] /\ t[j] => (d[i]=d[j] /\ d[i]#-1)
Term == <> \A i \in Nodes: up[i] =>t[i]
\* Remember == [] [ (\A j \in Nodes: v'[p]>=v[p]) ]_vars
======================================================================
Agreement. Two correct processes can not commit to different decision variables.
(∀i,j:ti ∧tj :di =dj)
Validity (Nontriviality). If all initial values are equal, correct processes must decide on that value.
(∃k ::(∀i ::vi =k)) ⇒ (∀i :ti :di =vi)
Termination. The system eventually terminates. true   (∀i :: ti)

Synchronous consensus
Every process broadcasts (to all other processes, including itself) its initial value vi. In a synchronous network, this can be done in a single "round" of messages. After this round, each process decides on the minimum value it received.
If no faults occur, this algorithm is correct. In the presence of a crash fault, however, a problem can arise. In particular, a problem may occur if a process crashes during a round. When this happens, some processes may have received its (low) initial value, but others may not have.

To address this concern, consider this simplifying assumption: say that at most 1 process can crash. How can we modify the algorithm to handle such a failure?
Answer: by using 2 rounds. In 1st round, processes broadcast their own initial value. In 2nd round, processes broadcast the minimum value they heard. Each process then decides on the min value among all the sets of values it received in 2nd round.
If the one crash occurs during the first round, the second round ensures that all processes have the same set of values from which to decide. Else, if the one crash occurs during the second round, the first round must have completed without a crash and hence all processes have the same set of values from which to decide.

The key observation is that if no crash occurs during a round, all processes have the same set of values from which to decide and they correctly decide on the same minimum value.
Thus, to tolerate multiple crashes, say f , the protocol is modified to have f + 1 rounds of synchronous communication. Of course, this requires knowing f , an upper bound on the number of possible crash faults.

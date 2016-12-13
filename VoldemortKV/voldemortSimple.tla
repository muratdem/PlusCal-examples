--------------------- MODULE voldemortSimple -----------------------------
(****************************************************************)
(* Replicated storage protocol with clientside routing *)
(***************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS N, C, STOP, ReadQ, WriteQ, FAILNUM
ASSUME N=5 /\ C=1 /\ STOP<10 /\ 1<=ReadQ /\ ReadQ<=3 
       /\ 1<=WriteQ /\ WriteQ<=3 /\ 0<=FAILNUM /\ FAILNUM<=2
Nodes == 1..N
Clients== N+1..N+C \* \* should give different ID space to Client


(* 
--algorithm voldemort
{
  variable FailNum=FAILNUM,
           up=[n \in Nodes |-> TRUE], \*\*Initially all nodes are up  
           db=[n \in Nodes |-> {[ver|->0, val|->0]}]; 
          \*\* All nodes have database, wherein [ver=0, val=0] stored for the item

  define
  {
   SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j
   SetofVers(S) == {p.ver : p \in S}
   ReturnDBs(S) == {db[k] : k \in S}	
   UpNodes == {n \in Nodes : up[n]=TRUE}
   ReturnReadQ == CHOOSE i \in SUBSET(UpNodes): Cardinality(i)=ReadQ 
   ReturnWriteQ == CHOOSE i \in SUBSET(UpNodes): Cardinality(i)=WriteQ 
   \*\* CHOOSE deterministically returns lowest ID nodes that satisfy the requirement
  }

  fair process (c \in Clients)
  variable cntr=0, hver=0, Q={};
  {
   CL: while(cntr<=STOP){
          cntr:=cntr+1;
        \*\* get the highest version number from read Quorum
          hver:=SetMax(SetofVers(UNION ReturnDBs(ReturnReadQ)));               
        \*\* write val=cntr to writeQuorum with higher version number
    CLWR: Q:=ReturnWriteQ;
    CLWW: while (Q # {}){
            with (p \in Q) {
              db[p]:=db[p] \union {[ver|->hver+1,val|->cntr]};
              Q:= Q \ {p};
            } 
          } 
        }
  }



  fair process (n \in Nodes)
  {
  NODE: while (TRUE){  
          if (FailNum>0 /\ up[self]=TRUE){ \*\* Storage node can fail 
            up[self]:=FALSE; 
            FailNum:=FailNum-1;}
          else if (up[self]=FALSE){ \* \* Or recover
            up[self]:=TRUE;
            FailNum:=FailNum+1;}
        }
  }

}

*)
\* BEGIN TRANSLATION
VARIABLES FailNum, up, db, pc

(* define statement *)
SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j
SetofVers(S) == {p.ver : p \in S}
ReturnDBs(S) == {db[k] : k \in S}
UpNodes == {n \in Nodes : up[n]=TRUE}
ReturnReadQ == CHOOSE i \in SUBSET(UpNodes): Cardinality(i)=ReadQ
ReturnWriteQ == CHOOSE i \in SUBSET(UpNodes): Cardinality(i)=WriteQ

VARIABLES cntr, hver, Q

vars == << FailNum, up, db, pc, cntr, hver, Q >>

ProcSet == (Clients) \cup (Nodes)

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ up = [n \in Nodes |-> TRUE]
        /\ db = [n \in Nodes |-> {[ver|->0, val|->0]}]
        (* Process c *)
        /\ cntr = [self \in Clients |-> 0]
        /\ hver = [self \in Clients |-> 0]
        /\ Q = [self \in Clients |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "CL"
                                        [] self \in Nodes -> "NODE"]

CL(self) == /\ pc[self] = "CL"
            /\ IF cntr[self]<=STOP
                  THEN /\ cntr' = [cntr EXCEPT ![self] = cntr[self]+1]
                       /\ hver' = [hver EXCEPT ![self] = SetMax(SetofVers(UNION ReturnDBs(ReturnReadQ)))]
                       /\ pc' = [pc EXCEPT ![self] = "CLWR"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << cntr, hver >>
            /\ UNCHANGED << FailNum, up, db, Q >>

CLWR(self) == /\ pc[self] = "CLWR"
              /\ Q' = [Q EXCEPT ![self] = ReturnWriteQ]
              /\ pc' = [pc EXCEPT ![self] = "CLWW"]
              /\ UNCHANGED << FailNum, up, db, cntr, hver >>

CLWW(self) == /\ pc[self] = "CLWW"
              /\ IF Q[self] # {}
                    THEN /\ \E p \in Q[self]:
                              /\ db' = [db EXCEPT ![p] = db[p] \union {[ver|->hver[self]+1,val|->cntr[self]]}]
                              /\ Q' = [Q EXCEPT ![self] = Q[self] \ {p}]
                         /\ pc' = [pc EXCEPT ![self] = "CLWW"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "CL"]
                         /\ UNCHANGED << db, Q >>
              /\ UNCHANGED << FailNum, up, cntr, hver >>

c(self) == CL(self) \/ CLWR(self) \/ CLWW(self)

NODE(self) == /\ pc[self] = "NODE"
              /\ IF FailNum>0 /\ up[self]=TRUE
                    THEN /\ up' = [up EXCEPT ![self] = FALSE]
                         /\ FailNum' = FailNum-1
                    ELSE /\ IF up[self]=FALSE
                               THEN /\ up' = [up EXCEPT ![self] = TRUE]
                                    /\ FailNum' = FailNum+1
                               ELSE /\ TRUE
                                    /\ UNCHANGED << FailNum, up >>
              /\ pc' = [pc EXCEPT ![self] = "NODE"]
              /\ UNCHANGED << db, cntr, hver, Q >>

n(self) == NODE(self)

Next == (\E self \in Clients: c(self))
           \/ (\E self \in Nodes: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(c(self))
        /\ \A self \in Nodes : WF_vars(n(self))

\* END TRANSLATION

\* invariant for all nodes, the ver and val should match. if there is consistency however, val > ver can happen. 
\* Because the client read an old ver, and cntr is incrementing as usual and ver becomes lower than cntr=val.

Consistent == \A p \in Nodes: \A m \in db[p]: m.ver=m.val
CPro == [] [ (\A j \in Clients: hver'[j]>=hver[j]) ]_vars
\*\* It is possible to write alternative Consistent properties,
\*\* this one is shortcut leveraging the way the client stores items to the storage system.
======================================================================
\* Created Wed, 12 Oct 16 - - - 13:49 by Murat

For the "Consistent" property to hold as invariant, the following should hold:
FAILNUM < ReadQ /\ FAILNUM < WriteQ 

If ~(FAILNUM < WriteQ) then all the WriteQ nodes (where the new version has been
written) can fail, and the ReadQ will read the old version, and the next write will violate "Consistent".

If ~(FAILNUM < ReadQ) then all the ReadQ nodes can fail, new version will be written to WriteQ, a separate set of nodes then the previous ReadQ. Then when the failed nodes are recovered again, when version is read from ReadQ, the new version will not be seen (because WriteQ does not intersect with ReadQ), and the next write will violate "Consistent". 




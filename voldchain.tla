--------------------- MODULE voldchain -----------------------------
(****************************************************************)
(* Chain replicated storage protocol. Serverside routing *)
(***************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS N, C, STOP, FAILNUM
ASSUME N-FAILNUM>=1 /\ STOP<5 /\ 0<=FAILNUM /\ FAILNUM<=2
Nodes == 1..N
Clients== N+1..N+C \*\* should give different ID space to Client
Procs == 1..N+C
Configurator== N+C+1 \*\* Configurator is unfallable 

(* 
--algorithm voldchain
{
  variable FailNum=FAILNUM,
        up=[n \in Nodes |-> TRUE], \*\* Initially all nodes are up
        msg= [j \in Procs |-> <<>>], \*\* Each process has an inbox
        db= \*\* db is single record only
	      [n \in Nodes |-> [ver|->-1, val|->-1, cli|->-1]]; 
        chain= <<>>; \*\* chain is a sequence, initially empty

  define
  {IsUp(e) == up[e]
   UpNodes == {n \in Nodes : up[n]=TRUE}
   InChain(s) == ~(chain \in Seq(Nodes\{s})) \*\* is s in the chain?
   ChainNodes == {n \in Nodes: InChain(n)=TRUE}   	      
   FreeUpNode == CHOOSE i \in UpNodes: ~InChain(i)
   GetIndex(s) == \*\* Assumes InChain(s), returns index of s in chain
     IF s=chain[1] THEN 1 ELSE IF s=chain[2] THEN 2 ELSE 3
   GetNext(s) == \*\* Assumes InChain(s), returns successor of s in chain
     IF GetIndex(s)=Len(chain) THEN s ELSE chain[GetIndex(s)+1]
  }

  
  fair process (c \in Clients) \*\* Client process
  variable cntr=0, hver=-1;
  {
   C0:await(Len(chain)>0);  \*\* start requests only after chain is constructed
   CL:while(cntr<=STOP){
CLR:    while(msg[self]= <<>>)  \*\* read hver from tail, retry until get a msg back
          msg[chain[Len(chain)]]:=[ver|->hver, val|->-1, cli|->self]; \*\*val=-1 == "read"
        hver:=msg[self].ver+1;
        msg[self]:= <<>>; 
        \*\* write val=cntr to head with higher version number
CLW:    while (msg[self]= <<>> \/ ~(msg[self].ver=hver /\ msg[self].cli=self)) \*\* head may be down or update lost, retry until get ack msg back
          msg[chain[1]]:= [ver|->hver, val|->cntr, cli|->self]; 
        cntr:=cntr+1;
        msg[self]:=<<>>;  
     }
 }

  fair process (n \in Nodes) \*\* Storage node
  {
  ND: while (TRUE){
      either
      NM:{\*\* react to message
          await(msg[self]# <<>> /\ up[self] /\ InChain(self));
	      if (msg[self].val#-1) \*\* val=-1 =="read" msg, "read" msg should not update db 
	        db[self]:=msg[self];
	      if (self=chain[Len(chain)]){ \*\* if tail
	        msg[msg[self].cli]:= db[self];} \*\* read and update respond is same= db of tail
	      else msg[GetNext(self)]:=msg[self]; \*\* Propagate msg to next node in chain
	  NEM:msg[self]:= <<>>; \*\* consume msg
      }or
     NDF:{
          if (FailNum>0 /\ up[self]=TRUE){ \*\* Storage node can fail, db & cnext & update reset
            up[self]:=FALSE;
            FailNum:=FailNum-1;}
          else if (up[self]=FALSE){ \*\* Or recover as new node
            up[self]:=TRUE;
            msg[self]:= <<>>;
            FailNum:=FailNum+1;}
         }
    }    
  }

  fair process (p=Configurator) \*\* Maintain the chain
  {
  P: while (TRUE){
       if (Len(chain)<3 /\ (UpNodes \ ChainNodes #{}) ){ \*\* add an up node to tail of chain, cp db from pred if any
       	  chain:= chain \o <<FreeUpNode>>;
	      if(Len(chain)>1) 
                db[chain[Len(chain)]]:=db[chain[Len(chain)-1]];} 
       else \*\* filter chain with IsUp to remove the downed chain nodes
	    chain:=SelectSeq(chain,IsUp);
    }
  }  

}

*)
\* BEGIN TRANSLATION
VARIABLES FailNum, up, msg, db, chain, pc

(* define statement *)
IsUp(e) == up[e]
UpNodes == {n \in Nodes : up[n]=TRUE}
InChain(s) == ~(chain \in Seq(Nodes\{s}))
ChainNodes == {n \in Nodes: InChain(n)=TRUE}
FreeUpNode == CHOOSE i \in UpNodes: ~InChain(i)
GetIndex(s) ==
  IF s=chain[1] THEN 1 ELSE IF s=chain[2] THEN 2 ELSE 3
GetNext(s) ==
  IF GetIndex(s)=Len(chain) THEN s ELSE chain[GetIndex(s)+1]

VARIABLES cntr, hver

vars == << FailNum, up, msg, db, chain, pc, cntr, hver >>

ProcSet == (Clients) \cup (Nodes) \cup {Configurator}

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ up = [n \in Nodes |-> TRUE]
        /\ msg = [j \in Procs |-> <<>>]
        /\ db = [n \in Nodes |-> [ver|->-1, val|->-1, cli|->-1]]
        /\ chain = <<>>
        (* Process c *)
        /\ cntr = [self \in Clients |-> 0]
        /\ hver = [self \in Clients |-> -1]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "C0"
                                        [] self \in Nodes -> "ND"
                                        [] self = Configurator -> "P"]

C0(self) == /\ pc[self] = "C0"
            /\ (Len(chain)>0)
            /\ pc' = [pc EXCEPT ![self] = "CL"]
            /\ UNCHANGED << FailNum, up, msg, db, chain, cntr, hver >>

CL(self) == /\ pc[self] = "CL"
            /\ IF cntr[self]<=STOP
                  THEN /\ pc' = [pc EXCEPT ![self] = "CLR"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << FailNum, up, msg, db, chain, cntr, hver >>

CLR(self) == /\ pc[self] = "CLR"
             /\ IF msg[self]= <<>>
                   THEN /\ msg' = [msg EXCEPT ![chain[Len(chain)]] = [ver|->hver[self], val|->-1, cli|->self]]
                        /\ pc' = [pc EXCEPT ![self] = "CLR"]
                        /\ hver' = hver
                   ELSE /\ hver' = [hver EXCEPT ![self] = msg[self].ver+1]
                        /\ msg' = [msg EXCEPT ![self] = <<>>]
                        /\ pc' = [pc EXCEPT ![self] = "CLW"]
             /\ UNCHANGED << FailNum, up, db, chain, cntr >>

CLW(self) == /\ pc[self] = "CLW"
             /\ IF msg[self]= <<>> \/ ~(msg[self].ver=hver[self] /\ msg[self].cli=self)
                   THEN /\ msg' = [msg EXCEPT ![chain[1]] = [ver|->hver[self], val|->cntr[self], cli|->self]]
                        /\ pc' = [pc EXCEPT ![self] = "CLW"]
                        /\ cntr' = cntr
                   ELSE /\ cntr' = [cntr EXCEPT ![self] = cntr[self]+1]
                        /\ msg' = [msg EXCEPT ![self] = <<>>]
                        /\ pc' = [pc EXCEPT ![self] = "CL"]
             /\ UNCHANGED << FailNum, up, db, chain, hver >>

c(self) == C0(self) \/ CL(self) \/ CLR(self) \/ CLW(self)

ND(self) == /\ pc[self] = "ND"
            /\ \/ /\ pc' = [pc EXCEPT ![self] = "NM"]
               \/ /\ pc' = [pc EXCEPT ![self] = "NDF"]
            /\ UNCHANGED << FailNum, up, msg, db, chain, cntr, hver >>

NM(self) == /\ pc[self] = "NM"
            /\ (msg[self]# <<>> /\ up[self] /\ InChain(self))
            /\ IF msg[self].val#-1
                  THEN /\ db' = [db EXCEPT ![self] = msg[self]]
                  ELSE /\ TRUE
                       /\ db' = db
            /\ IF self=chain[Len(chain)]
                  THEN /\ msg' = [msg EXCEPT ![msg[self].cli] = db'[self]]
                  ELSE /\ msg' = [msg EXCEPT ![GetNext(self)] = msg[self]]
            /\ pc' = [pc EXCEPT ![self] = "NEM"]
            /\ UNCHANGED << FailNum, up, chain, cntr, hver >>

NEM(self) == /\ pc[self] = "NEM"
             /\ msg' = [msg EXCEPT ![self] = <<>>]
             /\ pc' = [pc EXCEPT ![self] = "ND"]
             /\ UNCHANGED << FailNum, up, db, chain, cntr, hver >>

NDF(self) == /\ pc[self] = "NDF"
             /\ IF FailNum>0 /\ up[self]=TRUE
                   THEN /\ up' = [up EXCEPT ![self] = FALSE]
                        /\ FailNum' = FailNum-1
                        /\ msg' = msg
                   ELSE /\ IF up[self]=FALSE
                              THEN /\ up' = [up EXCEPT ![self] = TRUE]
                                   /\ msg' = [msg EXCEPT ![self] = <<>>]
                                   /\ FailNum' = FailNum+1
                              ELSE /\ TRUE
                                   /\ UNCHANGED << FailNum, up, msg >>
             /\ pc' = [pc EXCEPT ![self] = "ND"]
             /\ UNCHANGED << db, chain, cntr, hver >>

n(self) == ND(self) \/ NM(self) \/ NEM(self) \/ NDF(self)

P == /\ pc[Configurator] = "P"
     /\ IF Len(chain)<3 /\ (UpNodes \ ChainNodes #{})
           THEN /\ chain' = chain \o <<FreeUpNode>>
                /\ IF Len(chain')>1
                      THEN /\ db' = [db EXCEPT ![chain'[Len(chain')]] = db[chain'[Len(chain')-1]]]
                      ELSE /\ TRUE
                           /\ db' = db
           ELSE /\ chain' = SelectSeq(chain,IsUp)
                /\ db' = db
     /\ pc' = [pc EXCEPT ![Configurator] = "P"]
     /\ UNCHANGED << FailNum, up, msg, cntr, hver >>

p == P

Next == p
           \/ (\E self \in Clients: c(self))
           \/ (\E self \in Nodes: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(c(self))
        /\ \A self \in Nodes : WF_vars(n(self))
        /\ WF_vars(p)

\* END TRANSLATION

\* invariant for all nodes, the ver and val should match. if there is consistency however, val > ver can happen. 
\* Because the client read an old ver, and cntr is incrementing as usual and ver becomes lower than cntr=val.

Consistent == \A j \in Nodes: db[j].ver=db[j].val
CCon == \A j,k \in ChainNodes: GetIndex(j)<GetIndex(k) => db[j].ver>=db[k].ver
CPro == [][\A j \in Clients: hver[j] =< hver'[j]]_vars
======================================================================
Model checking runtimes

N=5 Failnum=0 instant.
N=5 Failnum=1 >1.5 hours at 51 diameters, 4GB

After setting N=3, FAILNUM=1, model checking:
done in 2 minutes, reached diameter 119.

N=3, FailNum=2, done in 6 minutes


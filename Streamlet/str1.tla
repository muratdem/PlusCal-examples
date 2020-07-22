------------- MODULE str1 --------------------
(*\* Crash fault-tolerant streamlet algorithm *)
EXTENDS Integers, Sequences, FiniteSets
CONSTANT N, EMAX
Nodes == 0..N-1

(* 
--algorithm str1 {
variable Msgs={[chain|-> <<0>>, epoch|->0, sender|->0],
               [chain|-> <<0>>, epoch|->0, sender|->1],
               [chain|-> <<0>>, epoch|->0, sender|->2]
               };

define{
ExtractMsg(e) == CHOOSE m \in Msgs: m.epoch=e
FindMaxChain == CHOOSE z \in {m.chain: m \in Msgs}:
             ~(\E x \in {m.chain: m \in Msgs}: Len(x)>Len(z))
ThreeCons(c) == Len(c)>2 /\ Head(c)= Head(Tail(c))+1 /\ Head(Tail(c))=Head(Tail(Tail(c)))+1                         
}

\*\* What to do with two chains with length=l
\*\* FindMaxChain returns c1, which is not notarized.
\*\* we chop off head and return it, but c2 with length l was notarized.
macro FindMaxNotarizedChain(e) {
   if (2*Cardinality ({m\in Msgs: m.epoch=e /\ m.chain=FindMaxChain}) > N)
      nChain:= FindMaxChain;
   else 
      nChain:= Tail(FindMaxChain); 
}

macro Propose (e) {
   FindMaxNotarizedChain(e-1); \* \* updates nChain
   Msgs:= Msgs \union {[chain|-> <<e>> \o nChain, epoch|->e, sender|->self]}; 
}

macro Vote (e){
   await (\E m \in Msgs: m.epoch=e);
   FindMaxNotarizedChain(e); \* \* updates nChain 
   if (Len(ExtractMsg(e).chain) = Len(nChain)+1)
      Msgs:= Msgs \union {[chain|->ExtractMsg(e).chain, epoch|->e, sender|->self]};
}

fair process (p \in Nodes)
   variable nChain= <<>>, ep=1;{
A: while (ep<EMAX) {
      if (ep%N=self)  Propose(ep)
      else Vote(ep);
      ep:=ep+1;
   }
} 

} \* \* end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES Msgs, pc

(* define statement *)
ExtractMsg(e) == CHOOSE m \in Msgs: m.epoch=e
FindMaxChain == CHOOSE z \in {m.chain: m \in Msgs}:
             ~(\E x \in {m.chain: m \in Msgs}: Len(x)>Len(z))
ThreeCons(c) == Len(c)>2 /\ Head(c)= Head(Tail(c))+1 /\ Head(Tail(c))=Head(Tail(Tail(c)))+1

VARIABLES nChain, ep

vars == << Msgs, pc, nChain, ep >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ Msgs = {[chain|-> <<0>>, epoch|->0, sender|->0],
                   [chain|-> <<0>>, epoch|->0, sender|->1],
                   [chain|-> <<0>>, epoch|->0, sender|->2]
                   }
        (* Process p *)
        /\ nChain = [self \in Nodes |-> <<>>]
        /\ ep = [self \in Nodes |-> 1]
        /\ pc = [self \in ProcSet |-> "A"]

A(self) == /\ pc[self] = "A"
           /\ IF ep[self]<EMAX
                 THEN /\ IF ep[self]%N=self
                            THEN /\ IF 2*Cardinality ({m\in Msgs: m.epoch=(ep[self]-1) /\ m.chain=FindMaxChain}) > N
                                       THEN /\ nChain' = [nChain EXCEPT ![self] = FindMaxChain]
                                       ELSE /\ nChain' = [nChain EXCEPT ![self] = Tail(FindMaxChain)]
                                 /\ Msgs' = (Msgs \union {[chain|-> <<ep[self]>> \o nChain'[self], epoch|->ep[self], sender|->self]})
                            ELSE /\ (\E m \in Msgs: m.epoch=ep[self])
                                 /\ IF 2*Cardinality ({m\in Msgs: m.epoch=ep[self] /\ m.chain=FindMaxChain}) > N
                                       THEN /\ nChain' = [nChain EXCEPT ![self] = FindMaxChain]
                                       ELSE /\ nChain' = [nChain EXCEPT ![self] = Tail(FindMaxChain)]
                                 /\ IF Len(ExtractMsg(ep[self]).chain) = Len(nChain'[self])+1
                                       THEN /\ Msgs' = (Msgs \union {[chain|->ExtractMsg(ep[self]).chain, epoch|->ep[self], sender|->self]})
                                       ELSE /\ TRUE
                                            /\ Msgs' = Msgs
                      /\ ep' = [ep EXCEPT ![self] = ep[self]+1]
                      /\ pc' = [pc EXCEPT ![self] = "A"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << Msgs, nChain, ep >>

p(self) == A(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


---------------------------------------------------------
\* Invariants

\* Check three finality rule!!
Consistency == \A i,j \in Nodes: ThreeCons(nChain[i]) /\ ThreeCons(nChain[j]) /\ Len(nChain[i])=< Len(nChain[j]) 
                                 => \A k \in 1..Len(nChain[i]): nChain[i][k]=nChain[j][Len(nChain[j])-Len(nChain[i])+k]
Bait2 == ~( \E i \in Nodes: Len(nChain[i])>1 /\ Head(nChain[i])= Head(Tail(nChain[i]))+1 )
Bait3 == ~( \E i \in Nodes: Len(nChain[i])>2 /\ Head(nChain[i])= Head(Tail(nChain[i]))+1 
            /\ Head(Tail(nChain[i]))=Head(Tail(Tail(nChain[i])))+1 )
BaitLength == \A i \in Nodes: Len (nChain[i]) <EMAX
BaitWidth ==  \A e \in 1..EMAX : Cardinality({m \in Msgs: m.epoch=e}) < 2
BaitSet == Cardinality(Msgs) <9
=========================================================

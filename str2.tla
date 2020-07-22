------------- MODULE str2 --------------------
(*\* Crash fault-tolerant streamlet algorithm *)
EXTENDS Integers, Sequences, FiniteSets
CONSTANT N, EMAX
Nodes == 0..N-1

(* 
--algorithm str2 {
variable Msgs=[n \in Nodes |-> {[chain|-> <<0>>, epoch|->0, sender|->0],
                                [chain|-> <<0>>, epoch|->0, sender|->1],
                                [chain|-> <<0>>, epoch|->0, sender|->2]}];

define{
ExtractMsg(e,s) == CHOOSE m \in Msgs[s]: m.epoch=e
FindMaxChain(s) == CHOOSE z \in {m.chain: m \in Msgs[s]}:
             ~(\E x \in {m.chain: m \in Msgs[s]}: Len(x)>Len(z))
ThreeCons(c) == Len(c)>2 /\ Head(c)= Head(Tail(c))+1 /\ Head(Tail(c))=Head(Tail(Tail(c)))+1                         
}

\*\* What to do with two chains with length=l
\*\* FindMaxChain returns c1, which is not notarized.
\*\* we chop off head and return it, but c2 with length l was notarized.
macro FindMaxNotarizedChain(e) {
   if (2*Cardinality ({m\in Msgs[self]: m.epoch=e /\ m.chain=FindMaxChain(self)}) > N)
      nChain:= FindMaxChain(self);
   else 
      nChain:= Tail(FindMaxChain(self)); 
}

fair process (p \in Nodes)
   variable nChain= <<>>, e=1, Q={};{
A: while (e<EMAX) {
      Q:=Nodes;
      if (e%N=self){
         FindMaxNotarizedChain(e-1); \* \* updates nChain
AP:      while (Q #{}) 
            with (p \in Q){ 
               Msgs[p]:= Msgs[p] \union {[chain|-> <<e>> \o nChain, epoch|->e, sender|->self]};
               Q:=Q\{p};
            }
      }
      else {
         await (\E m \in Msgs[self]: m.epoch=e);
         FindMaxNotarizedChain(e); \* \* updates nChain 
         if (Len(ExtractMsg(e,self).chain) = Len(nChain)+1)
AV:         while (Q #{}) 
               with (p \in Q){
                 Msgs[p]:= Msgs[p] \union {[chain|->ExtractMsg(e,self).chain, epoch|->e, sender|->self]};
                 Q:=Q\{p};
                 }
      };
AZ:   e:=e+1;
   }
} 

} \* \* end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES Msgs, pc

(* define statement *)
ExtractMsg(e,s) == CHOOSE m \in Msgs[s]: m.epoch=e
FindMaxChain(s) == CHOOSE z \in {m.chain: m \in Msgs[s]}:
             ~(\E x \in {m.chain: m \in Msgs[s]}: Len(x)>Len(z))
ThreeCons(c) == Len(c)>2 /\ Head(c)= Head(Tail(c))+1 /\ Head(Tail(c))=Head(Tail(Tail(c)))+1

VARIABLES nChain, e, Q

vars == << Msgs, pc, nChain, e, Q >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ Msgs = [n \in Nodes |-> {[chain|-> <<0>>, epoch|->0, sender|->0],
                                    [chain|-> <<0>>, epoch|->0, sender|->1],
                                    [chain|-> <<0>>, epoch|->0, sender|->2]}]
        (* Process p *)
        /\ nChain = [self \in Nodes |-> <<>>]
        /\ e = [self \in Nodes |-> 1]
        /\ Q = [self \in Nodes |-> {}]
        /\ pc = [self \in ProcSet |-> "A"]

A(self) == /\ pc[self] = "A"
           /\ IF e[self]<EMAX
                 THEN /\ Q' = [Q EXCEPT ![self] = Nodes]
                      /\ IF e[self]%N=self
                            THEN /\ IF 2*Cardinality ({m\in Msgs[self]: m.epoch=(e[self]-1) /\ m.chain=FindMaxChain(self)}) > N
                                       THEN /\ nChain' = [nChain EXCEPT ![self] = FindMaxChain(self)]
                                       ELSE /\ nChain' = [nChain EXCEPT ![self] = Tail(FindMaxChain(self))]
                                 /\ pc' = [pc EXCEPT ![self] = "AP"]
                            ELSE /\ (\E m \in Msgs[self]: m.epoch=e[self])
                                 /\ IF 2*Cardinality ({m\in Msgs[self]: m.epoch=e[self] /\ m.chain=FindMaxChain(self)}) > N
                                       THEN /\ nChain' = [nChain EXCEPT ![self] = FindMaxChain(self)]
                                       ELSE /\ nChain' = [nChain EXCEPT ![self] = Tail(FindMaxChain(self))]
                                 /\ IF Len(ExtractMsg(e[self],self).chain) = Len(nChain'[self])+1
                                       THEN /\ pc' = [pc EXCEPT ![self] = "AV"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "AZ"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << nChain, Q >>
           /\ UNCHANGED << Msgs, e >>

AZ(self) == /\ pc[self] = "AZ"
            /\ e' = [e EXCEPT ![self] = e[self]+1]
            /\ pc' = [pc EXCEPT ![self] = "A"]
            /\ UNCHANGED << Msgs, nChain, Q >>

AP(self) == /\ pc[self] = "AP"
            /\ IF Q[self] #{}
                  THEN /\ \E p \in Q[self]:
                            /\ Msgs' = [Msgs EXCEPT ![p] = Msgs[p] \union {[chain|-> <<e[self]>> \o nChain[self], epoch|->e[self], sender|->self]}]
                            /\ Q' = [Q EXCEPT ![self] = Q[self]\{p}]
                       /\ pc' = [pc EXCEPT ![self] = "AP"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "AZ"]
                       /\ UNCHANGED << Msgs, Q >>
            /\ UNCHANGED << nChain, e >>

AV(self) == /\ pc[self] = "AV"
            /\ IF Q[self] #{}
                  THEN /\ \E p \in Q[self]:
                            /\ Msgs' = [Msgs EXCEPT ![p] = Msgs[p] \union {[chain|->ExtractMsg(e[self],self).chain, epoch|->e[self], sender|->self]}]
                            /\ Q' = [Q EXCEPT ![self] = Q[self]\{p}]
                       /\ pc' = [pc EXCEPT ![self] = "AV"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "AZ"]
                       /\ UNCHANGED << Msgs, Q >>
            /\ UNCHANGED << nChain, e >>

p(self) == A(self) \/ AZ(self) \/ AP(self) \/ AV(self)

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
BaitLength == \A i \in Nodes: Len (nChain[i]) <5
BaitWidth ==  \A ep \in 1..EMAX : Cardinality({m \in Msgs: m.epoch=ep}) < 2
BaitSet == Cardinality(Msgs) <9
=========================================================

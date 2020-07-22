------------- MODULE str0 --------------------
(*\* Crash fault-tolerant streamlet algorithm *)
EXTENDS Integers, Sequences, FiniteSets
CONSTANT N, EMAX
Nodes == 0..N-1
E == 0..EMAX

(* 
--algorithm str0 {
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

\*\* What to do with two chains with length=l>1
\*\* FindMaxChain returns c1, which is not notarized.
\*\* we chop off head and return it, but c2 with length l was notarized.
macro FindMaxNotarizedChain() {
   if (\E ee \in E: 2*Cardinality ({m\in Msgs: m.epoch=ee /\ m.chain=FindMaxChain}) > N) \* notarized
      nChain:= FindMaxChain;
   else 
      nChain:= Tail(FindMaxChain); 
}

macro Propose (e) {
   await (~\E m \in Msgs: m.epoch=e);   
   FindMaxNotarizedChain(); \* \* updates nChain
   Msgs:= Msgs \union {[chain|-> <<e>> \o nChain, epoch|->e, sender|->self]}; 
}

macro Vote (e){
   await (\E m \in Msgs: m.epoch=e);
   FindMaxNotarizedChain(); \* \* updates nChain 
   if (Len(ExtractMsg(e).chain) = Len(nChain)+1)
      Msgs:= Msgs \union {[chain|->ExtractMsg(e).chain, epoch|->e, sender|->self]};
}

fair process (p \in Nodes)
   variable nChain= <<>>;
  {
A: while (TRUE) {
      with (e \in E) {
         if (e%N=self)  Propose(e)
         else Vote(e)
      }
   }
} 

} \* \* end algorithm
*)
\* BEGIN TRANSLATION
VARIABLE Msgs

(* define statement *)
ExtractMsg(e) == CHOOSE m \in Msgs: m.epoch=e
FindMaxChain == CHOOSE z \in {m.chain: m \in Msgs}:
             ~(\E x \in {m.chain: m \in Msgs}: Len(x)>Len(z))
ThreeCons(c) == Len(c)>2 /\ Head(c)= Head(Tail(c))+1 /\ Head(Tail(c))=Head(Tail(Tail(c)))+1

VARIABLE nChain

vars == << Msgs, nChain >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ Msgs = {[chain|-> <<0>>, epoch|->0, sender|->0],
                   [chain|-> <<0>>, epoch|->0, sender|->1],
                   [chain|-> <<0>>, epoch|->0, sender|->2]
                   }
        (* Process p *)
        /\ nChain = [self \in Nodes |-> <<>>]

p(self) == \E e \in E:
             IF e%N=self
                THEN /\ (~\E m \in Msgs: m.epoch=e)
                     /\ IF \E ee \in E: 2*Cardinality ({m\in Msgs: m.epoch=ee /\ m.chain=FindMaxChain}) > N
                           THEN /\ nChain' = [nChain EXCEPT ![self] = FindMaxChain]
                           ELSE /\ nChain' = [nChain EXCEPT ![self] = Tail(FindMaxChain)]
                     /\ Msgs' = (Msgs \union {[chain|-> <<e>> \o nChain'[self], epoch|->e, sender|->self]})
                ELSE /\ (\E m \in Msgs: m.epoch=e)
                     /\ IF \E ee \in E: 2*Cardinality ({m\in Msgs: m.epoch=ee /\ m.chain=FindMaxChain}) > N
                           THEN /\ nChain' = [nChain EXCEPT ![self] = FindMaxChain]
                           ELSE /\ nChain' = [nChain EXCEPT ![self] = Tail(FindMaxChain)]
                     /\ IF Len(ExtractMsg(e).chain) = Len(nChain'[self])+1
                           THEN /\ Msgs' = (Msgs \union {[chain|->ExtractMsg(e).chain, epoch|->e, sender|->self]})
                           ELSE /\ TRUE
                                /\ Msgs' = Msgs

Next == (\E self \in Nodes: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(p(self))

\* END TRANSLATION


---------------------------------------------------------
\* Invariants

\* Check three finality rule!!
Consistency == \A i,j \in Nodes: ThreeCons(nChain[i]) /\ ThreeCons(nChain[j]) /\ Len(nChain[i])=< Len(nChain[j]) 
                                 => \A k \in 1..Len(nChain[i])-1: nChain[i][k]=nChain[j][Len(nChain[j])-Len(nChain[i])+k]
Bait2 == ~( \E i \in Nodes: Len(nChain[i])>1 /\ Head(nChain[i])= Head(Tail(nChain[i]))+1 )
Bait3 == ~( \E i \in Nodes: Len(nChain[i])>2 /\ Head(nChain[i])= Head(Tail(nChain[i]))+1 
            /\ Head(Tail(nChain[i]))=Head(Tail(Tail(nChain[i])))+1 )
BaitLength == \A i \in Nodes: Len (nChain[i]) <4
BaitWidth ==  \A e \in 1..EMAX : Cardinality({m \in Msgs: m.epoch=e}) < 2
BaitSet == Cardinality(Msgs) <9
=========================================================

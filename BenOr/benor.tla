------------- MODULE benor2 --------------------
EXTENDS Integers, Sequences, FiniteSets
CONSTANT N, F, MAXROUND, INPUT
\* E.g., INPUT= <<0,1,1,1>> for N=4. 
ASSUME F<N   \* F is upperbound on # of crash faults
Procs == 1..N
(*
--algorithm benor
{ variable p1Msg={}, p2Msg={};

  define{
     ExtractValSet(S) == {m[3] : m \in S}
     SentP1Msgs(r) ==  {m \in p1Msg: m[2]=r}
     SentP1MsgsV(r,a) == {m \in p1Msg: m[2]=r /\ m[3]=a}                    
     SentP2Msgs(r) ==  {m \in p2Msg: m[2]=r}
     SentP2MsgsV(r,a) == {m \in p2Msg: m[2]=r /\ m[3]=a}          
  }

  macro EvalP1(r) {
     await ( Cardinality(SentP1Msgs(r))>= N-F ); \* await N-F p1-values
     if (\E a \in {0,1}: 2* Cardinality(SentP1MsgsV(r,a)) > N ) \* set p2v
        p2v:= CHOOSE a \in ExtractValSet(SentP1Msgs(r)): 2* Cardinality(SentP1MsgsV(r,a)) > N;
  }

  macro EvalP2(r) { \* set p1v for next round
     await ( Cardinality(SentP2Msgs(r))>= N-F ); \* await N-F p2-values
     if (  (\E a \in {0,1}: \* N-F may be > > F, so some v=-1, some v=a
               Cardinality(SentP2MsgsV(r,a)) > F) ) { 
        p1v:= CHOOSE a \in ExtractValSet(SentP2Msgs(r)): a#-1;
        decided:= p1v;}
     else if (\E a \in ExtractValSet(SentP2Msgs(r)): a#-1)
        p1v:= CHOOSE a \in ExtractValSet(SentP2Msgs(r)): a#-1;
     else with (v \in {0,1}) 
       {p1v:=v;}        
  }

  fair process (p \in Procs)
  variable r=1, p1v=INPUT[self], p2v=-1, decided=-1;
  { 
  S: while (r<= MAXROUND){
        p1Msg:=p1Msg \union {<<self, r, p1v>>}; \* bcast p1v for r
        p2v:=-1; \* default value
  CP1:  EvalP1(r); \* await N-F p1-values, evaluate phase1
        p2Msg:=p2Msg \union {<<self, r, p2v>>}; \* bcast p2v for r
  CP2:  EvalP2(r); \* await N-F p2-values, evaluate phase2
        r:=r+1;
     }
  }
  
} \* end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES p1Msg, p2Msg, pc

(* define statement *)
ExtractValSet(S) == {m[3] : m \in S}
SentP1Msgs(r) ==  {m \in p1Msg: m[2]=r}
SentP1MsgsV(r,a) == {m \in p1Msg: m[2]=r /\ m[3]=a}
SentP2Msgs(r) ==  {m \in p2Msg: m[2]=r}
SentP2MsgsV(r,a) == {m \in p2Msg: m[2]=r /\ m[3]=a}

VARIABLES r, p1v, p2v, decided

vars == << p1Msg, p2Msg, pc, r, p1v, p2v, decided >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ p1Msg = {}
        /\ p2Msg = {}
        (* Process p *)
        /\ r = [self \in Procs |-> 1]
        /\ p1v = [self \in Procs |-> INPUT[self]]
        /\ p2v = [self \in Procs |-> -1]
        /\ decided = [self \in Procs |-> -1]
        /\ pc = [self \in ProcSet |-> "S"]

S(self) == /\ pc[self] = "S"
           /\ IF r[self]<= MAXROUND
                 THEN /\ p1Msg' = (p1Msg \union {<<self, r[self], p1v[self]>>})
                      /\ p2v' = [p2v EXCEPT ![self] = -1]
                      /\ pc' = [pc EXCEPT ![self] = "CP1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << p1Msg, p2v >>
           /\ UNCHANGED << p2Msg, r, p1v, decided >>

CP1(self) == /\ pc[self] = "CP1"
             /\ ( Cardinality(SentP1Msgs(r[self]))>= N-F )
             /\ IF \E a \in {0,1}: 2* Cardinality(SentP1MsgsV(r[self],a)) > N
                   THEN /\ p2v' = [p2v EXCEPT ![self] = CHOOSE a \in ExtractValSet(SentP1Msgs(r[self])): 2* Cardinality(SentP1MsgsV(r[self],a)) > N]
                   ELSE /\ TRUE
                        /\ p2v' = p2v
             /\ p2Msg' = (p2Msg \union {<<self, r[self], p2v'[self]>>})
             /\ pc' = [pc EXCEPT ![self] = "CP2"]
             /\ UNCHANGED << p1Msg, r, p1v, decided >>

CP2(self) == /\ pc[self] = "CP2"
             /\ ( Cardinality(SentP2Msgs(r[self]))>= N-F )
             /\ IF (\E a \in {0,1}:
                       Cardinality(SentP2MsgsV(r[self],a)) > F)
                   THEN /\ p1v' = [p1v EXCEPT ![self] = CHOOSE a \in ExtractValSet(SentP2Msgs(r[self])): a#-1]
                        /\ decided' = [decided EXCEPT ![self] = p1v'[self]]
                   ELSE /\ IF \E a \in ExtractValSet(SentP2Msgs(r[self])): a#-1
                              THEN /\ p1v' = [p1v EXCEPT ![self] = CHOOSE a \in ExtractValSet(SentP2Msgs(r[self])): a#-1]
                              ELSE /\ \E v \in {0,1}:
                                        p1v' = [p1v EXCEPT ![self] = v]
                        /\ UNCHANGED decided
             /\ r' = [r EXCEPT ![self] = r[self]+1]
             /\ pc' = [pc EXCEPT ![self] = "S"]
             /\ UNCHANGED << p1Msg, p2Msg, p2v >>

p(self) == S(self) \/ CP1(self) \/ CP2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
---------------------------------------------------------
Agreement == \A j,k \in Procs: 
                decided[j]#-1  /\ decided[k]#-1 
                => decided[j]=decided[k]

BaitProgress == \E j \in Procs: decided[j]=-1
MinorityReport == ~ \A j \in Procs: decided[j]=0

Progress  == <> (\A j \in Procs: decided[j]#-1) 

=========================================================
See https://muratbuffalo.blogspot.com/2019/12/the-ben-or-decentralized-consensus.html
for explanation.
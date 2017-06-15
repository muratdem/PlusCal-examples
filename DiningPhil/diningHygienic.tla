---------------- MODULE diningHygienic ----------------
(* Dining philosophers problem, hygenic edition. *)
EXTENDS Naturals
CONSTANT N
ASSUME N \in Nat
Procs == 0..N-1
Topology == {<<0,1>>, <<0,3>>, <<1,3>>, <<2,3>>}
RTopology== {<<1,0>>, <<3,0>>, <<3,1>>, <<3,2>>}
(* 
--algorithm diningHygienic {
  variable fork = Topology, \*\* initially forks are at lower id side of the edges
  	   clean = {}, \*\* initially none of the forks is clean
  	   req= RTopology; \*\* initially req tokens are at higher id side of edges
  define{
  Edge(p,q) == IF (<<p,q>> \in Topology \/ <<q,p>> \in Topology) THEN TRUE ELSE FALSE
  GetNbrs(p) == {q \in Procs : Edge(p,q)}
  Forkat(p,q) == IF (<<p,q>> \in fork) THEN TRUE ELSE FALSE
  Reqat(p,q) == IF (<<p,q>> \in req) THEN TRUE ELSE FALSE
  Clean(p,q) == IF (<<p,q>> \in clean \/ <<q,p>> \in clean) THEN TRUE ELSE FALSE
  GetForkNbrs(p) == {q \in Procs : Edge(p,q) /\ ~Forkat(p,q) /\ Reqat(p,q)}
  GetReqNbrs(p) == {q \in Procs: Edge(p,q) /\ Reqat(p,q) 
                                /\ Forkat(p,q) /\ ~Clean(p,q)}
  }

  fair process (j \in Procs)
  variable state = "Thinking", Q={}, q=0; 
  {J0: while (TRUE) {
        if (state#"Eating" /\ GetReqNbrs(self)#{}){ \*\* answer request for fork
           Q:=GetReqNbrs(self); \*\* gather the reqs for the dirty forks
      Ai:  while(Q # {}){
             q:= CHOOSE k \in Q: TRUE; 
             Q:= Q \ {q};
             fork:=fork \ {<<self,q>>};
       Aii:  fork:=fork \union {<<q,self>>};
             clean:=clean \union {<<q,self>>};
           }\*\* endwhile    
        }\*\* else  
        else if (state="Hungry" /\ GetForkNbrs(self)#{}) 
           {Q:=GetForkNbrs(self);   \*\* if hungry, request forks
         Hi:while(Q # {}){
              q:= CHOOSE k \in Q: TRUE;
              Q:= Q \ {q};                   
              req:= req \ {<<self,q>>};
         Hii: req:= req \union {<<q,self>>};
            };\*\* endwhile
        }\*\* endelse        
        else if (state="Hungry" /\ (\A k \in Procs: Edge(self,k) => Forkat(self,k) 
            /\ (Clean(self,k) \/ ~Reqat(self,k)))) 
           {state:="Eating";} \*\* if ready to eat, eat 
        else if (state="Eating") \*\* if eating, go to thinking
           {state:="Thinking"; 
            Q:=GetNbrs(self);
        Ei: while(Q # {}){
              q:= CHOOSE k \in Q: TRUE;
              Q:= Q \ {q};                   
              clean:= clean \ {<<self,q>>};
           }\*\* endwhile
        }\*\* endelse   
        else if (state="Thinking") 
          {state:="Hungry";
        }\*\* endif
	    
     }\*\* endwhile (true)
    }\*\* endprocess
}\*\* endalg

****************************************************************)
\* BEGIN TRANSLATION
VARIABLES fork, clean, req, pc

(* define statement *)
Edge(p,q) == IF (<<p,q>> \in Topology \/ <<q,p>> \in Topology) THEN TRUE ELSE FALSE
GetNbrs(p) == {q \in Procs : Edge(p,q)}
Forkat(p,q) == IF (<<p,q>> \in fork) THEN TRUE ELSE FALSE
Reqat(p,q) == IF (<<p,q>> \in req) THEN TRUE ELSE FALSE
Clean(p,q) == IF (<<p,q>> \in clean \/ <<q,p>> \in clean) THEN TRUE ELSE FALSE
GetForkNbrs(p) == {q \in Procs : Edge(p,q) /\ ~Forkat(p,q) /\ Reqat(p,q)}
GetReqNbrs(p) == {q \in Procs: Edge(p,q) /\ Reqat(p,q)
                              /\ Forkat(p,q) /\ ~Clean(p,q)}

VARIABLES state, Q, q

vars == << fork, clean, req, pc, state, Q, q >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ fork = Topology
        /\ clean = {}
        /\ req = RTopology
        (* Process j *)
        /\ state = [self \in Procs |-> "Thinking"]
        /\ Q = [self \in Procs |-> {}]
        /\ q = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "J0"]

J0(self) == /\ pc[self] = "J0"
            /\ IF state[self]#"Eating" /\ GetReqNbrs(self)#{}
                  THEN /\ Q' = [Q EXCEPT ![self] = GetReqNbrs(self)]
                       /\ pc' = [pc EXCEPT ![self] = "Ai"]
                       /\ state' = state
                  ELSE /\ IF state[self]="Hungry" /\ GetForkNbrs(self)#{}
                             THEN /\ Q' = [Q EXCEPT ![self] = GetForkNbrs(self)]
                                  /\ pc' = [pc EXCEPT ![self] = "Hi"]
                                  /\ state' = state
                             ELSE /\ IF      state[self]="Hungry" /\ (\A k \in Procs: Edge(self,k) => Forkat(self,k)
                                        /\ (Clean(self,k) \/ ~Reqat(self,k)))
                                        THEN /\ state' = [state EXCEPT ![self] = "Eating"]
                                             /\ pc' = [pc EXCEPT ![self] = "J0"]
                                             /\ Q' = Q
                                        ELSE /\ IF state[self]="Eating"
                                                   THEN /\ state' = [state EXCEPT ![self] = "Thinking"]
                                                        /\ Q' = [Q EXCEPT ![self] = GetNbrs(self)]
                                                        /\ pc' = [pc EXCEPT ![self] = "Ei"]
                                                   ELSE /\ IF state[self]="Thinking"
                                                              THEN /\ state' = [state EXCEPT ![self] = "Hungry"]
                                                              ELSE /\ TRUE
                                                                   /\ state' = state
                                                        /\ pc' = [pc EXCEPT ![self] = "J0"]
                                                        /\ Q' = Q
            /\ UNCHANGED << fork, clean, req, q >>

Ai(self) == /\ pc[self] = "Ai"
            /\ IF Q[self] # {}
                  THEN /\ q' = [q EXCEPT ![self] = CHOOSE k \in Q[self]: TRUE]
                       /\ Q' = [Q EXCEPT ![self] = Q[self] \ {q'[self]}]
                       /\ fork' = fork \ {<<self,q'[self]>>}
                       /\ pc' = [pc EXCEPT ![self] = "Aii"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "J0"]
                       /\ UNCHANGED << fork, Q, q >>
            /\ UNCHANGED << clean, req, state >>

Aii(self) == /\ pc[self] = "Aii"
             /\ fork' = (fork \union {<<q[self],self>>})
             /\ clean' = (clean \union {<<q[self],self>>})
             /\ pc' = [pc EXCEPT ![self] = "Ai"]
             /\ UNCHANGED << req, state, Q, q >>

Hi(self) == /\ pc[self] = "Hi"
            /\ IF Q[self] # {}
                  THEN /\ q' = [q EXCEPT ![self] = CHOOSE k \in Q[self]: TRUE]
                       /\ Q' = [Q EXCEPT ![self] = Q[self] \ {q'[self]}]
                       /\ req' = req \ {<<self,q'[self]>>}
                       /\ pc' = [pc EXCEPT ![self] = "Hii"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "J0"]
                       /\ UNCHANGED << req, Q, q >>
            /\ UNCHANGED << fork, clean, state >>

Hii(self) == /\ pc[self] = "Hii"
             /\ req' = (req \union {<<q[self],self>>})
             /\ pc' = [pc EXCEPT ![self] = "Hi"]
             /\ UNCHANGED << fork, clean, state, Q, q >>

Ei(self) == /\ pc[self] = "Ei"
            /\ IF Q[self] # {}
                  THEN /\ q' = [q EXCEPT ![self] = CHOOSE k \in Q[self]: TRUE]
                       /\ Q' = [Q EXCEPT ![self] = Q[self] \ {q'[self]}]
                       /\ clean' = clean \ {<<self,q'[self]>>}
                       /\ pc' = [pc EXCEPT ![self] = "Ei"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "J0"]
                       /\ UNCHANGED << clean, Q, q >>
            /\ UNCHANGED << fork, req, state >>

j(self) == J0(self) \/ Ai(self) \/ Aii(self) \/ Hi(self) \/ Hii(self)
              \/ Ei(self)

Next == (\E self \in Procs: j(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))

\* END TRANSLATION

\* \*Safety properties and liveness property to be checked
ME == \A k,l \in Procs: (state[k]="Eating"/\ state[l]="Eating") => ~Edge(k,l)
TypeOkFork == \A k,l \in Procs: Forkat(k,l) => ~Forkat(l,k)
TypeOkReq == \A k,l \in Procs: Reqat(k,l) => ~Reqat(l,k)

NoStarvation ==  \A p \in Procs: [] (state[p]="Hungry" => <> (state[p]="Eating"))
==================================



Thu, 20 Oct 16 - - - 23:34
thought about modeling fork like this, but then i would have two forks at each edge, incoming edge and outgoing edge.
hard to manage.

variable fork = [p \in Procs |-> [q \in Procs |-> InitFork(p,q)]],
  	   req= [p \in Procs |-> [q \in Procs |-> InitReq(p,q)]],
  	   clean= [p \in Procs |-> [q \in Procs |-> FALSE]]; 	   

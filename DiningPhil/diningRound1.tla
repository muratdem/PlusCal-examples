---------------- MODULE diningRound1 ----------------
(* \* Dining philosophers problem, round table edition. *)
(* \* proc 0 is distinguished to be lefty, so no deadlocks *)
(* \* But not fair, some processes starve *)
(* \* By: Murat Demirbas, 26 Oct 2016  *)
EXTENDS Naturals
CONSTANT N
ASSUME N \in Nat
Procs == 0..N-1


(* 
--algorithm diningRound {
  variable fork = [k \in Procs |-> N]; \* initially all forks are available

  define{
  forkAvailable(i) == fork[i]=N
  LeftF(i) == i
  LeftP(i) == IF (i=N-1) THEN 0 ELSE i+1
  RightF(i) == IF (i=0) THEN (N-1) ELSE (i-1)
  RightP(i) == IF (i=0) THEN (N-1) ELSE (i-1)  
  }

   fair process (j \in Procs)
   variable state = "Thinking"; 
    { 
    J0: while (TRUE) {
      H: either{
      	      if (state="Thinking") state:="Hungry";
      	      }
       or P:{
	     if (self#0 /\ state="Hungry"){
		      await(forkAvailable(RightF(self)));
      	    	    fork[RightF(self)]:=self;
      	   E: await(forkAvailable(LeftF(self)));
		      fork[LeftF(self)]:=self;
		      state:="Eating";
		    }
		else if (self=0 /\ state="Hungry"){ \* self=0 is lefty
      	      await(forkAvailable(LeftF(self)));
		          fork[LeftF(self)]:=self;
		  E0: await(forkAvailable(RightF(self)));
      	      fork[RightF(self)]:=self;
		      state:="Eating";
		  }
              }
      or T:{
      		if (state="Eating"){
      		    state:="Thinking";
      		    fork[LeftF(self)]:=N;
      		  R:fork[RightF(self)]:=N;
      		 }   
      		}
      }		
    }
}

****************************************************************)
\* BEGIN TRANSLATION
VARIABLES fork, pc

(* define statement *)
forkAvailable(i) == fork[i]=N
LeftF(i) == i
LeftP(i) == IF (i=N-1) THEN 0 ELSE i+1
RightF(i) == IF (i=0) THEN (N-1) ELSE (i-1)
RightP(i) == IF (i=0) THEN (N-1) ELSE (i-1)

VARIABLE state

vars == << fork, pc, state >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ fork = [k \in Procs |-> N]
        (* Process j *)
        /\ state = [self \in Procs |-> "Thinking"]
        /\ pc = [self \in ProcSet |-> "J0"]

J0(self) == /\ pc[self] = "J0"
            /\ pc' = [pc EXCEPT ![self] = "H"]
            /\ UNCHANGED << fork, state >>

H(self) == /\ pc[self] = "H"
           /\ \/ /\ IF state[self]="Thinking"
                       THEN /\ state' = [state EXCEPT ![self] = "Hungry"]
                       ELSE /\ TRUE
                            /\ state' = state
                 /\ pc' = [pc EXCEPT ![self] = "J0"]
              \/ /\ pc' = [pc EXCEPT ![self] = "P"]
                 /\ state' = state
              \/ /\ pc' = [pc EXCEPT ![self] = "T"]
                 /\ state' = state
           /\ fork' = fork

P(self) == /\ pc[self] = "P"
           /\ IF self#0 /\ state[self]="Hungry"
                 THEN /\ (forkAvailable(RightF(self)))
                      /\ fork' = [fork EXCEPT ![RightF(self)] = self]
                      /\ pc' = [pc EXCEPT ![self] = "E"]
                 ELSE /\ IF self=0 /\ state[self]="Hungry"
                            THEN /\ (forkAvailable(LeftF(self)))
                                 /\ fork' = [fork EXCEPT ![LeftF(self)] = self]
                                 /\ pc' = [pc EXCEPT ![self] = "E0"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "J0"]
                                 /\ fork' = fork
           /\ state' = state

E(self) == /\ pc[self] = "E"
           /\ (forkAvailable(LeftF(self)))
           /\ fork' = [fork EXCEPT ![LeftF(self)] = self]
           /\ state' = [state EXCEPT ![self] = "Eating"]
           /\ pc' = [pc EXCEPT ![self] = "J0"]

E0(self) == /\ pc[self] = "E0"
            /\ (forkAvailable(RightF(self)))
            /\ fork' = [fork EXCEPT ![RightF(self)] = self]
            /\ state' = [state EXCEPT ![self] = "Eating"]
            /\ pc' = [pc EXCEPT ![self] = "J0"]

T(self) == /\ pc[self] = "T"
           /\ IF state[self]="Eating"
                 THEN /\ state' = [state EXCEPT ![self] = "Thinking"]
                      /\ fork' = [fork EXCEPT ![LeftF(self)] = N]
                      /\ pc' = [pc EXCEPT ![self] = "R"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "J0"]
                      /\ UNCHANGED << fork, state >>

R(self) == /\ pc[self] = "R"
           /\ fork' = [fork EXCEPT ![RightF(self)] = N]
           /\ pc' = [pc EXCEPT ![self] = "J0"]
           /\ state' = state

j(self) == J0(self) \/ H(self) \/ P(self) \/ E(self) \/ E0(self) \/ T(self)
              \/ R(self)

Next == (\E self \in Procs: j(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j(self))

\* END TRANSLATION

\* DEADLOCK is reached as all processes go to PREP, but none of them can proceed to HUNGRY waiting for the Left fork
ME == \A p \in Procs: (state[p]="Eating" => (state[LeftP(p)]#"Eating" /\ state[RightP(p)]#"Eating"))
NoStarvation ==  \A p \in Procs: [] (state[p]="Hungry" => <> (state[p]="Eating"))
\* DeadlockFreedom == \A 
==================================

------------------------- MODULE CabbageGoatWolf_Pluscal -----------------------------
EXTENDS Naturals, FiniteSets, TLC
\* Solving the https://en.wikipedia.org/wiki/Wolf,_goat_and_cabbage_problem
    
Sides == {1,2}
C == "Cabbage"
G == "Goat"
W == "Wolf"
F == "Farmer"

Allowed(S) == 
    \/ F \in S 
    \/ (/\ ~ ( C \in S  /\  G \in S )
        /\ ~ ( G \in S  /\  W \in S ) )


(* --algorithm CabbageGoatWolf {
  variables 
    banks = << {C,G,W,F}, {} >>;
    boat  = {};

define {
    SafeBoats(s) == 
        { B \in SUBSET banks[s]:
            /\ F \in B
            /\ Cardinality(B) <= 2 
            /\ Allowed(banks[s] \ B) }
    
    TypeOK == 
        /\ Cardinality(banks[1]) + Cardinality(banks[2]) + Cardinality(boat) = 4
        /\ Cardinality(boat) <=2 
        /\ boat \in SUBSET {F,C,G,W}
        /\ banks[1] \in SUBSET {F,C,G,W}
        /\ banks[2] \in SUBSET {F,C,G,W}

    NotSolved == Cardinality(banks[2]) < 4     
}

fair process (Bank \in Sides) 
{
S: while (TRUE) {
    either { \* LOAD 
        await (banks[self]#{} /\  boat={});
        with (P \in SafeBoats(self)) {
            boat := P;
            banks[self] := banks[self] \ P;
        }  
    } or { \* UNLOAD
        await (boat#{});
        banks[self] :=  banks[self] \union boat;
        boat := {};
    }

  } \* end while     
}

} \* end algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "3bc90940" /\ chksum(tla) = "2c10c4a9")
VARIABLES banks, boat

(* define statement *)
SafeBoats(s) ==
    { B \in SUBSET banks[s]:
        /\ F \in B
        /\ Cardinality(B) <= 2
        /\ Allowed(banks[s] \ B) }

TypeOK ==
    /\ Cardinality(banks[1]) + Cardinality(banks[2]) + Cardinality(boat) = 4
    /\ Cardinality(boat) <=2
    /\ boat \in SUBSET {F,C,G,W}
    /\ banks[1] \in SUBSET {F,C,G,W}
    /\ banks[2] \in SUBSET {F,C,G,W}

NotSolved == Cardinality(banks[2]) < 4


vars == << banks, boat >>

ProcSet == (Sides)

Init == (* Global variables *)
        /\ banks = << {C,G,W,F}, {} >>
        /\ boat = {}

Bank(self) == \/ /\ (banks[self]#{} /\  boat={})
                 /\ \E P \in SafeBoats(self):
                      /\ boat' = P
                      /\ banks' = [banks EXCEPT ![self] = banks[self] \ P]
              \/ /\ (boat#{})
                 /\ banks' = [banks EXCEPT ![self] = banks[self] \union boat]
                 /\ boat' = {}

Next == (\E self \in Sides: Bank(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Sides : WF_vars(Bank(self))

\* END TRANSLATION 

------------------

============================================================

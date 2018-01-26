----------------------- MODULE dao --------------------
EXTENDS TLC, Integers, Sequences
CONSTANT BALANCE, AMOUNT

(* --algorithm Dao_Attack {
variable attack = 3,
  bankBalance = BALANCE,
  malloryBalance = 0;
  
define{
  SafeWithdrawal == 
      \/ bankBalance=BALANCE /\ malloryBalance=0
      \/ bankBalance=BALANCE /\ malloryBalance=AMOUNT
      \/ bankBalance=BALANCE-AMOUNT /\ malloryBalance=AMOUNT}

procedure BankWithdraw(amount) {
  CheckBalance: \* check if Mallory has sufficient balance
    if (bankBalance < amount) return;
  DispenseAmount: \* dispense Mallory the amount
    call MallorySendMoney(amount);
  FinishWithdraw: \* update Mallory's bankBalance  
    bankBalance := bankBalance-amount; 
  return;}

procedure MallorySendMoney(amount){
  Receive:
    malloryBalance := malloryBalance + amount;
    if (attack>0){
      attack := attack -1; \* avoid infinite stack; don't run out of gas    
      call BankWithdraw(amount);}; \* cheating! doublecalling withdraw
FC:return;}

fair process (blockchain = "blockchain") {
  Transact: \* Mallory calls Bank to withdraw AMOUNT from her bankBalance
    call BankWithdraw(AMOUNT);}

} *)
\* BEGIN TRANSLATION
\* Parameter amount of procedure BankWithdraw at line 16 col 24 changed to amount_
CONSTANT defaultInitValue
VARIABLES attack, bankBalance, malloryBalance, pc, stack

(* define statement *)
SafeWithdrawal ==
    \/ bankBalance=BALANCE /\ malloryBalance=0
    \/ bankBalance=BALANCE /\ malloryBalance=AMOUNT
    \/ bankBalance=BALANCE-AMOUNT /\ malloryBalance=AMOUNT

VARIABLES amount_, amount

vars == << attack, bankBalance, malloryBalance, pc, stack, amount_, amount >>

ProcSet == {"blockchain"}

Init == (* Global variables *)
        /\ attack = 3
        /\ bankBalance = BALANCE
        /\ malloryBalance = 0
        (* Procedure BankWithdraw *)
        /\ amount_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure MallorySendMoney *)
        /\ amount = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Transact"]

CheckBalance(self) == /\ pc[self] = "CheckBalance"
                      /\ IF bankBalance < amount_[self]
                            THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ amount_' = [amount_ EXCEPT ![self] = Head(stack[self]).amount_]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "DispenseAmount"]
                                 /\ UNCHANGED << stack, amount_ >>
                      /\ UNCHANGED << attack, bankBalance, malloryBalance, 
                                      amount >>

DispenseAmount(self) == /\ pc[self] = "DispenseAmount"
                        /\ /\ amount' = [amount EXCEPT ![self] = amount_[self]]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "MallorySendMoney",
                                                                    pc        |->  "FinishWithdraw",
                                                                    amount    |->  amount[self] ] >>
                                                                \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "Receive"]
                        /\ UNCHANGED << attack, bankBalance, malloryBalance, 
                                        amount_ >>

FinishWithdraw(self) == /\ pc[self] = "FinishWithdraw"
                        /\ bankBalance' = bankBalance-amount_[self]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ amount_' = [amount_ EXCEPT ![self] = Head(stack[self]).amount_]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << attack, malloryBalance, amount >>

BankWithdraw(self) == CheckBalance(self) \/ DispenseAmount(self)
                         \/ FinishWithdraw(self)

Receive(self) == /\ pc[self] = "Receive"
                 /\ malloryBalance' = malloryBalance + amount[self]
                 /\ IF attack>0
                       THEN /\ attack' = attack -1
                            /\ /\ amount_' = [amount_ EXCEPT ![self] = amount[self]]
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "BankWithdraw",
                                                                        pc        |->  "FC",
                                                                        amount_   |->  amount_[self] ] >>
                                                                    \o stack[self]]
                            /\ pc' = [pc EXCEPT ![self] = "CheckBalance"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "FC"]
                            /\ UNCHANGED << attack, stack, amount_ >>
                 /\ UNCHANGED << bankBalance, amount >>

FC(self) == /\ pc[self] = "FC"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ amount' = [amount EXCEPT ![self] = Head(stack[self]).amount]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << attack, bankBalance, malloryBalance, amount_ >>

MallorySendMoney(self) == Receive(self) \/ FC(self)

Transact == /\ pc["blockchain"] = "Transact"
            /\ /\ amount_' = [amount_ EXCEPT !["blockchain"] = AMOUNT]
               /\ stack' = [stack EXCEPT !["blockchain"] = << [ procedure |->  "BankWithdraw",
                                                                pc        |->  "Done",
                                                                amount_   |->  amount_["blockchain"] ] >>
                                                            \o stack["blockchain"]]
            /\ pc' = [pc EXCEPT !["blockchain"] = "CheckBalance"]
            /\ UNCHANGED << attack, bankBalance, malloryBalance, amount >>

blockchain == Transact

Next == blockchain
           \/ (\E self \in ProcSet:  \/ BankWithdraw(self)
                                     \/ MallorySendMoney(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ /\ WF_vars(blockchain)
           /\ WF_vars(BankWithdraw("blockchain"))
           /\ WF_vars(MallorySendMoney("blockchain"))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

==============================================
  SafeWithdrawal1 ==
      \/ accountAlice=BALANCE /\ accountBob=0
      \/ accountAlice=BALANCE-AMOUNT /\ accountBob=AMOUNT
This was too restrictive, because updating of both Alice's and Bob's accounts do not happen atomically.
/\  accountAlice = 12
/\  accountBob = 5
/\  accountTotal = 12
/\  amount = [blockchain |-> 5]
/\  amount_ = [blockchain |-> 5]
/\  pc = [blockchain |-> "CheckBalance"]
/\  stack = [blockchain |-> <<[pc |-> "FinishAlice2", amount_ |-> 5, procedure |-> "withdrawFromAlice"], [pc |-> "Done", amount_ |-> defaultInitValue, procedure |-> "withdrawFromAlice"]>>]

after Bob got money, but before it was subtracted from Alice's account, the SafeWithdrawal1 broke.
So I need to relax this.

Yes, TLA found the double-spending!!!
/\  accountAlice = 12
/\  accountBob = 10
/\  accountTotal = 12
/\  amount = [blockchain |-> 5]
/\  amount_ = [blockchain |-> 5]
/\  pc = [blockchain |-> "CheckBalance"]
/\  stack = [blockchain |-> <<[pc |-> "FinishAlice2", amount_ |-> 5, procedure |-> "withdrawFromAlice"], [pc |-> "FinishAlice2", amount_ |-> 5, procedure |-> "withdrawFromAlice"], [pc |-> "Done", amount_ |-> defaultInitValue, procedure |-> "withdrawFromAlice"]>>]

Bob's account got 10! Double withdrawal.
Even if I make Alice's account subtraction line 25 come before sendMoney, 
I would have the same double withdrawal problem!


\* assert accountAlice >= BALANCE-AMOUNT;

function withdraw(uint amount) {
client = msg.sender;
if (balance[ client ] >= amount} {
if (client.call.sendMoney(amount)){ balance[ client ] −= amount;
}}}

function sendMoney(unit amount) {
victim = msg.sender;
balance += amount;
victim . withdraw(amount)
}


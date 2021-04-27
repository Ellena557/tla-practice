--------------------------- MODULE PingPongSync ---------------------------

EXTENDS Integers, TLC, Sequences

(* --algorithm xp
variables
  turn = 0;
  counter = 1000;

process Ping = 0
begin
\* while (TRUE) do
Ping_step1:  while (counter > 0) do
  
\* while(turn)
\*Ping_step2:    while (turn) do
Ping_step2:      await (turn = 0);

\* critical section
Ping_step3:      skip;

\* decrease counter
Ping_step4:      counter := counter - 1;

\* change flag
Ping_step5:      turn := 1;

    end while;
end process;

process Pong = 1
begin
Pong_step1:  while (counter > 0) do
  
\* while(turn)
\* Pong_step2:    while (~turn) do
Pong_step2:      await (turn = 1);

\* critical section
Pong_step3:      skip;

\* decrease counter
Pong_step4:      counter := counter - 1;

\* change flag
Pong_step5:      turn := 0;

    end while;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "95612b2e" /\ chksum(tla) = "cc5ec11c")
VARIABLES turn, counter, pc

vars == << turn, counter, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ turn = 0
        /\ counter = 1000
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "Ping_step1"
                                        [] self = 1 -> "Pong_step1"]

Ping_step1 == /\ pc[0] = "Ping_step1"
              /\ IF (counter > 0)
                    THEN /\ pc' = [pc EXCEPT ![0] = "Ping_step2"]
                    ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
              /\ UNCHANGED << turn, counter >>

Ping_step2 == /\ pc[0] = "Ping_step2"
              /\ (turn = 0)
              /\ pc' = [pc EXCEPT ![0] = "Ping_step3"]
              /\ UNCHANGED << turn, counter >>

Ping_step3 == /\ pc[0] = "Ping_step3"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![0] = "Ping_step4"]
              /\ UNCHANGED << turn, counter >>

Ping_step4 == /\ pc[0] = "Ping_step4"
              /\ counter' = counter - 1
              /\ pc' = [pc EXCEPT ![0] = "Ping_step5"]
              /\ turn' = turn

Ping_step5 == /\ pc[0] = "Ping_step5"
              /\ turn' = 1
              /\ pc' = [pc EXCEPT ![0] = "Ping_step1"]
              /\ UNCHANGED counter

Ping == Ping_step1 \/ Ping_step2 \/ Ping_step3 \/ Ping_step4 \/ Ping_step5

Pong_step1 == /\ pc[1] = "Pong_step1"
              /\ IF (counter > 0)
                    THEN /\ pc' = [pc EXCEPT ![1] = "Pong_step2"]
                    ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
              /\ UNCHANGED << turn, counter >>

Pong_step2 == /\ pc[1] = "Pong_step2"
              /\ (turn = 1)
              /\ pc' = [pc EXCEPT ![1] = "Pong_step3"]
              /\ UNCHANGED << turn, counter >>

Pong_step3 == /\ pc[1] = "Pong_step3"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![1] = "Pong_step4"]
              /\ UNCHANGED << turn, counter >>

Pong_step4 == /\ pc[1] = "Pong_step4"
              /\ counter' = counter - 1
              /\ pc' = [pc EXCEPT ![1] = "Pong_step5"]
              /\ turn' = turn

Pong_step5 == /\ pc[1] = "Pong_step5"
              /\ turn' = 0
              /\ pc' = [pc EXCEPT ![1] = "Pong_step1"]
              /\ UNCHANGED counter

Pong == Pong_step1 \/ Pong_step2 \/ Pong_step3 \/ Pong_step4 \/ Pong_step5

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Ping \/ Pong
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 





(***************************************************************************)
(* The following formula asserts that no two processes are in the        *)
(* critcal sections at the same time.                                    *)
(***************************************************************************)
MutualExclusion == {pc[0], pc[1]} # {"Ping_step3", "Pong_step3"}


(***************************************************************************)
(* The following formula asserts that counter is not negative              *)
(***************************************************************************)
TypeOK == counter >= -1



=============================================================================
\* Modification History
\* Last modified Tue Apr 27 03:14:17 MSK 2021 by Elena
\* Created Mon Apr 26 23:17:12 MSK 2021 by Elena

--------------------------- MODULE Semaphore ---------------------------

EXTENDS Integers, TLC

(* --algorithm xp
variables
  semaphore = 0;
  
process Thread_0 = 0
begin
T0_step1:   while (TRUE) do

\* semaphore.Wait();
T0_step2:    await (semaphore >= 1); 
             semaphore := semaphore - 1;

\* critical_section();
T0_step3:    skip;
             
\* semaphore.Release();
T0_step4:    semaphore := semaphore + 1;

  end while;
end process;

\* producer
process Thread_1 = 1
begin
T1_step1:   while (TRUE) do

\* semaphore.Wait();
T1_step2:    if (semaphore >= 1) then
               await (semaphore >= 1); 
               semaphore := semaphore - 1;

\* critical_section();
T1_step3:      skip;
             
\* semaphore.Release();
T1_step4:      semaphore := semaphore + 1;

               else
T1_step5:        semaphore := semaphore + 1;
               end if;


  end while;
end process;

end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "c1b8614f" /\ chksum(tla) = "ef56811")
VARIABLES semaphore, pc

vars == << semaphore, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ semaphore = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "T0_step1"
                                        [] self = 1 -> "T1_step1"]

T0_step1 == /\ pc[0] = "T0_step1"
            /\ pc' = [pc EXCEPT ![0] = "T0_step2"]
            /\ UNCHANGED semaphore

T0_step2 == /\ pc[0] = "T0_step2"
            /\ (semaphore >= 1)
            /\ semaphore' = semaphore - 1
            /\ pc' = [pc EXCEPT ![0] = "T0_step3"]

T0_step3 == /\ pc[0] = "T0_step3"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![0] = "T0_step4"]
            /\ UNCHANGED semaphore

T0_step4 == /\ pc[0] = "T0_step4"
            /\ semaphore' = semaphore + 1
            /\ pc' = [pc EXCEPT ![0] = "T0_step1"]

Thread_0 == T0_step1 \/ T0_step2 \/ T0_step3 \/ T0_step4

T1_step1 == /\ pc[1] = "T1_step1"
            /\ pc' = [pc EXCEPT ![1] = "T1_step2"]
            /\ UNCHANGED semaphore

T1_step2 == /\ pc[1] = "T1_step2"
            /\ IF (semaphore >= 1)
                  THEN /\ (semaphore >= 1)
                       /\ semaphore' = semaphore - 1
                       /\ pc' = [pc EXCEPT ![1] = "T1_step3"]
                  ELSE /\ pc' = [pc EXCEPT ![1] = "T1_step5"]
                       /\ UNCHANGED semaphore

T1_step3 == /\ pc[1] = "T1_step3"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![1] = "T1_step4"]
            /\ UNCHANGED semaphore

T1_step4 == /\ pc[1] = "T1_step4"
            /\ semaphore' = semaphore + 1
            /\ pc' = [pc EXCEPT ![1] = "T1_step1"]

T1_step5 == /\ pc[1] = "T1_step5"
            /\ semaphore' = semaphore + 1
            /\ pc' = [pc EXCEPT ![1] = "T1_step1"]

Thread_1 == T1_step1 \/ T1_step2 \/ T1_step3 \/ T1_step4 \/ T1_step5

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Thread_0 \/ Thread_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

(***************************************************************************)
(* The following formula asserts that no two processes are in the        *)
(* critcal sections at the same time.                                    *)
(***************************************************************************)
MutualExclusion == {pc[0], pc[1]} # {"T0_step3", "T1_step3"}


=============================================================================
\* Modification History
\* Last modified Tue Apr 27 20:16:31 MSK 2021 by Elena
\* Created Mon Apr 26 04:12:53 MSK 2021 by Elena

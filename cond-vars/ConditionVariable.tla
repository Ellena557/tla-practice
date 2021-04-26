--------------------------- MODULE ConditionVariable ---------------------------

EXTENDS Integers, TLC, Sequences

(* --algorithm xp
variables
  mutex = "free";
  queueSize = 0;
  
process Thread0 = 0
begin
T0_step1:  while (TRUE) do
  
\* Monitor.Enter(mutex); 
T0_step2:    await (mutex = "free");
             mutex := "t0";        \* take mutex

\* if (queue.Count == 0)
T0_step3:      if (queueSize = 0) then
                 mutex := "free";

\* Monitor.Wait(mutex);
T0_step4_1:      await (mutex = "wakeup");    \* wait until it is woken up by a pulse

T0_step4_2:      await (mutex = "free");      \* take again
                 mutex := "t0";
               end if;
               
\* queue.Dequeue();
T0_step5:      queueSize := queueSize - 1;   
    
\* Monitor.Exit(mutex);
T0_step6:      mutex := "free";

  end while;
end process;

process Thread1 = 1
begin
T1_step1:  while (TRUE) do
  
\* Monitor.Enter(mutex); 
T1_step2:    await (mutex = "free");
             mutex := "t1";        \* take mutex

\* if (queue.Count == 0)
T1_step3:      if (queueSize = 0) then
                 mutex := "free";
  
\* Monitor.Wait(mutex);
T1_step4_1:      await (mutex = "wakeup");    \* wait until it is woken up by a pulse

T1_step4_2:      await (mutex = "free");      \* take again
                 mutex := "t1";
               end if;
               
\* queue.Dequeue();
T1_step5:      queueSize := queueSize - 1;   
    
\* Monitor.Exit(mutex);
T1_step6:      mutex := "free";

  end while;
end process;

process Thread2 = 2
begin
T2_step1:  while (TRUE) do
  
\* Monitor.Enter(mutex);
T2_step2:    await (mutex = "free");
             mutex := "t2";       \* take mutex

\* queue.Enqueue(42);
T2_step3:    queueSize := queueSize + 1;  
  
\* Monitor.PulseAll(mutex);
T2_step4:    mutex := "wakeup";   \* signals other threads   
               
\* Monitor.Exit(mutex);
T2_step5:    mutex := "free";  

  end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "32274274" /\ chksum(tla) = "fef8734b")
VARIABLES mutex, queueSize, pc

vars == << mutex, queueSize, pc >>

ProcSet == {0} \cup {1} \cup {2}

Init == (* Global variables *)
        /\ mutex = "free"
        /\ queueSize = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "T0_step1"
                                        [] self = 1 -> "T1_step1"
                                        [] self = 2 -> "T2_step1"]

T0_step1 == /\ pc[0] = "T0_step1"
            /\ pc' = [pc EXCEPT ![0] = "T0_step2"]
            /\ UNCHANGED << mutex, queueSize >>

T0_step2 == /\ pc[0] = "T0_step2"
            /\ (mutex = "free")
            /\ mutex' = "t0"
            /\ pc' = [pc EXCEPT ![0] = "T0_step3"]
            /\ UNCHANGED queueSize

T0_step3 == /\ pc[0] = "T0_step3"
            /\ IF (queueSize = 0)
                  THEN /\ mutex' = "free"
                       /\ pc' = [pc EXCEPT ![0] = "T0_step4_1"]
                  ELSE /\ pc' = [pc EXCEPT ![0] = "T0_step5"]
                       /\ mutex' = mutex
            /\ UNCHANGED queueSize

T0_step4_1 == /\ pc[0] = "T0_step4_1"
              /\ (mutex = "wakeup")
              /\ pc' = [pc EXCEPT ![0] = "T0_step4_2"]
              /\ UNCHANGED << mutex, queueSize >>

T0_step4_2 == /\ pc[0] = "T0_step4_2"
              /\ (mutex = "free")
              /\ mutex' = "t0"
              /\ pc' = [pc EXCEPT ![0] = "T0_step5"]
              /\ UNCHANGED queueSize

T0_step5 == /\ pc[0] = "T0_step5"
            /\ queueSize' = queueSize - 1
            /\ pc' = [pc EXCEPT ![0] = "T0_step6"]
            /\ mutex' = mutex

T0_step6 == /\ pc[0] = "T0_step6"
            /\ mutex' = "free"
            /\ pc' = [pc EXCEPT ![0] = "T0_step1"]
            /\ UNCHANGED queueSize

Thread0 == T0_step1 \/ T0_step2 \/ T0_step3 \/ T0_step4_1 \/ T0_step4_2
              \/ T0_step5 \/ T0_step6

T1_step1 == /\ pc[1] = "T1_step1"
            /\ pc' = [pc EXCEPT ![1] = "T1_step2"]
            /\ UNCHANGED << mutex, queueSize >>

T1_step2 == /\ pc[1] = "T1_step2"
            /\ (mutex = "free")
            /\ mutex' = "t1"
            /\ pc' = [pc EXCEPT ![1] = "T1_step3"]
            /\ UNCHANGED queueSize

T1_step3 == /\ pc[1] = "T1_step3"
            /\ IF (queueSize = 0)
                  THEN /\ mutex' = "free"
                       /\ pc' = [pc EXCEPT ![1] = "T1_step4_1"]
                  ELSE /\ pc' = [pc EXCEPT ![1] = "T1_step5"]
                       /\ mutex' = mutex
            /\ UNCHANGED queueSize

T1_step4_1 == /\ pc[1] = "T1_step4_1"
              /\ (mutex = "wakeup")
              /\ pc' = [pc EXCEPT ![1] = "T1_step4_2"]
              /\ UNCHANGED << mutex, queueSize >>

T1_step4_2 == /\ pc[1] = "T1_step4_2"
              /\ (mutex = "free")
              /\ mutex' = "t1"
              /\ pc' = [pc EXCEPT ![1] = "T1_step5"]
              /\ UNCHANGED queueSize

T1_step5 == /\ pc[1] = "T1_step5"
            /\ queueSize' = queueSize - 1
            /\ pc' = [pc EXCEPT ![1] = "T1_step6"]
            /\ mutex' = mutex

T1_step6 == /\ pc[1] = "T1_step6"
            /\ mutex' = "free"
            /\ pc' = [pc EXCEPT ![1] = "T1_step1"]
            /\ UNCHANGED queueSize

Thread1 == T1_step1 \/ T1_step2 \/ T1_step3 \/ T1_step4_1 \/ T1_step4_2
              \/ T1_step5 \/ T1_step6

T2_step1 == /\ pc[2] = "T2_step1"
            /\ pc' = [pc EXCEPT ![2] = "T2_step2"]
            /\ UNCHANGED << mutex, queueSize >>

T2_step2 == /\ pc[2] = "T2_step2"
            /\ (mutex = "free")
            /\ mutex' = "t2"
            /\ pc' = [pc EXCEPT ![2] = "T2_step3"]
            /\ UNCHANGED queueSize

T2_step3 == /\ pc[2] = "T2_step3"
            /\ queueSize' = queueSize + 1
            /\ pc' = [pc EXCEPT ![2] = "T2_step4"]
            /\ mutex' = mutex

T2_step4 == /\ pc[2] = "T2_step4"
            /\ mutex' = "wakeup"
            /\ pc' = [pc EXCEPT ![2] = "T2_step5"]
            /\ UNCHANGED queueSize

T2_step5 == /\ pc[2] = "T2_step5"
            /\ mutex' = "free"
            /\ pc' = [pc EXCEPT ![2] = "T2_step1"]
            /\ UNCHANGED queueSize

Thread2 == T2_step1 \/ T2_step2 \/ T2_step3 \/ T2_step4 \/ T2_step5

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Thread0 \/ Thread1 \/ Thread2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Apr 27 02:34:51 MSK 2021 by Elena
\* Created Mon Apr 26 05:01:12 MSK 2021 by Elena

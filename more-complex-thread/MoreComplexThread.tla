--------------------------- MODULE MoreComplexThread ---------------------------

EXTENDS Integers, TLC, Sequences

(* --algorithm xp
variables
  mutex1 = 0;
  mutex2 = 0;
  mutex3 = 0;
  flag = FALSE;
  holder1 = 2;     \* who holds mutex1 (0 - Thread0, 1 - Thread1, 2 - no one)
  holder2 = 2;
  holder3 = 2;
  
process Thread0 = 0
begin
T0_step1:  while (TRUE) do
  
\* Monitor.TryEnter(mutex)) 
T0_step2:    if ((holder1 = 0) \/ (mutex1 = 0)) then
               \* if it is free or T0 is the holder
               mutex1 := mutex1 + 1;
               holder1 := 0;

\* Monitor.Enter(mutex3);
T0_step3:      await ((holder3 = 0) \/ (mutex3 = 0));
               \* difference is that we don't "try", we just enter
               holder3 := 0;
               mutex3 := mutex3 + 1;
  
\* Monitor.Enter(mutex);
T0_step4:      await ((holder1 = 0) \/ (mutex1 = 0));
               mutex1 := mutex1 + 1;
               holder1 := 0;

\* critical_section();
T0_step5:      skip;    
    
\* Monitor.Exit(mutex);
T0_step6:      mutex1 := mutex1 - 1;
               if (mutex1 = 0) then
                 holder1 := 2;
               end if; 
  
\* Monitor.Enter(mutex2);
T0_step7:      await ((holder2 = 0) \/ (mutex2 = 0));
               holder2 := 0;
               mutex2 := mutex2 + 1;              
    
\* flag = false;
T0_step8:      flag := FALSE;
  
\* Monitor.Exit(mutex2);
T0_step9:      mutex2 := mutex2 - 1;
               if (mutex2 = 0) then
                 holder2 := 2;
               end if; 
  
\* Monitor.Exit(mutex3);
T0_step10:     mutex3 := mutex3 - 1;
               if (mutex3 = 0) then
                 holder3 := 3;
               end if; 
             
             else
  
\* Monitor.Enter(mutex2);
T0_step11:     await ((holder2 = 0) \/ (mutex2 = 0));
               mutex2 := mutex2 + 1;
               holder2 := 0;

\* flag = true;
T0_step12:     flag := TRUE;

\* Monitor.Exit(mutex2);
T0_step13:     mutex2 := mutex2 - 1;
               if (mutex2 = 0) then
                 holder2 := 2;
               end if; 

    end if;
  end while;
end process;


process Thread1 = 1
begin
T1_step1:  while (TRUE) do

\* if (flag)
T1_step2:    if (flag) then

\* Monitor.Enter(mutex2);
T1_step3:      await ((holder2 = 1) \/ (mutex2 = 0));
               mutex2 := mutex2 + 1;
               holder2 := 1;
  
\* Monitor.Enter(mutex);
T1_step4:      await ((holder1 = 1) \/ (mutex1 = 0));
               mutex1 := mutex1 + 1;
               holder1 := 1;
  
\* flag = false;
T1_step5:      flag := FALSE;
  
\* critical_section();
T1_step6:      skip;
  
\* Monitor.Exit(mutex);
T1_step7:      mutex1 := mutex1 - 1;
               if (mutex1 = 0) then
                 holder1 := 2;
               end if; 
  
\* Monitor.Enter(mutex2);
T1_step8:      await ((holder2 = 1) \/ (mutex2 = 0));
               mutex2 := mutex2 + 1;
               holder2 := 1;
             
             else
             
\* Monitor.Enter(mutex);
T1_step9:      await ((holder1 = 1) \/ (mutex1 = 0));
               mutex1 := mutex1 + 1;
               holder1 := 1;
  
\* flag = false;
T1_step10:     flag := FALSE;
  
  
\* Monitor.Exit(mutex);
T1_step11:     mutex1 := mutex1 - 1;
               if (mutex1 = 0) then
                 holder1 := 2;
               end if; 
  
    end if;
  end while;
end process;

end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "a6e25d6d" /\ chksum(tla) = "774e2555")
VARIABLES mutex1, mutex2, mutex3, flag, holder1, holder2, holder3, pc

vars == << mutex1, mutex2, mutex3, flag, holder1, holder2, holder3, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ mutex1 = 0
        /\ mutex2 = 0
        /\ mutex3 = 0
        /\ flag = FALSE
        /\ holder1 = 2
        /\ holder2 = 2
        /\ holder3 = 2
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "T0_step1"
                                        [] self = 1 -> "T1_step1"]

T0_step1 == /\ pc[0] = "T0_step1"
            /\ pc' = [pc EXCEPT ![0] = "T0_step2"]
            /\ UNCHANGED << mutex1, mutex2, mutex3, flag, holder1, holder2, 
                            holder3 >>

T0_step2 == /\ pc[0] = "T0_step2"
            /\ IF ((holder1 = 0) \/ (mutex1 = 0))
                  THEN /\ mutex1' = mutex1 + 1
                       /\ holder1' = 0
                       /\ pc' = [pc EXCEPT ![0] = "T0_step3"]
                  ELSE /\ pc' = [pc EXCEPT ![0] = "T0_step11"]
                       /\ UNCHANGED << mutex1, holder1 >>
            /\ UNCHANGED << mutex2, mutex3, flag, holder2, holder3 >>

T0_step3 == /\ pc[0] = "T0_step3"
            /\ ((holder3 = 0) \/ (mutex3 = 0))
            /\ holder3' = 0
            /\ mutex3' = mutex3 + 1
            /\ pc' = [pc EXCEPT ![0] = "T0_step4"]
            /\ UNCHANGED << mutex1, mutex2, flag, holder1, holder2 >>

T0_step4 == /\ pc[0] = "T0_step4"
            /\ ((holder1 = 0) \/ (mutex1 = 0))
            /\ mutex1' = mutex1 + 1
            /\ holder1' = 0
            /\ pc' = [pc EXCEPT ![0] = "T0_step5"]
            /\ UNCHANGED << mutex2, mutex3, flag, holder2, holder3 >>

T0_step5 == /\ pc[0] = "T0_step5"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![0] = "T0_step6"]
            /\ UNCHANGED << mutex1, mutex2, mutex3, flag, holder1, holder2, 
                            holder3 >>

T0_step6 == /\ pc[0] = "T0_step6"
            /\ mutex1' = mutex1 - 1
            /\ IF (mutex1' = 0)
                  THEN /\ holder1' = 2
                  ELSE /\ TRUE
                       /\ UNCHANGED holder1
            /\ pc' = [pc EXCEPT ![0] = "T0_step7"]
            /\ UNCHANGED << mutex2, mutex3, flag, holder2, holder3 >>

T0_step7 == /\ pc[0] = "T0_step7"
            /\ ((holder2 = 0) \/ (mutex2 = 0))
            /\ holder2' = 0
            /\ mutex2' = mutex2 + 1
            /\ pc' = [pc EXCEPT ![0] = "T0_step8"]
            /\ UNCHANGED << mutex1, mutex3, flag, holder1, holder3 >>

T0_step8 == /\ pc[0] = "T0_step8"
            /\ flag' = FALSE
            /\ pc' = [pc EXCEPT ![0] = "T0_step9"]
            /\ UNCHANGED << mutex1, mutex2, mutex3, holder1, holder2, holder3 >>

T0_step9 == /\ pc[0] = "T0_step9"
            /\ mutex2' = mutex2 - 1
            /\ IF (mutex2' = 0)
                  THEN /\ holder2' = 2
                  ELSE /\ TRUE
                       /\ UNCHANGED holder2
            /\ pc' = [pc EXCEPT ![0] = "T0_step10"]
            /\ UNCHANGED << mutex1, mutex3, flag, holder1, holder3 >>

T0_step10 == /\ pc[0] = "T0_step10"
             /\ mutex3' = mutex3 - 1
             /\ IF (mutex3' = 0)
                   THEN /\ holder3' = 3
                   ELSE /\ TRUE
                        /\ UNCHANGED holder3
             /\ pc' = [pc EXCEPT ![0] = "T0_step1"]
             /\ UNCHANGED << mutex1, mutex2, flag, holder1, holder2 >>

T0_step11 == /\ pc[0] = "T0_step11"
             /\ ((holder2 = 0) \/ (mutex2 = 0))
             /\ mutex2' = mutex2 + 1
             /\ holder2' = 0
             /\ pc' = [pc EXCEPT ![0] = "T0_step12"]
             /\ UNCHANGED << mutex1, mutex3, flag, holder1, holder3 >>

T0_step12 == /\ pc[0] = "T0_step12"
             /\ flag' = TRUE
             /\ pc' = [pc EXCEPT ![0] = "T0_step13"]
             /\ UNCHANGED << mutex1, mutex2, mutex3, holder1, holder2, holder3 >>

T0_step13 == /\ pc[0] = "T0_step13"
             /\ mutex2' = mutex2 - 1
             /\ IF (mutex2' = 0)
                   THEN /\ holder2' = 2
                   ELSE /\ TRUE
                        /\ UNCHANGED holder2
             /\ pc' = [pc EXCEPT ![0] = "T0_step1"]
             /\ UNCHANGED << mutex1, mutex3, flag, holder1, holder3 >>

Thread0 == T0_step1 \/ T0_step2 \/ T0_step3 \/ T0_step4 \/ T0_step5
              \/ T0_step6 \/ T0_step7 \/ T0_step8 \/ T0_step9 \/ T0_step10
              \/ T0_step11 \/ T0_step12 \/ T0_step13

T1_step1 == /\ pc[1] = "T1_step1"
            /\ pc' = [pc EXCEPT ![1] = "T1_step2"]
            /\ UNCHANGED << mutex1, mutex2, mutex3, flag, holder1, holder2, 
                            holder3 >>

T1_step2 == /\ pc[1] = "T1_step2"
            /\ IF (flag)
                  THEN /\ pc' = [pc EXCEPT ![1] = "T1_step3"]
                  ELSE /\ pc' = [pc EXCEPT ![1] = "T1_step9"]
            /\ UNCHANGED << mutex1, mutex2, mutex3, flag, holder1, holder2, 
                            holder3 >>

T1_step3 == /\ pc[1] = "T1_step3"
            /\ ((holder2 = 1) \/ (mutex2 = 0))
            /\ mutex2' = mutex2 + 1
            /\ holder2' = 1
            /\ pc' = [pc EXCEPT ![1] = "T1_step4"]
            /\ UNCHANGED << mutex1, mutex3, flag, holder1, holder3 >>

T1_step4 == /\ pc[1] = "T1_step4"
            /\ ((holder1 = 1) \/ (mutex1 = 0))
            /\ mutex1' = mutex1 + 1
            /\ holder1' = 1
            /\ pc' = [pc EXCEPT ![1] = "T1_step5"]
            /\ UNCHANGED << mutex2, mutex3, flag, holder2, holder3 >>

T1_step5 == /\ pc[1] = "T1_step5"
            /\ flag' = FALSE
            /\ pc' = [pc EXCEPT ![1] = "T1_step6"]
            /\ UNCHANGED << mutex1, mutex2, mutex3, holder1, holder2, holder3 >>

T1_step6 == /\ pc[1] = "T1_step6"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![1] = "T1_step7"]
            /\ UNCHANGED << mutex1, mutex2, mutex3, flag, holder1, holder2, 
                            holder3 >>

T1_step7 == /\ pc[1] = "T1_step7"
            /\ mutex1' = mutex1 - 1
            /\ IF (mutex1' = 0)
                  THEN /\ holder1' = 2
                  ELSE /\ TRUE
                       /\ UNCHANGED holder1
            /\ pc' = [pc EXCEPT ![1] = "T1_step8"]
            /\ UNCHANGED << mutex2, mutex3, flag, holder2, holder3 >>

T1_step8 == /\ pc[1] = "T1_step8"
            /\ ((holder2 = 1) \/ (mutex2 = 0))
            /\ mutex2' = mutex2 + 1
            /\ holder2' = 1
            /\ pc' = [pc EXCEPT ![1] = "T1_step1"]
            /\ UNCHANGED << mutex1, mutex3, flag, holder1, holder3 >>

T1_step9 == /\ pc[1] = "T1_step9"
            /\ ((holder1 = 1) \/ (mutex1 = 0))
            /\ mutex1' = mutex1 + 1
            /\ holder1' = 1
            /\ pc' = [pc EXCEPT ![1] = "T1_step10"]
            /\ UNCHANGED << mutex2, mutex3, flag, holder2, holder3 >>

T1_step10 == /\ pc[1] = "T1_step10"
             /\ flag' = FALSE
             /\ pc' = [pc EXCEPT ![1] = "T1_step11"]
             /\ UNCHANGED << mutex1, mutex2, mutex3, holder1, holder2, holder3 >>

T1_step11 == /\ pc[1] = "T1_step11"
             /\ mutex1' = mutex1 - 1
             /\ IF (mutex1' = 0)
                   THEN /\ holder1' = 2
                   ELSE /\ TRUE
                        /\ UNCHANGED holder1
             /\ pc' = [pc EXCEPT ![1] = "T1_step1"]
             /\ UNCHANGED << mutex2, mutex3, flag, holder2, holder3 >>

Thread1 == T1_step1 \/ T1_step2 \/ T1_step3 \/ T1_step4 \/ T1_step5
              \/ T1_step6 \/ T1_step7 \/ T1_step8 \/ T1_step9 \/ T1_step10
              \/ T1_step11

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Thread0 \/ Thread1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 



(***************************************************************************)
(* The following formula asserts that no two processes are in the        *)
(* critcal sections at the same time.                                    *)
(***************************************************************************)
MutualExclusion == {pc[0], pc[1]} # {"T0_step5", "T1_step6"}


=============================================================================
\* Modification History
\* Last modified Tue Apr 27 01:14:27 MSK 2021 by Elena
\* Created Mon Apr 26 01:02:40 MSK 2021 by Elena

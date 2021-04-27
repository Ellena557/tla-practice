--------------------------- MODULE TripleDanger ---------------------------

EXTENDS Integers, TLC

(* --algorithm xp
variables
  conduit = "";
  energyBursts = 3;
  
process Sorcerer = 0
begin
Sorcerer_1:  while (TRUE) do

\* Monitor.Enter(conduit);
Sorcerer_2:    await (conduit = "");
               conduit := "Sorcerer";

\* energyBursts.Enqueue(new EnergyBurst());
Sorcerer_3:    energyBursts := energyBursts + 1;

\* Monitor.Exit(conduit);
Sorcerer_4:    conduit := "";

  end while;
end process;

process Electricity = 1
begin
Electricity_1:   while (TRUE) do

\* if (energyBursts.Count > 0) 
Electricity_2:     if  energyBursts > 0 then

\* Monitor.Enter(conduit);
Electricity_3:     await (conduit = "");
                   conduit := "Electricity";

\*energyBursts.Dequeue();
Electricity_4:     energyBursts := energyBursts - 1;

\* lightning_bolts(terrifying: true) (does not affect parallelism)
Electricity_5:     skip;

\* Monitor.Exit(conduit);
Electricity_6:     conduit := ""; 

    end if;
  end while;
end process;

process Fire = 2
begin
Fire_1:    while (TRUE) do

\* if (energyBursts.Count > 0) 
Fire_2:      if  energyBursts > 0 then
 
\* Monitor.Enter(conduit);
Fire_3:      await (conduit = "");
             conduit := "Fire";

\* energyBursts.Dequeue();
Fire_4:      energyBursts := energyBursts - 1;

\* fireball(mighty: true);
Fire_5:      skip;

\* Monitor.Exit(conduit);
Fire_6:      conduit := ""; 

    end if;
  end while;
end process;


end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "58cd5310" /\ chksum(tla) = "18fe4fe")
VARIABLES conduit, energyBursts, pc

vars == << conduit, energyBursts, pc >>

ProcSet == {0} \cup {1} \cup {2}

Init == (* Global variables *)
        /\ conduit = ""
        /\ energyBursts = 3
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "Sorcerer_1"
                                        [] self = 1 -> "Electricity_1"
                                        [] self = 2 -> "Fire_1"]

Sorcerer_1 == /\ pc[0] = "Sorcerer_1"
              /\ pc' = [pc EXCEPT ![0] = "Sorcerer_2"]
              /\ UNCHANGED << conduit, energyBursts >>

Sorcerer_2 == /\ pc[0] = "Sorcerer_2"
              /\ (conduit = "")
              /\ conduit' = "Sorcerer"
              /\ pc' = [pc EXCEPT ![0] = "Sorcerer_3"]
              /\ UNCHANGED energyBursts

Sorcerer_3 == /\ pc[0] = "Sorcerer_3"
              /\ energyBursts' = energyBursts + 1
              /\ pc' = [pc EXCEPT ![0] = "Sorcerer_4"]
              /\ UNCHANGED conduit

Sorcerer_4 == /\ pc[0] = "Sorcerer_4"
              /\ conduit' = ""
              /\ pc' = [pc EXCEPT ![0] = "Sorcerer_1"]
              /\ UNCHANGED energyBursts

Sorcerer == Sorcerer_1 \/ Sorcerer_2 \/ Sorcerer_3 \/ Sorcerer_4

Electricity_1 == /\ pc[1] = "Electricity_1"
                 /\ pc' = [pc EXCEPT ![1] = "Electricity_2"]
                 /\ UNCHANGED << conduit, energyBursts >>

Electricity_2 == /\ pc[1] = "Electricity_2"
                 /\ IF energyBursts > 0
                       THEN /\ pc' = [pc EXCEPT ![1] = "Electricity_3"]
                       ELSE /\ pc' = [pc EXCEPT ![1] = "Electricity_1"]
                 /\ UNCHANGED << conduit, energyBursts >>

Electricity_3 == /\ pc[1] = "Electricity_3"
                 /\ (conduit = "")
                 /\ conduit' = "Electricity"
                 /\ pc' = [pc EXCEPT ![1] = "Electricity_4"]
                 /\ UNCHANGED energyBursts

Electricity_4 == /\ pc[1] = "Electricity_4"
                 /\ energyBursts' = energyBursts - 1
                 /\ pc' = [pc EXCEPT ![1] = "Electricity_5"]
                 /\ UNCHANGED conduit

Electricity_5 == /\ pc[1] = "Electricity_5"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![1] = "Electricity_6"]
                 /\ UNCHANGED << conduit, energyBursts >>

Electricity_6 == /\ pc[1] = "Electricity_6"
                 /\ conduit' = ""
                 /\ pc' = [pc EXCEPT ![1] = "Electricity_1"]
                 /\ UNCHANGED energyBursts

Electricity == Electricity_1 \/ Electricity_2 \/ Electricity_3
                  \/ Electricity_4 \/ Electricity_5 \/ Electricity_6

Fire_1 == /\ pc[2] = "Fire_1"
          /\ pc' = [pc EXCEPT ![2] = "Fire_2"]
          /\ UNCHANGED << conduit, energyBursts >>

Fire_2 == /\ pc[2] = "Fire_2"
          /\ IF energyBursts > 0
                THEN /\ pc' = [pc EXCEPT ![2] = "Fire_3"]
                ELSE /\ pc' = [pc EXCEPT ![2] = "Fire_1"]
          /\ UNCHANGED << conduit, energyBursts >>

Fire_3 == /\ pc[2] = "Fire_3"
          /\ (conduit = "")
          /\ conduit' = "Fire"
          /\ pc' = [pc EXCEPT ![2] = "Fire_4"]
          /\ UNCHANGED energyBursts

Fire_4 == /\ pc[2] = "Fire_4"
          /\ energyBursts' = energyBursts - 1
          /\ pc' = [pc EXCEPT ![2] = "Fire_5"]
          /\ UNCHANGED conduit

Fire_5 == /\ pc[2] = "Fire_5"
          /\ TRUE
          /\ pc' = [pc EXCEPT ![2] = "Fire_6"]
          /\ UNCHANGED << conduit, energyBursts >>

Fire_6 == /\ pc[2] = "Fire_6"
          /\ conduit' = ""
          /\ pc' = [pc EXCEPT ![2] = "Fire_1"]
          /\ UNCHANGED energyBursts

Fire == Fire_1 \/ Fire_2 \/ Fire_3 \/ Fire_4 \/ Fire_5 \/ Fire_6

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Sorcerer \/ Electricity \/ Fire
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

energyBurstsPositive == energyBursts >= 0

=============================================================================
\* Modification History
\* Last modified Tue Apr 27 20:30:10 MSK 2021 by Elena
\* Created Mon Apr 26 19:02:40 MSK 2021 by Elena

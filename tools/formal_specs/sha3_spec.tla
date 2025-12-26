(* SPDX-FileCopyrightText: 2025 Rhett Creighton
 * SPDX-License-Identifier: Apache-2.0
 *)

---------------------------- MODULE SHA3Spec ----------------------------
(* Formal specification of SHA3-256 in TLA+ *)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS 
    StateWidth,      \* 1600 bits for Keccak-f[1600]
    Rate,           \* 1088 bits for SHA3-256
    Capacity,       \* 512 bits for SHA3-256
    OutputLength    \* 256 bits for SHA3-256

ASSUME StateWidth = 1600
ASSUME Rate = 1088
ASSUME Capacity = 512
ASSUME OutputLength = 256
ASSUME StateWidth = Rate + Capacity

VARIABLES
    state,          \* Current Keccak state (1600 bits)
    message,        \* Input message
    phase,          \* Current phase: "absorbing", "squeezing", "done"
    absorbed,       \* Number of bits absorbed so far
    squeezed,       \* Number of bits squeezed so far
    output          \* Final hash output

TypeInvariant ==
    /\ state \in [1..StateWidth -> {0, 1}]
    /\ message \in Seq({0, 1})
    /\ phase \in {"absorbing", "squeezing", "done"}
    /\ absorbed \in 0..Len(message)
    /\ squeezed \in 0..OutputLength
    /\ output \in Seq({0, 1})
    /\ Len(output) <= OutputLength

Init ==
    /\ state = [i \in 1..StateWidth |-> 0]
    /\ message \in Seq({0, 1})  \* Arbitrary message
    /\ phase = "absorbing"
    /\ absorbed = 0
    /\ squeezed = 0
    /\ output = <<>>

(* Keccak-f permutation - simplified model *)
KeccakF(s) ==
    \* In reality, this is 24 rounds of 5 steps each
    \* Here we model it as a bijective function
    LET 
        \* Theta step effect
        ThetaEffect(st) == [i \in DOMAIN st |-> 
            IF i % 5 = 0 THEN st[i] ELSE (st[i] + 1) % 2]
        \* Other steps abstracted
        Permuted == ThetaEffect(s)
    IN Permuted

(* Pad the message according to SHA3 padding rule *)
PadMessage(msg) ==
    LET
        msgLen == Len(msg)
        \* SHA3 uses pad10*1: append 01, then 0s, then 1
        padLen == Rate - (msgLen % Rate)
        padding == <<0, 1>> \o [i \in 1..(padLen-3) |-> 0] \o <<1>>
    IN msg \o padding

(* XOR a block into the state *)
XORIntoState(st, block) ==
    [i \in DOMAIN st |->
        IF i <= Len(block) 
        THEN (st[i] + block[i]) % 2
        ELSE st[i]]

(* Extract a block from the state *)
ExtractFromState(st, length) ==
    [i \in 1..length |-> st[i]]

(* Absorb one block *)
AbsorbBlock ==
    /\ phase = "absorbing"
    /\ absorbed < Len(message)
    /\ LET
        remaining == Len(message) - absorbed
        blockSize == IF remaining >= Rate THEN Rate ELSE remaining
        block == [i \in 1..blockSize |-> message[absorbed + i]]
        paddedBlock == IF remaining < Rate 
                       THEN PadMessage(block)
                       ELSE block
        newState == KeccakF(XORIntoState(state, paddedBlock))
       IN
        /\ state' = newState
        /\ absorbed' = absorbed + blockSize
        /\ IF absorbed' = Len(message)
           THEN phase' = "squeezing"
           ELSE phase' = phase
        /\ UNCHANGED <<message, squeezed, output>>

(* Squeeze one block *)
SqueezeBlock ==
    /\ phase = "squeezing"
    /\ squeezed < OutputLength
    /\ LET
        remaining == OutputLength - squeezed
        blockSize == IF remaining >= Rate THEN Rate ELSE remaining
        block == ExtractFromState(state, blockSize)
       IN
        /\ output' = output \o block
        /\ squeezed' = squeezed + blockSize
        /\ IF squeezed' = OutputLength
           THEN phase' = "done"
           ELSE /\ phase' = phase
                /\ state' = KeccakF(state)
        /\ UNCHANGED <<message, absorbed>>

(* Complete specification *)
Next ==
    \/ AbsorbBlock
    \/ SqueezeBlock
    \/ (phase = "done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

(* Properties *)

(* Property 1: The algorithm terminates *)
Termination == <>(phase = "done")

(* Property 2: Output has correct length *)
OutputLength == [](phase = "done" => Len(output) = OutputLength)

(* Property 3: Deterministic - same message produces same hash *)
Deterministic ==
    \A m1, m2 \in Seq({0, 1}):
        (m1 = m2) => 
        LET
            h1 == SHA3Hash(m1)
            h2 == SHA3Hash(m2)
        IN h1 = h2

(* Property 4: Collision resistance (computational, not verifiable) *)
(* For formal verification, we check weaker properties *)

(* Property 5: Absorbing completes before squeezing *)
PhaseOrdering ==
    [](phase = "squeezing" => absorbed = Len(message))

(* Property 6: State is always valid *)
StateValid ==
    []TypeInvariant

====================================================================
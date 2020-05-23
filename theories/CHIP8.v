Require Import Coq.Init.Byte Coq.Strings.Byte Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.
Import BvectorNotations.

From CHIP8 Require Import HelperDataTypes.
From CHIP8 Require Import MainMemory.
From CHIP8 Require Import MainSystem.
From CHIP8 Require Import InstructionSet.

(*
 We'll be using bytes. Instructions are 2 bytes long and memory/instructions are stored in big-endian format.
 
 Caution: coq bytes are stored in little endian format
 
 - Modelling this machine requires several components:
    - Modelling main memory (Sounds easy, list of bytes?).
    - Modelling the stack (We've also done this before).
    - Modelling "GPU" memory (Even if I don't think there's a way to display it on Coq, we still need it for some instructions.
    - Modelling the instruction set (We can write the equivalent of exec that we've been using in class.
    - Modelling the "CPU" (Hardest part for sure):
        - Modelling the 16 registers (V0-VF) and the I register.
        - Modellling the Program Counter.
        - Modelling the timer registers (Don't see how it's possible).
        - Modelling input (Also not sure).

 For more info see https://en.wikipedia.org/wiki/CHIP-8.
*)

Definition test := write_memory x10 1 init_memory.
Definition test2 := write_memory x23 3 test.

Compute map to_nat (firstn 10 test2).

Definition registersStart := init_memory' 16.
Definition registersWritten := write_memory x99 0 registersStart.
(*
Compute registersStart.
Compute registersWritten.
Compute exec'' (x82, x00) registersWritten.
Compute exec'' (x00, x00) registersStart.

(*Check or*)
Definition registersWrittenTwice := write_memory x8f 1 registersWritten.
Compute registersWrittenTwice.

Compute exec'' (x80, x13) registersWrittenTwice.

(* Adding NN to vX. Example with and without overflow*)
Compute map to_nat (exec'' (x71, x01) (exec'' (x61, x09) registersStart)).
Compute map to_nat (exec'' (x71, xff) (exec'' (x61, x02) registersStart)).

(*I8XY4 - Add v1 to v0 *)
(*With overflow*)
Compute map to_nat registersWrittenTwice.
Compute map to_nat (exec'' (x80, x14) registersWrittenTwice).

(*Without overflow*)
Compute map to_nat (exec'' (x61, x09) registersStart).
Compute map to_nat (exec'' (x80, x14) (exec'' (x61, x09) registersStart)).
*)
Import MainSystem.
Definition startingState := makeCHIP8 (x00,x00) (x00,x00) registersStart ((x10, x10) :: []) 0 [].

(* Set PC to x303*)
Compute I1NNN (x13, x03) startingState.

(* Testing record update functions *)
Compute setPC (x40, x40) startingState.

(* Address in the stack is 0x0505. If we pop it we should get our PC = x0505
    Note - the stack list isn't cleared. It's technically not needed because we would overwrite it when we next push
    but still it's worth looking into if it's needed. Nothing else looks at the stack except the push/pop functions
*)
Definition poppableState := makeCHIP8 (x00,x00) (x00,x00) registersStart [(x05, x05)] 1 [].

Compute popStack poppableState.

(*Pushes the current PC (x00,x00) into the stack 
 overwritting the (x10,x10) that was there previously*)
Compute pushStack startingState.

(* 2NNN - Testing it. *)
Compute I2NNN (x20,x12) startingState.
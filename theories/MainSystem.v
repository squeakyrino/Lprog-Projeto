Require Import Coq.Init.Byte Coq.Strings.Byte Coq.Bool.Bvector Coq.Lists.List Coq.Init.Nat.

From CHIP8 Require Import MainMemory.
From CHIP8 Require Import HelperDataTypes.
From RecordUpdate Require Import RecordSet.

(*Everything is stored in big-endian format*)
Record CHIP8 : Set := makeCHIP8  {
  pc : (byte * byte); (* Program Counter *)
  i : (byte * byte);  (* I register *)
  registers : list byte; (* 16 registers - TODO check if we can limit the length to be 16 always*)
  stack : list (byte * byte); (* 16 level stack *)
  stackPointer : nat;
  ram : list byte; (* Program instructions*) 
}.

(* This is needed for the record update library *)
Instance etaX : Settable _ := settable! makeCHIP8 <pc; i; registers; stack; stackPointer; ram>.

Import RecordSetNotations.

(* Record update helper functions *)
(*Set PC to a. PC should be of the form (x0N, xNN)*)
Definition setPC a x := x <|pc := a|>.

(*Increment PC by 2. This is just a useful to have*)
Definition incrementPCBy2 x := x <|pc := nat_to_word_be (add (word_to_nat_be x.(pc)) 2)|>.

(*Set the I register *)
Definition setIRegister val x := x <|i := val|>.

(*Update the registers*)
Definition  updateRegisters registers' x := x <|registers := registers'|>.

(*popStack: decrements the stackPointer and puts the program counter equals to the value popped*)
Definition popStack x := x <|stackPointer ::= sub 1|> 
                           <|pc := nth (sub 1 (x.(stackPointer))) x.(stack) (xde, xad)|>.

(*Push the current PC into the stack and then increase stackpointer*)
Definition pushStack (x : CHIP8) := x <|stackPointer ::= succ|> 
                            <|stack := write_memory x.(pc) x.(stackPointer) x.(stack)|>.

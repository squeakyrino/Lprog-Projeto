Require Import Coq.Init.Byte Coq.Strings.Byte Coq.Bool.Bvector.

From CHIP8 Require Import MainMemory.
From CHIP8 Require Import HelperDataTypes.
From RecordUpdate Require Import RecordSet.

Record CHIP8 : Set := makeCHIP8  {
  pc : (byte * byte); (* Program Counter *)
  i : (byte * byte);  (* I register *)
  registers : list byte; (* 16 registers - TODO check if we can limit the length to be 16 always*)
  stack : list (byte * byte); (* 16 level stack *)
  stackPointer : nat;
  ram : list byte; (* Program instructions*) 
}.

Import RecordSetNotations.

(* Record update helper functions *)
Definition setPC a x := x <|pc := a|>.

Definition popStack x := x <|stackPointer ::= sub 1|> <|pc := nth (sub 1 (x.(stackPointer))) x.(stack) (xde, xad)|>.

(*Update stack and then increase update stackpointer*)
Definition pushStack (address : (byte * byte)) x := x <|stackPointer ::= succ|> 
                                                      <|stack := write_memory address x.(stackPointer) x.(stack)|>.
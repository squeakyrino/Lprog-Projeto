Require Import Coq.Init.Byte Coq.Strings.Byte Coq.Bool.Bvector Coq.Lists.List Coq.Init.Nat.

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

(* This is needed for the record update library *)
Instance etaX : Settable _ := settable! makeCHIP8 <pc; i; registers; stack; stackPointer; ram>.

Import RecordSetNotations.

(* Record update helper functions *)
Definition setPC a x := x <|pc := a|>.

Definition popStack x := x <|stackPointer ::= sub 1|> <|pc := nth (sub 1 (x.(stackPointer))) x.(stack) (xde, xad)|>.

(*Push the current PC into the stacl and then increase stackpointer*)
Definition pushStack x := x <|stackPointer ::= succ|> 
                            <|stack := write_memory x.(pc) x.(stackPointer) x.(stack)|>.
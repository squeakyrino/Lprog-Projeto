Require Import Coq.Init.Byte Coq.Strings.Byte Coq.Bool.Bvector.

From CHIP8 Require Import MainMemory.
From CHIP8 Require Import HelperDataTypes.

Record CHIP8 : Set := makeCHIP8  {
  pc : (byte * byte); (* Program Counter *)
  i : (byte * byte);  (* I register *)
  registers : list byte; (* 16 registers - TODO check if we can limit the length to be 16 always*)
  stack : list byte; (* 16 level stack *)
  stackPointer : nat;
  ram : list byte; (* Program instructions*) 
}.

Require Import Coq.Init.Byte Coq.Strings.Byte Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.

Fixpoint create_list {A : Type} (default : A) (n : nat) : list A :=
  match n with
    |0 => []
    |S n' => default :: create_list default n'
  end.

Fixpoint init_memory' (n : nat) : list byte :=
  create_list (x00) n.

Definition init_memory : list byte :=
  init_memory'  4096.

(* Reading memory is done by using the nth function *)

Fixpoint write_memory {A : Type}(data : A) (address : nat) (ram : list A) : list A :=
  match address, ram with
    |0, head :: tail => data :: tail
    |0, [] => []
    |S address', [] => []
    |S address', head :: tail => head :: write_memory data address' tail
  end.
  
Definition write_instruction (inst : byte * byte) (address : nat) (ram : list byte) : list byte :=
  match inst with
  | (b1, b2) =>
    write_memory b2 (S(address)) (write_memory b1 address ram)
  end.

Fixpoint write_all_instructions (insts : list (byte * byte)) (address : nat) (ram : list byte) : list byte :=
  match insts with
  | []              => ram
  | inst::insts' =>
    let new_ram := write_instruction inst address ram in
    write_all_instructions insts' (S(S(address))) new_ram
  end.


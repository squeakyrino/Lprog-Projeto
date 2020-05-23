Require Import Coq.Init.Byte Coq.Strings.Byte Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.

Fixpoint init_memory' (n : nat) : list byte :=
  match n with
    |0 => []
    |S n' => x00 :: init_memory' n'
  end.

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
  

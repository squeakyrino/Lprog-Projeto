Require Import Coq.Init.Byte Coq.Strings.Byte.
From CHIP8 Require Import InstructionSet.
From CHIP8 Require Import HelperDataTypes.
From CHIP8 Require Import MainMemory.
From CHIP8 Require Import MainSystem.

Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Import InstructionSetNotation.

Fixpoint fibonacci_aux a b c :=
  match c with
  | 0 => a
  | S c' => fibonacci_aux (b) (a+b) c'
  end.

Fixpoint fibonacci n :=
  fibonacci_aux 0 1 n.

Definition fibonacci_n_chip8 n :=
  ( ( v1 := n0 ::: n0 ) ;; (*value of a : n0*)
    ( v2 := n0 ::: n1 ) ;; (*value of b : n2*)
    ( v3 := n0 ::: n ) ;; (*value to reach : n4*)
    ( v4 := n0 ::: n0 ) ;; (*value of counter : n6*)
    (* Start of program *)
    ( skip if v4 equal to v3 ) (*if equal go to end : n8*) ;;
    ( jump to n2 ::: n0 ::: ne ) (* jump to procedure : na*) ;;
    ( ret ) (* return point : nc *) ;;
    ( v4 :=+ n0 ::: n1 ) ;;
    ( v5 := v2 ) ;;
    ( v2 :=+ v1 ) ;;
    ( v1 := v5) ;; 
    ( jump to n2 ::: n0 ::: n8 ) 
  ).

Definition CHIP_prog prog :=
  updateRam (prog 512 init_memory) CHIP8InitialStateEmptyRam.

Example fib_prog : forall n,
    Some (nth 1 (exec_step (CHIP_prog (fibonacci_n_chip8 n)) 300).(registers) x00)
    =
    of_nat (modulo (fibonacci (n_to_nat n)) 256).
Proof.
  intros n. destruct n eqn:E ; reflexivity.
Qed.




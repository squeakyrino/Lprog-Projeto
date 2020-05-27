Require Import Coq.Init.Byte Coq.Strings.Byte.
From CHIP8 Require Import InstructionSet.
From CHIP8 Require Import HelperDataTypes.
From CHIP8 Require Import MainMemory.
From CHIP8 Require Import MainSystem.

Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.omega.Omega.

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
    ( jump to n2 ::: n0 ::: nc ) (* return point : nc *) ;;
    ( v4 :=+ n0 ::: n1 ) ;;
    ( v5 := v2 ) ;;
    ( v2 :=+ v1 ) ;;
    ( v1 := v5) ;; 
    ( jump to n2 ::: n0 ::: n8 ) 
  ).

Definition CHIP_prog prog :=
  updateRam (prog 512 init_memory) CHIP8InitialStateEmptyRam.

Example fib_prog0 : forall s, exists s',
    s > s' ->
    Some (nth 1 (exec_step (CHIP_prog (fibonacci_n_chip8 n0)) s).(registers) x00)
    =
    of_nat (modulo (fibonacci (n_to_nat n0)) 256).
Proof.
  intros s.
  exists 4. intros.
  induction H.
  + reflexivity.
  + do 5 (destruct m ; try lia).
    assumption.    
Qed.

Example fib_prog1 : forall s, exists s',
    s > s' ->
    Some (nth 1 (exec_step (CHIP_prog (fibonacci_n_chip8 n1)) s).(registers) x00)
    =
    of_nat (modulo (fibonacci (n_to_nat n1)) 256).
Proof.
  intros s.
  exists 12. intros.
  induction H.
  + reflexivity.
  + do 13 (destruct m ; try omega).
    assumption.    
Qed.

Example fib_prog2 : forall s n, exists s',
    s > s' ->
    Some (nth 1 (exec_step (CHIP_prog (fibonacci_n_chip8 n)) s).(registers) x00)
    =
    of_nat (modulo (fibonacci (n_to_nat n)) 256).
Proof.
  intros s n.
  exists (4 + 8* (n_to_nat n)). intros.
  induction H.
  + destruct n ; reflexivity.
  + destruct n eqn: E; simpl in H.                        
    - do 5 (destruct m ; try omega).
      assumption.    
    - do 13 (destruct m ; try omega).
      assumption. 
    - do 21 (destruct m ; try omega).
      assumption.
    - do 29 (destruct m ; try omega).
      assumption. 
    - do 37 (destruct m ; try omega).
      assumption. 
    - do 45 (destruct m ; try omega).
      assumption. 
    - do 53 (destruct m ; try omega).
      assumption. 
    - do 61 (destruct m ; try omega).
      assumption. 
    - do 69 (destruct m ; try omega).
      assumption. 
    - do 77 (destruct m ; try omega).
      assumption. 
    - do 85 (destruct m ; try omega).
      assumption. 
    - do 93 (destruct m ; try omega).
      assumption. 
    - do 101 (destruct m ; try omega).
      assumption. 
    - do 109 (destruct m ; try omega).
      assumption. 
    - do 117 (destruct m ; try omega).
      assumption. 
    - do 125 (destruct m ; try omega).
      assumption. 
Qed.

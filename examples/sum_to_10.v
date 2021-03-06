Require Import Coq.Init.Byte Coq.Strings.Byte.
From CHIP8 Require Import InstructionSet.
From CHIP8 Require Import HelperDataTypes.
From CHIP8 Require Import MainMemory.
From CHIP8 Require Import MainSystem.
Require Import Coq.Lists.List.

Import InstructionSetNotation.


Check CHIP8InitialStateEmptyRam.

Definition sum_to_10 :=
  ( ( v1 := n0 ::: n0 ) ;; (*counter : n0*)
    ( v2 := n0 ::: na ) ;; (*sum to 10 : n2*)
    ( v3 := n0 ::: n0 ) ;; (*sum : n4*)
    ( v1 :=+ n0 ::: n1 ) ;; (*update counter*)
    ( v3 :=+ v1 ) ;; (*add v1 to v3 : n6*)
    ( skip if v1 equal to v2 ) ;;
    ( jump to n2 ::: n0 ::: n6 ) ;;
    ( ret ) (*exit?*)
  ).

Definition CHIP_prog prog :=
  updateRam (prog 512 init_memory) CHIP8InitialStateEmptyRam.

Example sum_to_10_prog :
      (nth 3 (exec_step (CHIP_prog sum_to_10) 41).(registers) x00) = x37.
Proof.
  reflexivity.
Qed.

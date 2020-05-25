
From CHIP8 Require Import InstructionSet.
From CHIP8 Require Import HelperDataTypes.
Import InstructionSetNotation.


Definition sum_to_10 start_addr :=
  ( ( v0 := start_addr ) ;;
    ( v1 := n0 ::: n0   ) ;; (*counter : n0*)
    ( v2 := n0 ::: na   ) ;; (*sum to 10 : n2*)
    ( v3 := n0 ::: n0   ) ;; (*sum : n4*)
    ( v3 :=+ v1     ) ;; (*add v1 to v3 : n6*)
    ( v1 :=+ n0 ::: n1  ) ;; (*update counter*)
    ( jumpv0 to n0 ::: n0 ::: n6 ) ;;
    ( ret ) (*exit?*)
  ).

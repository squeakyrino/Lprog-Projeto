Require Import Coq.Init.Byte Coq.Strings.Byte Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.
Import BvectorNotations.

From CHIP8 Require Import HelperDataTypes.
From CHIP8 Require Import MainMemory.
From CHIP8 Require Import MainSystem.

(*00EE - Returns from a subroutine. (Also increment the PC)*)
Definition I00EE (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
    incrementPCBy2 (popStack system).


(*1NNN - Jumps to address NNN. Using record update*)
Definition I1NNN (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let newB1 := (n0, n2) in 
                 setPC ((nib_to_byte newB1), b2) system
  end.

(*1NNN - Jumps to address NNN.*)
Definition I1NNN' (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match system with
    |{|pc := pc'; i := i'; registers := registers'; stack := stack'; stackPointer := stackPointer'; ram := ram'|} =>
      match instruction with
        |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                    let newB1 := (n0, n2) in 
                    {|pc := ((nib_to_byte newB1), b2); i := i'; registers := registers'; 
                      stack := stack'; stackPointer := stackPointer'; ram := ram'|}
      end
    end.

(* Proving both functions do the same *) 
Lemma sameI1NNN : forall state instruction,
  I1NNN' instruction state = I1NNN instruction state.
Proof.
intros.
destruct state.
auto.
Qed.

(* 2NNN - Calls subroutine at NNN. *)
Definition I2NNN (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let newB1 := (n0, n2) in 
                 let resultAddress := ((nib_to_byte newB1), b2) in
                 (*Push the current address into the stack and then set PC to the new address*)
                 setPC resultAddress (pushStack system)
  end.


(*6XNN - Sets VX to NN.*)
Definition I6XNN (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 let (n3, n4) := byte_to_nib b2 in
                 let vY := n_to_nat n3 in
                 let updatedRegisters := write_memory b2 vX system.(registers) in
                 updateRegisters updatedRegisters system
  end.   

(*7XNN - 	Adds NN to VX. (Carry flag is not changed)*)
Definition I7XNN (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 (* Another use of nth. Read the value from register VX in nat*)
                 let numVX := to_nat (nth vX system.(registers) x00) in
                 let numNN := to_nat b2 in
                 let addition := modulo (numVX + numNN) 256 in
                   match of_nat addition with
                   (*TODO - there has to be a better way to do this since addition should never be above 256 because of modulo*)
                    |None => system
                    (*write to VX*)
                    |Some x => let updatedRegisters := write_memory x vX system.(registers) in
                                updateRegisters updatedRegisters system
                    end
  end.

(*8XY0 - Sets VX to the value of VY.*)
Definition I8XY0 (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 let (n3, n4) := byte_to_nib b2 in
                 let vY := n_to_nat n3 in
                  (* TODO: nth function requires a default value. I think we should replace it with nth_error for now to help in debugging.*)
                  let updatedRegisters := write_memory (nth vY system.(registers) x00) vX system.(registers) in
                      updateRegisters updatedRegisters system
  end.

(*Sets VX to VX or VY. (Bitwise OR operation) *)
Definition I8XY1 (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 let (n3, n4) := byte_to_nib b2 in
                 let vY := n_to_nat n3 in
                 let register_y_value := (nth vY system.(registers) x00) in 
                 let register_x_value := (nth vX system.(registers) x00) in
                 let y_value_as_Bvector := byte_to_Bvector register_y_value in 
                 let x_value_as_Bvector := byte_to_Bvector register_x_value in
                 let or_x_y_as_Bvector := y_value_as_Bvector ^| x_value_as_Bvector in 
                 let or_x_y_as_byte := Bvector_to_byte or_x_y_as_Bvector in 
                 let updatedRegisters := write_memory or_x_y_as_byte vX system.(registers) in
                 updateRegisters updatedRegisters system
  end.
  
(*I8XY2 - Sets VX to VX and VY. (Bitwise AND operation) *)
Definition I8XY2 (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 let (n3, n4) := byte_to_nib b2 in
                 let vY := n_to_nat n3 in
                 let register_y_value := (nth vY system.(registers) x00) in 
                 let register_x_value := (nth vX system.(registers) x00) in
                 let y_value_as_Bvector := byte_to_Bvector register_y_value in 
                 let x_value_as_Bvector := byte_to_Bvector register_x_value in
                 let and_x_y_as_Bvector := y_value_as_Bvector ^& x_value_as_Bvector in 
                 let and_x_y_as_byte := Bvector_to_byte and_x_y_as_Bvector in 
                 let updatedRegisters := write_memory and_x_y_as_byte vX system.(registers) in
                 updateRegisters updatedRegisters system
  end.
  
(*I8XY3 - Sets VX to VX xor VY.*)
Definition I8XY3 (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 let (n3, n4) := byte_to_nib b2 in
                 let vY := n_to_nat n3 in
                 let register_y_value := (nth vY system.(registers) x00) in 
                 let register_x_value := (nth vX system.(registers) x00) in
                 let y_value_as_Bvector := byte_to_Bvector register_y_value in 
                 let x_value_as_Bvector := byte_to_Bvector register_x_value in
                 let xor_x_y_as_Bvector := BVxor 8 y_value_as_Bvector x_value_as_Bvector in 
                 let xor_x_y_as_byte := Bvector_to_byte xor_x_y_as_Bvector in 
                 let updatedRegisters := write_memory xor_x_y_as_byte vX system.(registers) in
                 updateRegisters updatedRegisters system
  end.

(*8XY4 - Adds VY to VX. VF is set to 1 when there's a carry, and to 0 when there isn't.*)
Definition I8XY4 (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 let (n3, n4) := byte_to_nib b2 in
                 let vY := n_to_nat n3 in
                 (* Another use of nth. Read the value from register VX in nat*)
                 let numVX := to_nat (nth vX system.(registers) x00) in
                 let numVY := to_nat (nth vY system.(registers) x00) in
                 let addition := numVX + numVY in
                 let mod_addition := modulo addition 256 in
                 match of_nat mod_addition with
                              (*TODO - refactor this one out. Think of a better way to structure this*)
                              |None => system
                              |Some x =>  match of_nat addition with
                                          (*If we get a None that means there was overflow, set VF to 1*)
                                          |None => let registersWithoutOF := write_memory x vX (write_memory x01 15 system.(registers)) in
                                                   updateRegisters registersWithoutOF system 
                                          (*Else put VF to 0*)
                                          |Some _ => let registersWithOF := write_memory x vX (write_memory x00 15 system.(registers)) in
                                                     updateRegisters registersWithOF system 
                                          end
                                          
                              
                              end
  end.

(*ANNN - Sets I to the address NNN.*)
Definition IANNN (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let newB1 := (n0, n2) in 
                 let val := ((nib_to_byte newB1), b2) in
                 setIRegister val system
  end.
(*
Fixpoint exec (instruction : byte * byte) (registers : list byte) : list byte :=
  match instruction with
    |(e1, e2) => let (l_nib1, r_nib1) := byte_to_nib' e1 in
                 let (l_nib2, r_nib2) := byte_to_nib' e2 in 
                 (*8XY0 - Much more readable now in my opinion*)
                    if ((nib_eq l_nib1 n8) && (nib_eq r_nib2 n0)) then I8XY0 instruction registers else 
                    if (nib_eq l_nib1 n6) then I6XNN instruction registers else
                    [xde;xad;xbe;xef]
  end.

Fixpoint exec' (instruction : byte * byte) (registers : list byte) : list byte :=
  match instruction with
  |(e1, e2) =>
   match byte_to_nib' e1, byte_to_nib' e2 with
   | (n8,_),(_,n0) => I8XY0 instruction registers
   | (n6,_),(_, _) => I6XNN instruction registers
   |  _    ,    _  => [xde;xad;xbe;xef]
   end
  end.

Theorem exec_equality : forall w lb,
    exec w lb = exec' w lb.
Proof.
  intros ; destruct w.
  unfold exec, exec' ; destruct b ; simpl ; try reflexivity ; 
    try (destruct (byte_to_nib' b0) ; reflexivity) ;
       try (destruct b0 ; reflexivity).
Qed.
*)

Fixpoint exec'' (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
  |(e1, e2) =>
   match byte_to_nib' e1, byte_to_nib' e2 with
   | (n0,n0),(ne,ne) => I00EE instruction system
   | (n1,_),(_,_)  => I1NNN instruction system
   | (n2,_),(_,_)  => I2NNN instruction system
   | (n6,_),(_,_)  => I6XNN instruction system
   | (n7,_),(_,_)  => I7XNN instruction system
   | (n8,_),(_,n0) => I8XY0 instruction system                            
   | (n8,_),(_,n1) => I8XY1 instruction system                          
   | (n8,_),(_,n2) => I8XY2 instruction system                          
   | (n8,_),(_,n3) => I8XY3 instruction system
   | (n8,_),(_,n4) => I8XY4 instruction system
   | (na,_),(_,_)  => IANNN instruction system
   |  _    ,    _  => system
   end
  end.

(*
Fixpoint exec_step (system : CHIP8) (step : nat) : CHIP8 :=
  match nat with
    |O => system
    |S step' => exec_ste  
  *)


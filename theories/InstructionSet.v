Require Import Coq.Init.Byte Coq.Strings.Byte Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

From CHIP8 Require Import HelperDataTypes.
From CHIP8 Require Import MainMemory.
From CHIP8 Require Import MainSystem.

Section InstructionSetCode.

Import BvectorNotations.
  
(*00EE - Returns from a subroutine. (Also increment the PC because the PC we popped is the call instruction)*)
Definition I00EE (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
    incrementPCBy2 (popStack system).


(*1NNN - Jumps to address NNN. Using record update*)
Definition I1NNN (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (_, n2) := byte_to_nib b1 in
                 let truncatedHighByte := nib_to_byte (n0, n2) in 
                 let truncatedNNN := (truncatedHighByte, b2) in
                 setPC truncatedNNN system
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

(* 2NNN - Calls subroutine at NNN. *)
Definition I2NNN (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let newB1 := (n0, n2) in 
                 let resultAddress := ((nib_to_byte newB1), b2) in
                 (*Push the current address into the stack and then set PC to the new address*)
                 setPC resultAddress (pushStack system)
  end.

(*Simple function to avoid duplicating code since the I3XNN and I4XNN do the same but have different boolean conditions.
  This increments the PC already so don't increment the PC on the actual instruction functions*)
Definition I3AndI4Base (func : byte -> byte -> bool) (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
 match instruction with
    |(b1, b2) => let (_, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 (*TODO: another use of default nth*)
                 let byteVX := (nth vX system.(registers) x00) in
                 if func byteVX b2 then
                    (*Passed the boolean check so increment the PC by 4, effectively skipping the next instruction*)
                    incrementPCBy2 (incrementPCBy2 system)
                 else
                 incrementPCBy2 system
  end.

(*3XNN - Skips the next instruction if VX equals NN. (Usually the next instruction is a jump to skip a code block)*)
Definition I3XNN (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
 I3AndI4Base Byte.eqb instruction system.                  

Definition neqb (byte1 byte2 : byte) : bool := negb (Byte.eqb byte1 byte2).
(*4XNN - Skips the next instruction if VX doesn't equal NN. (Usually the next instruction is a jump to skip a code block)*)
Definition I4XNN (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
 I3AndI4Base neqb instruction system.

(*Another function to reduce duplicated code since I5XY0 and I9XY0 do the same but the bool check is different.
  Like the other one, this function already increments the PC so don't increment it in the instruction functions*)
Definition I5AndI9Base (func : byte -> byte -> bool) (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
match instruction with
    |(b1, b2) => let (_, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 (*TODO: another use of default nth*)
                 let byteVX := (nth vX system.(registers) x00) in
                 let (n3,_) := byte_to_nib b2 in
                 let vY := n_to_nat n3 in
                 (*TODO: another use of default nth*)
                 let byteVY := (nth vY system.(registers) x00) in
                 if func byteVX byteVY then
                    (*Passed the boolean check so increment the PC by 4, effectively skipping the next instruction*)
                    incrementPCBy2 (incrementPCBy2 system)
                 else
                    incrementPCBy2 system
  end.

(*5XY0 - Skips the next instruction if VX equals VY. (Usually the next instruction is a jump to skip a code block)*)
Definition I5XY0 (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
 I5AndI9Base Byte.eqb instruction system.

(*6XNN - Sets VX to NN.*)
Definition I6XNN (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 let (n3, n4) := byte_to_nib b2 in
                 let vY := n_to_nat n3 in
                 let updatedRegisters := write_memory b2 vX system.(registers) in
                 incrementPCBy2 (updateRegisters updatedRegisters system)
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
                                  incrementPCBy2 (updateRegisters updatedRegisters system)
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
                      incrementPCBy2 (updateRegisters updatedRegisters system)
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
                 incrementPCBy2 (updateRegisters updatedRegisters system)
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
                 incrementPCBy2 (updateRegisters updatedRegisters system)
  end.
  
(*I8XY3 - Sets VX to VX xor VY.*)
Definition I8XY3 (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (_, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 let (_, n4) := byte_to_nib b2 in
                 let vY := n_to_nat n3 in
                 let register_y_value := (nth vY system.(registers) x00) in 
                 let register_x_value := (nth vX system.(registers) x00) in
                 let y_value_as_Bvector := byte_to_Bvector register_y_value in 
                 let x_value_as_Bvector := byte_to_Bvector register_x_value in
                 let xor_x_y_as_Bvector := BVxor 8 y_value_as_Bvector x_value_as_Bvector in 
                 let xor_x_y_as_byte := Bvector_to_byte xor_x_y_as_Bvector in 
                 let updatedRegisters := write_memory xor_x_y_as_byte vX system.(registers) in
                 incrementPCBy2 (updateRegisters updatedRegisters system)
  end.

(*8XY4 - Adds VY to VX. VF is set to 1 when there's a carry, and to 0 when there isn't.*)
Definition I8XY4 (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
match instruction with
    |(b1, b2) => let (_, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 let (_, n4) := byte_to_nib b2 in
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
                                                   incrementPCBy2 (updateRegisters registersWithoutOF system)
                                          (*Else put VF to 0*)
                                          |Some _ => let registersWithOF := write_memory x vX (write_memory x00 15 system.(registers)) in
                                                     incrementPCBy2 (updateRegisters registersWithOF system) 
                                          end
                                          
                              
                              end
  end.

(*TODO:
  - 8XY5
  - 8XY6
  - 8XY7
  - 8XYE
  *)
  
(*9XY0 - Skips the next instruction if VX doesn't equal VY. (Usually the next instruction is a jump to skip a code block)*)
Definition I9XY0 (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  I5AndI9Base neqb instruction system.

(*ANNN - Sets I to the address NNN.*)
Definition IANNN (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let newB1 := (n0, n2) in 
                 let val := ((nib_to_byte newB1), b2) in
                 incrementPCBy2 (setIRegister val system)
  end.

(*BNNN - Jumps to the address NNN plus V0.*)
Definition IBNNN (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (_, n2) := byte_to_nib b1 in
                 let truncatedHighByte := nib_to_byte (n0, n2) in 
                 let truncatedNNN := (truncatedHighByte, b2) in
                 let truncatedNNNAsNat := word_to_nat_be truncatedNNN in
                  (*Get value of v0 as a nat*)
                 let numVX := to_nat (nth 0 system.(registers) x00) in
                 setPC (nat_to_word_be (truncatedNNNAsNat + numVX)) system
  end.

(*Helper function: writes in memory address I + vX the value of vX*)
Fixpoint writeRegistersInMemory (vX : nat) (system : CHIP8) : CHIP8 :=
  match vX with
          (*TODO: use of nth*)
  |S vX' => let numVX := nth vX' system.(registers) (x00) in
            let address := (word_to_nat_be system.(i)) + vX' in
            let updatedRam := write_memory numVX address system.(ram) in
            let updatedSystem := updateRam updatedRam system in
            writeRegistersInMemory vX' updatedSystem
            
  |0 =>     let numV0 := nth 0 system.(registers) (x00) in
            let address := (word_to_nat_be system.(i)) in
            let updatedRam := write_memory numV0 address system.(ram) in
            let updatedSystem := updateRam updatedRam system in
            updatedSystem
  end.
  
  
  
(*FX55 - Stores V0 to VX (including VX) in memory starting at address I. 
         The offset from I is increased by 1 for each value written.
         In the original CHIP-8 the I register is incremented by 1 everytime we write to memory.
         In the SCHIP implementation the I register is left unmodified.
         This instruction will follow the original CHIP8 implementation*)
Definition IFX55 (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, _) => let (_, n2) := byte_to_nib b1 in
                let counter := (n_to_nat n2) + 1 in
                let newIRegister := nat_to_word_be ((word_to_nat_be system.(i)) + counter) in
                setIRegister newIRegister (writeRegistersInMemory counter system)
  end.

Fixpoint readMemoryToRegisters (vX : nat) (system : CHIP8) : CHIP8 :=
  match vX with
          (*TODO: use of nth*)
  |S vX' => let address := (word_to_nat_be system.(i)) + vX' in
            let memoryByte := nth address system.(ram) (x00) in
            let updatedRegisters := write_memory memoryByte vX' system.(registers) in
            let updatedSystem := updateRegisters updatedRegisters system in
            readMemoryToRegisters vX' updatedSystem
            
  |0 =>     let address := (word_to_nat_be system.(i)) in
            let memoryByte := nth address system.(ram) (x00) in
            let updatedRegisters := write_memory memoryByte 0 system.(registers) in
            let updatedSystem := updateRegisters updatedRegisters system in
            updatedSystem
  end.
  
  
(*FX65 - Fills V0 to VX (including VX) with values from memory starting at address I. 
         The offset from I is increased by 1 for each value written.
         In the original CHIP-8 the I register is incremented by 1 everytime we read from memory.
         In the SCHIP implementation the I register is left unmodified.
         This instruction will follow the original CHIP8 implementation*)
Definition IFX65 (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, _) => let (_, n2) := byte_to_nib b1 in
                let counter := (n_to_nat n2) + 1 in
                let newIRegister := nat_to_word_be ((word_to_nat_be system.(i)) + counter) in
                setIRegister newIRegister (readMemoryToRegisters counter system)
  end. 

Fixpoint exec'' (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
  |(e1, e2) =>
   match byte_to_nib' e1, byte_to_nib' e2 with
   | (n0,n0),(ne,ne) => I00EE instruction system
   | (n1,_),(_,_)  => I1NNN instruction system
   | (n2,_),(_,_)  => I2NNN instruction system
   | (n3,_),(_,_)  => I3XNN instruction system
   | (n4,_),(_,_)  => I4XNN instruction system
   | (n5,_),(_,n0) => I5XY0 instruction system
   | (n6,_),(_,_)  => I6XNN instruction system
   | (n7,_),(_,_)  => I7XNN instruction system
   | (n8,_),(_,n0) => I8XY0 instruction system
   | (n8,_),(_,n1) => I8XY1 instruction system
   | (n8,_),(_,n2) => I8XY2 instruction system
   | (n8,_),(_,n3) => I8XY3 instruction system
   | (n8,_),(_,n4) => I8XY4 instruction system
   | (n9,_),(_,n0) => I9XY0 instruction system
   | (na,_),(_,_)  => IANNN instruction system
   | (nb,_),(_,_)  => IBNNN instruction system
   | (nf,_),(n5,n5)=> IFX55 instruction system
   | (nf,_),(n6,n5)=> IFX65 instruction system
   |  _    ,    _  => system
   end
  end.

(*Exec_step: each full instruction subtracts 1 from the i parameter. Is there a way to know if a program finished?
  Not really. In the original machine, the programs usually just loop forever when they are finished. Unless we define
  our own methodology to simbolise that a program is over it's not really possible.
  There are ways to do it like writting to a place in memory below 0x200 which was reserved in the original system but it's a workaround really*)
Fixpoint exec_step (system : CHIP8) (i : nat) : CHIP8 :=
  match i with
    |O => system
    |S i' => let pcAsNat := word_to_nat_be system.(pc) in
             (*- Read the instruction from memory
                  TODO: use of nth with default*)
             let mSB := nth pcAsNat system.(ram) (x00) in
             let lSB := nth (pcAsNat + 1) system.(ram) (x00) in
             (*Assemble the instruction*)
             let instruction := (mSB,lSB) in
             exec_step (exec'' instruction system) i'
  end.

End InstructionSetCode.

Module InstructionSetNotation.
  
Notation "( 'ret' )" := (write_instruction_nib (n0,n0,ne,ne)).

Notation "( 'jump' 'to' ng ::: nh ::: ni )" := (write_instruction_nib (n1,ng,nh,ni)).

Notation "( 'call' ng ::: nh ::: ni )" := (write_instruction_nib (n2,ng,nh,ni)).

Notation "( 'skip' 'if' vx 'equal' 'to' ng ::: nh )" := (write_instruction_nib (n3, register_to_nib vx,ng,nh)).

Notation "( 'skip' 'if' vx 'not' 'equal' 'to' ng nh )" := (write_instruction_nib (n4, register_to_nib vx,ng,nh)).

Notation "( 'skip' 'if' vx 'equal' vy )" := (write_instruction_nib (n5, register_to_nib vx,register_to_nib vy,n0)).

Notation "( vx := ng ::: nh )" := (write_instruction_nib (n6, register_to_nib vx, ng, nh)).

Notation "( vx :=+ ng ::: nh )" := (write_instruction_nib (n7, register_to_nib vx, ng, nh)).

Notation "( vx := vy )" := (write_instruction_nib (n8,register_to_nib vx,register_to_nib vy,n0)).
Notation "( vx :=\/ vy )" := (write_instruction_nib (n8,register_to_nib vx,register_to_nib vy,n1)).
Notation "( vx :=/\ vy )" := (write_instruction_nib (n8,register_to_nib vx,register_to_nib vy,n2)).
Notation "( vx :=(+) vy )" := (write_instruction_nib (n8,register_to_nib vx,register_to_nib vy,n3)).
Notation "( vx :=+ vy )" := (write_instruction_nib (n8,register_to_nib vx,register_to_nib vy,n4)).

Notation "( 'skip' 'if' vx 'not' 'equal' 'to' vy )" := (write_instruction_nib (n9,register_to_nib vx,register_to_nib vy,n0)).

Notation "( i := ng ::: nh ::: ni )" := (write_instruction_nib (na,ng, nh, ni)).

Notation "( 'jumpv0' 'to' ng ::: nh ::: ni )" := (write_instruction_nib (nb,ng,nh,ni)).

Notation "( 'fill' vx )" := (write_instruction_nib (nf,register_to_nib vx,n5,n5)).

Notation "inst1 ;; inst2" := (fun addr system => inst2 (S (S addr)) (inst1 addr system)) (at level 80, right associativity).

End InstructionSetNotation.

Import InstructionSetNotation.
  
Section InstructionSetProofs.

  (* Proving both functions do the same *) 
  Lemma sameI1NNN : forall state instruction,
    I1NNN' instruction state = I1NNN instruction state.
  Proof.
    intros.
    destruct state.
    auto.
  Qed.

End InstructionSetProofs.


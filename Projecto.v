Require Import Coq.Init.Byte Coq.Strings.Byte Coq.Bool.Bvector.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.
Import BvectorNotations.

From RecordUpdate Require Import RecordSet.

(*
 We'll be using bytes. Instructions are 2 bytes long and memory/instructions are stored in big-endian format.
 
 Caution: coq bytes are stored in little endian format
 
 - Modelling this machine requires several components:
    - Modelling main memory (Sounds easy, list of bytes?).
    - Modelling the stack (We've also done this before).
    - Modelling "GPU" memory (Even if I don't think there's a way to display it on Coq, we still need it for some instructions.
    - Modelling the instruction set (We can write the equivalent of exec that we've been using in class.
    - Modelling the "CPU" (Hardest part for sure):
        - Modelling the 16 registers (V0-VF) and the I register.
        - Modellling the Program Counter.
        - Modelling the timer registers (Don't see how it's possible).
        - Modelling input (Also not sure).

 For more info see https://en.wikipedia.org/wiki/CHIP-8.
*)

Module HelperDataTypes.

Inductive nibble :=
  |n0
  |n1
  |n2
  |n3
  |n4
  |n5
  |n6
  |n7
  |n8
  |n9
  |na
  |nb
  |nc
  |nd
  |ne
  |nf.


  
Definition n_to_nat (n : nibble) : nat :=
  match n with
  |n0 => 0
  |n1 => 1
  |n2 => 2
  |n3 => 3
  |n4 => 4
  |n5 => 5
  |n6 => 6
  |n7 => 7
  |n8 => 8
  |n9 => 9
  |na => 10
  |nb => 11
  |nc => 12
  |nd => 13
  |ne => 14
  |nf => 15
  end.

Definition nib_eq (n1 n2 : nibble) : bool :=
  eqb (n_to_nat n1) (n_to_nat n2).
  
Definition nat_to_n (n : nat) : nibble :=
  match n with
  |0  => n0
  |1  => n1
  |2  => n2
  |3  => n3
  |4  => n4
  |5  => n5
  |6  => n6
  |7  => n7
  |8  => n8
  |9  => n9
  |10 => na
  |11 => nb
  |12 => nc
  |13 => nd
  |14 => ne
  |15 => nf
  | _ => n0
  end.

Definition nibble_of_bits :=
  fun n => nat_to_n (to_nat (of_bits n)).

Definition byte_to_nib' (data : byte) : (nibble * nibble) := 
  match to_bits data with
  | (a,(b,(c,(d,(e,(f,(g,h))))))) =>
    let low  := (e,(f,(g,(h,(false,(false,(false,(false)))))))) in 
    let high := (a,(b,(c,(d,(false,(false,(false,(false)))))))) in
    (nibble_of_bits low, nibble_of_bits high)
  end.

Local Notation "0" := false.
Local Notation "1" := true.

Definition n_to_bits (n : nibble) : bool * (bool * (bool * bool)) :=
  match n with
    |n0 => (0, (0 ,(0 , 0)))
    |n1 => (1 ,(0 ,(0 , 0)))
    |n2 => (0 ,(1 ,(0 , 0)))
    |n3 => (1 ,(1 ,(0 , 0)))
    |n4 => (0 ,(0 ,(1 , 0)))
    |n5 => (1 ,(0 ,(1 , 0)))
    |n6 => (0 ,(1 ,(1 , 0)))
    |n7 => (1 ,(1 ,(1 , 0)))
    |n8 => (0 ,(0 ,(0 , 1)))
    |n9 => (1 ,(0 ,(0 , 1)))
    |na => (0 ,(1 ,(0 , 1)))
    |nb => (1 ,(1 ,(0 , 1)))
    |nc => (0 ,(0 ,(1 , 1)))
    |nd => (1 ,(0 ,(1 , 1)))
    |ne => (0 ,(1 ,(1 , 1)))
    |nf => (1 ,(1 ,(1 , 1)))
  end.


Definition nib_to_byte (nib_pair : (nibble * nibble)) : byte := 
  match nib_pair with
  | (nHigh, nLow) =>
      let '(a, (b, (c, d))) := n_to_bits nHigh in
      let '(e, (f, (g, h))) := n_to_bits nLow in
        of_bits (e,(f,(g,(h,(a,(b,(c,d)))))))
  end.


Definition byte_to_nib (data : byte) : (nibble * nibble) :=
   match data with
     | x00 => (n0, n0)
     | x01 => (n0, n1)
     | x02 => (n0, n2)
     | x03 => (n0, n3)
     | x04 => (n0, n4)
     | x05 => (n0, n5)                
     | x06 => (n0, n6)
     | x07 => (n0, n7)
     | x08 => (n0, n8)
     | x09 => (n0, n9)
     | x0a => (n0, na)
     | x0b => (n0, nb)
     | x0c => (n0, nc)
     | x0d => (n0, nd)
     | x0e => (n0, ne)
     | x0f => (n0, nf)
     | x10 => (n1, n0)
     | x11 => (n1, n1)
     | x12 => (n1, n2)
     | x13 => (n1, n3)
     | x14 => (n1, n4)
     | x15 => (n1, n5)
     | x16 => (n1, n6)
     | x17 => (n1, n7)
     | x18 => (n1, n8)
     | x19 => (n1, n9)
     | x1a => (n1, na)
     | x1b => (n1, nb)
     | x1c => (n1, nc)
     | x1d => (n1, nd)
     | x1e => (n1, ne)
     | x1f => (n1, nf)
     | x20 => (n2, n0)
     | x21 => (n2, n1)
     | x22 => (n2, n2)
     | x23 => (n2, n3)
     | x24 => (n2, n4)
     | x25 => (n2, n5)
     | x26 => (n2, n6)
     | x27 => (n2, n7)
     | x28 => (n2, n8)
     | x29 => (n2, n9)
     | x2a => (n2, na)
     | x2b => (n2, nb)
     | x2c => (n2, nc)
     | x2d => (n2, nd)
     | x2e => (n2, ne)
     | x2f => (n2, nf)
     | x30 => (n3, n0)
     | x31 => (n3, n1)
     | x32 => (n3, n2)
     | x33 => (n3, n3)
     | x34 => (n3, n4)
     | x35 => (n3, n5)
     | x36 => (n3, n6)
     | x37 => (n3, n7)
     | x38 => (n3, n8)
     | x39 => (n3, n9)
     | x3a => (n3, na)
     | x3b => (n3, nb)
     | x3c => (n3, nc)
     | x3d => (n3, nd)
     | x3e => (n3, ne)
     | x3f => (n3, nf)
     | x40 => (n4, n0)
     | x41 => (n4, n1)
     | x42 => (n4, n2)
     | x43 => (n4, n3)
     | x44 => (n4, n4)
     | x45 => (n4, n5)
     | x46 => (n4, n6)
     | x47 => (n4, n7)
     | x48 => (n4, n8)
     | x49 => (n4, n9)
     | x4a => (n4, na)
     | x4b => (n4, nb)
     | x4c => (n4, nc)
     | x4d => (n4, nd)
     | x4e => (n4, ne)
     | x4f => (n4, nf)
     | x50 => (n5, n0)
     | x51 => (n5, n1)
     | x52 => (n5, n2)
     | x53 => (n5, n3)
     | x54 => (n5, n4)
     | x55 => (n5, n5)
     | x56 => (n5, n6)
     | x57 => (n5, n7)
     | x58 => (n5, n8)
     | x59 => (n5, n9)
     | x5a => (n5, na)
     | x5b => (n5, nb)
     | x5c => (n5, nc)
     | x5d => (n5, nd)
     | x5e => (n5, ne)
     | x5f => (n5, nf)
     | x60 => (n6, n0)
     | x61 => (n6, n1)
     | x62 => (n6, n2)
     | x63 => (n6, n3)
     | x64 => (n6, n4)
     | x65 => (n6, n5)
     | x66 => (n6, n6)
     | x67 => (n6, n7)
     | x68 => (n6, n8)
     | x69 => (n6, n9)
     | x6a => (n6, na)
     | x6b => (n6, nb)
     | x6c => (n6, nc)
     | x6d => (n6, nd)
     | x6e => (n6, ne)
     | x6f => (n6, nf)
     | x70 => (n7, n0)
     | x71 => (n7, n1)
     | x72 => (n7, n2)
     | x73 => (n7, n3)
     | x74 => (n7, n4)
     | x75 => (n7, n5)
     | x76 => (n7, n6)
     | x77 => (n7, n7)
     | x78 => (n7, n8)
     | x79 => (n7, n9)
     | x7a => (n7, na)
     | x7b => (n7, nb)
     | x7c => (n7, nc)
     | x7d => (n7, nd)
     | x7e => (n7, ne)
     | x7f => (n7, nf)
     | x80 => (n8, n0)
     | x81 => (n8, n1)
     | x82 => (n8, n2)
     | x83 => (n8, n3)
     | x84 => (n8, n4)
     | x85 => (n8, n5)
     | x86 => (n8, n6)
     | x87 => (n8, n7)
     | x88 => (n8, n8)
     | x89 => (n8, n9)
     | x8a => (n8, na)
     | x8b => (n8, nb)
     | x8c => (n8, nc)
     | x8d => (n8, nd)
     | x8e => (n8, ne)
     | x8f => (n8, nf)
     | x90 => (n9, n0)
     | x91 => (n9, n1)
     | x92 => (n9, n2)
     | x93 => (n9, n3)
     | x94 => (n9, n4)
     | x95 => (n9, n5)
     | x96 => (n9, n6)
     | x97 => (n9, n7)
     | x98 => (n9, n8)
     | x99 => (n9, n9)
     | x9a => (n9, na)
     | x9b => (n9, nb)
     | x9c => (n9, nc)
     | x9d => (n9, nd)
     | x9e => (n9, ne)
     | x9f => (n9, nf)
     | xa0 => (na, n0)
     | xa1 => (na, n1)
     | xa2 => (na, n2)
     | xa3 => (na, n3)
     | xa4 => (na, n4)
     | xa5 => (na, n5)
     | xa6 => (na, n6)
     | xa7 => (na, n7)
     | xa8 => (na, n8)
     | xa9 => (na, n9)
     | xaa => (na, na)
     | xab => (na, nb)
     | xac => (na, nc)
     | xad => (na, nd)
     | xae => (na, ne)
     | xaf => (na, nf)
     | xb0 => (nb, n0)
     | xb1 => (nb, n1)
     | xb2 => (nb, n2)
     | xb3 => (nb, n3)
     | xb4 => (nb, n4)
     | xb5 => (nb, n5)
     | xb6 => (nb, n6)
     | xb7 => (nb, n7)
     | xb8 => (nb, n8)
     | xb9 => (nb, n9)
     | xba => (nb, na)
     | xbb => (nb, nb)
     | xbc => (nb, nc)
     | xbd => (nb, nd)
     | xbe => (nb, ne)
     | xbf => (nb, nf)
     | xc0 => (nc, n0)
     | xc1 => (nc, n1)
     | xc2 => (nc, n2)
     | xc3 => (nc, n3)
     | xc4 => (nc, n4)
     | xc5 => (nc, n5)
     | xc6 => (nc, n6)
     | xc7 => (nc, n7)
     | xc8 => (nc, n8)
     | xc9 => (nc, n9)
     | xca => (nc, na)
     | xcb => (nc, nb)
     | xcc => (nc, nc)
     | xcd => (nc, nd)
     | xce => (nc, ne)
     | xcf => (nc, nf)
     | xd0 => (nd, n0)
     | xd1 => (nd, n1)
     | xd2 => (nd, n2)
     | xd3 => (nd, n3)
     | xd4 => (nd, n4)
     | xd5 => (nd, n5)
     | xd6 => (nd, n6)
     | xd7 => (nd, n7)
     | xd8 => (nd, n8)
     | xd9 => (nd, n9)
     | xda => (nd, na)
     | xdb => (nd, nb)
     | xdc => (nd, nc)
     | xdd => (nd, nd)
     | xde => (nd, ne)
     | xdf => (nd, nf)
     | xe0 => (ne, n0)
     | xe1 => (ne, n1)
     | xe2 => (ne, n2)
     | xe3 => (ne, n3)
     | xe4 => (ne, n4)
     | xe5 => (ne, n5)
     | xe6 => (ne, n6)
     | xe7 => (ne, n7)
     | xe8 => (ne, n8)
     | xe9 => (ne, n9)
     | xea => (ne, na)
     | xeb => (ne, nb)
     | xec => (ne, nc)
     | xed => (ne, nd)
     | xee => (ne, ne)
     | xef => (ne, nf)
     | xf0 => (nf, n0)
     | xf1 => (nf, n1)
     | xf2 => (nf, n2)
     | xf3 => (nf, n3)
     | xf4 => (nf, n4)
     | xf5 => (nf, n5)
     | xf6 => (nf, n6)
     | xf7 => (nf, n7)
     | xf8 => (nf, n8)
     | xf9 => (nf, n9)
     | xfa => (nf, na)
     | xfb => (nf, nb)
     | xfc => (nf, nc)
     | xfd => (nf, nd)
     | xfe => (nf, ne)
     | xff => (nf, nf)
     end.

Lemma byte_to_nib_equality : forall b,
    byte_to_nib' b = byte_to_nib b.
Proof.
  intros ; destruct b ; simpl ; auto.
Qed.
  
End HelperDataTypes.


Module MainMemory.

Fixpoint init_memory' (n : nat) : list byte :=
  match n with
    |0 => []
    |S n' => x00 :: init_memory' n'
  end.


Definition init_memory : list byte :=
  init_memory'  4096.


(* nth function to read memory*)

Fixpoint write_memory {A : Type}(data : A) (address : nat) (ram : list A) : list A :=
  match address, ram with
    |0, head :: tail => data :: tail
    |0, [] => []
    |S address', [] => []
    |S address', head :: tail => head :: write_memory data address' tail
  end.
  
End MainMemory.

Definition byte_to_Bvector (b : byte) : Bvector 8 :=
  match to_bits b with 
  | (a,(b,(c,(d,(e,(f,(g,h))))))) =>
    [a;b;c;d;e;f;g;h]%vector
  end.

Definition Bvector_to_byte (bv : Bvector 8) : byte :=
  match bv with 
    | [a;b;c;d;e;f;g;h]%vector => 
      of_bits (a,(b,(c,(d,(e,(f,(g,h)))))))
    | _ => x00
  end.

Theorem byte_to_Bvector_inverse : forall b,
    Bvector_to_byte (byte_to_Bvector b) = b.
Proof.
  intros.
  unfold Bvector_to_byte, byte_to_Bvector.
  destruct b ; simpl ; reflexivity.
Qed.
  
Import MainMemory.

Definition test := write_memory x10 1 init_memory.
Definition test2 := write_memory x23 3 test.

Compute map to_nat (firstn 10 test2).

Module MainSystem.


Record CHIP8 : Set := makeCHIP8  {
  pc : (byte * byte); (* Program Counter *)
  i : (byte * byte);  (* I register *)
  registers : list byte; (* 16 registers - TODO check if we can limit the length to be 16 always*)
  stack : list (byte * byte); (* 16 level stack *)
  stackPointer : nat;
  ram : list byte; (* Program instructions*) 
}.

Instance etaX : Settable _ := settable! makeCHIP8 <pc; i; registers; stack; stackPointer; ram>.

Import RecordSetNotations.
Definition setPC a x := x <|pc := a|>.

Definition popStack x := x <|stackPointer ::= sub 1|> <|pc := nth (sub 1 (x.(stackPointer))) x.(stack) (xde, xad)|>.
(*Update stack and then increase update stackpointer*)
Definition pushStack (address : (byte * byte)) x := x <|stackPointer ::= succ|> 
                                                      <|stack := write_memory address x.(stackPointer) x.(stack)|>.
End MainSystem.















Module InstructionSet.
Import HelperDataTypes MainSystem.

(*1NNN - Jumps to address NNN. Using record update*)
Definition I1NNN' (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let newB1 := (n0, n2) in 
                 setPC ((nib_to_byte newB1), b2) system
  end.



(*1NNN - Jumps to address NNN.*)
Definition I1NNN (instruction : byte * byte) (system : CHIP8) : CHIP8 :=
  match system with
    |{|pc := pc'; i := i'; registers := registers'; stack := stack'; stackPointer := stackPointer'; ram := ram'|} =>
      match instruction with
        |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                    let newB1 := (n0, n2) in 
                    {|pc := ((nib_to_byte newB1), b2); i := i'; registers := registers'; 
                      stack := stack'; stackPointer := stackPointer'; ram := ram'|}
      end
    end.

Lemma sameI1NNN : forall state instruction,
  I1NNN' instruction state = I1NNN instruction state.
Proof.
intros.
destruct state.
auto.
Qed.

(*3XNN - Skips the next instruction if VX equals NN.*)



(*7XNN - 	Adds NN to VX. (Carry flag is not changed)*)
Definition I7XNN (instruction : byte * byte) (registers : list byte) : list byte :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 (* Another use of nth. Read the value from register VX in nat*)
                 let numVX := to_nat (nth vX registers x00) in
                 let numNN := to_nat b2 in
                 let addition := modulo (numVX + numNN) 256 in
                   match of_nat addition with
                   (*TODO - there has to be a better way to do this since addition should never be above 256 because of modulo*)
                    |None => registers
                    (*write to VX*)
                    |Some x => write_memory x vX registers
                    end
  end.


Definition I8XY0 (instruction : byte * byte) (registers : list byte) : list byte :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 let (n3, n4) := byte_to_nib b2 in
                 let vY := n_to_nat n3 in
                  (* nth function requires a default value. I think we should replace it with nth_error for now to help in debugging.*)
                  write_memory (nth vY registers x00) vX registers
  end.

(*Sets VX to VX or VY. (Bitwise OR operation) *)
Definition I8XY1 (instruction : byte * byte) (registers : list byte) : list byte :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 let (n3, n4) := byte_to_nib b2 in
                 let vY := n_to_nat n3 in
                 let register_y_value := (nth vY registers x00) in 
                 let register_x_value := (nth vX registers x00) in
                 let y_value_as_Bvector := byte_to_Bvector register_y_value in 
                 let x_value_as_Bvector := byte_to_Bvector register_x_value in
                 let or_x_y_as_Bvector := y_value_as_Bvector ^| x_value_as_Bvector in 
                 let or_x_y_as_byte := Bvector_to_byte or_x_y_as_Bvector in 
                  write_memory or_x_y_as_byte vX registers
  end.

Definition I8XY2 (instruction : byte * byte) (registers : list byte) : list byte :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 let (n3, n4) := byte_to_nib b2 in
                 let vY := n_to_nat n3 in
                 let register_y_value := (nth vY registers x00) in 
                 let register_x_value := (nth vX registers x00) in
                 let y_value_as_Bvector := byte_to_Bvector register_y_value in 
                 let x_value_as_Bvector := byte_to_Bvector register_x_value in
                 let or_x_y_as_Bvector := y_value_as_Bvector ^& x_value_as_Bvector in 
                 let or_x_y_as_byte := Bvector_to_byte or_x_y_as_Bvector in 
                  write_memory or_x_y_as_byte vX registers
  end.

Definition I8XY3 (instruction : byte * byte) (registers : list byte) : list byte :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 let (n3, n4) := byte_to_nib b2 in
                 let vY := n_to_nat n3 in
                 let register_y_value := (nth vY registers x00) in 
                 let register_x_value := (nth vX registers x00) in
                 let y_value_as_Bvector := byte_to_Bvector register_y_value in 
                 let x_value_as_Bvector := byte_to_Bvector register_x_value in
                 let or_x_y_as_Bvector := BVxor 8 y_value_as_Bvector x_value_as_Bvector in 
                 let or_x_y_as_byte := Bvector_to_byte or_x_y_as_Bvector in 
                  write_memory or_x_y_as_byte vX registers
  end.

(*8XY4 - Adds VY to VX. VF is set to 1 when there's a carry, and to 0 when there isn't.*)
Definition I8XY4 (instruction : byte * byte) (registers : list byte) : list byte :=
match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 let (n3, n4) := byte_to_nib b2 in
                 let vY := n_to_nat n3 in
                 (* Another use of nth. Read the value from register VX in nat*)
                 let numVX := to_nat (nth vX registers x00) in
                 let numVY := to_nat (nth vY registers x00) in
                 let addition := numVX + numVY in
                 let mod_addition := modulo addition 256 in
                 match of_nat mod_addition with
                              |Some x =>  match of_nat addition with
                                          (*If we get a None that means there was overflow, set VF to 1*)
                                          |None => write_memory x vX (write_memory x01 15 registers)
                                          (*Else put VF to 0*)
                                          |Some _ => write_memory x vX (write_memory x00 15 registers)
                                          end
                                          
                              (*TODO - refactor this one out. Think of a better way to structure this*)
                              |_ => registers
                              end
  end.




(*6XNN - Sets VX to NN.*)
Definition I6XNN (instruction : byte * byte) (registers : list byte) : list byte :=
  match instruction with
    |(b1, b2) => let (n1, n2) := byte_to_nib b1 in
                 let vX := n_to_nat n2 in
                 let (n3, n4) := byte_to_nib b2 in
                 let vY := n_to_nat n3 in
                  write_memory b2 vX registers
  end.                  

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

Fixpoint exec'' (instruction : byte * byte) (registers : list byte) : list byte :=
  match instruction with
  |(e1, e2) =>
   match byte_to_nib' e1, byte_to_nib' e2 with
   | (n8,_),(_,n0) => I8XY0 instruction registers                            
   | (n8,_),(_,n1) => I8XY1 instruction registers                          
   | (n8,_),(_,n2) => I8XY2 instruction registers                          
   | (n8,_),(_,n3) => I8XY3 instruction registers
   | (n6,_),(_,_)  => I6XNN instruction registers
   | (n7,_),(_,_)  => I7XNN instruction registers
   | (n8,_),(_,n4) => I8XY4 instruction registers
   |  _    ,    _  => [xde;xad;xbe;xef]
   end
  end.

(*
Fixpoint exec_step (system : CHIP8) (step : nat) : CHIP8 :=
  match nat with
    |O => system
    |S step' => exec_ste  
  *)


End InstructionSet.

Import InstructionSet.

Definition registersStart := init_memory' 16.
Definition registersWritten := write_memory x99 0 registersStart.

Compute registersStart.
Compute registersWritten.
Compute exec (x82, x00) registersWritten.
Compute exec (x00, x00) registersStart.

(*Check or*)
Definition registersWrittenTwice := write_memory x8f 1 registersWritten.
Compute registersWrittenTwice.

Compute exec'' (x80, x13) registersWrittenTwice.

(* Adding NN to vX. Example with and without overflow*)
Compute map to_nat (exec'' (x71, x01) (exec'' (x61, x09) registersStart)).
Compute map to_nat (exec'' (x71, xff) (exec'' (x61, x02) registersStart)).

(*I8XY4 - Add v1 to v0 *)
(*With overflow*)
Compute map to_nat registersWrittenTwice.
Compute map to_nat (exec'' (x80, x14) registersWrittenTwice).

(*Without overflow*)
Compute map to_nat (exec'' (x61, x09) registersStart).
Compute map to_nat (exec'' (x80, x14) (exec'' (x61, x09) registersStart)).

Import MainSystem.
Definition startingState := makeCHIP8 (x00,x00) (x00,x00) registersStart [(x00, x00)] 0 [].

(* Set PC to x303*)
Compute I1NNN (x13, x03) startingState.

Compute setPC (x40, x40) startingState.

(* Address in the stack is 0x0505. If we pop it we should get our PC = x0505
    Note - the stack list isn't cleared. It's technically not needed because we would overwrite it when we next push
    but still it's worth looking into if it's needed. Nothing else looks at the stack except the push/pop functions
*)
Definition poppableState := makeCHIP8 (x00,x00) (x00,x00) registersStart [(x05, x05)] 1 [].

Compute popStack poppableState.

Compute pushStack (x09, x09) startingState.

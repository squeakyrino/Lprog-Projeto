Require Import Coq.Init.Byte Coq.Strings.Byte Coq.Bool.Bvector.
Require Import Coq.Init.Nat.
Require Import Coq.omega.Omega.

Section HelperDataTypesTypes.

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

Inductive register :=
  |v0
  |v1
  |v2
  |v3
  |v4
  |v5
  |v6
  |v7
  |v8
  |v9
  |va
  |vb
  |vc
  |vd
  |ve
  |vf.

End HelperDataTypesTypes.

Section HelperDataTypesCode.

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

Local Notation "0" := false.
Local Notation "1" := true.

Definition bits_to_n (n :  bool * (bool * (bool * bool))) : nibble :=
  match n with
  |(0,(0,(0,0))) => n0
  |(1,(0,(0,0))) => n1
  |(0,(1,(0,0))) => n2
  |(1,(1,(0,0))) => n3
  |(0,(0,(1,0))) => n4
  |(1,(0,(1,0))) => n5
  |(0,(1,(1,0))) => n6
  |(1,(1,(1,0))) => n7
  |(0,(0,(0,1))) => n8
  |(1,(0,(0,1))) => n9
  |(0,(1,(0,1))) => na
  |(1,(1,(0,1))) => nb
  |(0,(0,(1,1))) => nc
  |(1,(0,(1,1))) => nd
  |(0,(1,(1,1))) => ne
  |(1,(1,(1,1))) => nf
  end.

Definition byte_to_nib' (data : byte) : (nibble * nibble) := 
  match to_bits data with
  | (a,(b,(c,(d,(e,(f,(g,h))))))) =>
    let low  := (e,(f,(g,h))) in 
    let high := (a,(b,(c,d))) in
    (bits_to_n low, bits_to_n high)
  end.

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

Definition word_to_nat_le (bv : (byte * byte)) : nat :=
  match bv with
  | (b1, b2) =>
    let n1 := to_nat b1 in
    let n2 := 256 * (to_nat b2) in 
    n1 + n2
  end.

Definition word_to_nat_be (bv : (byte * byte)) : nat :=
  match bv with
  | (b1, b2) => word_to_nat_le (b2, b1)
  end.

Definition nat_to_word_le (n : nat) : (byte * byte) :=
  let d := div n 256 in
  let r := modulo n 256 in
  match of_nat r with
  | None => (x00,x00)
  | Some x1 => 
    match of_nat d with
    | None => (x00,x00)
    | Some x2 => (x1, x2)
    end
  end.

Definition nat_to_word_be (n : nat) : (byte * byte) :=
  let nat_to_le := nat_to_word_le n in
  match nat_to_le with
    (a,b) => (b,a)
  end.

Definition register_to_nib (r : register) :=
  match r with
  |v0 => n0
  |v1 => n1
  |v2 => n2
  |v3 => n3
  |v4 => n4
  |v5 => n5
  |v6 => n6
  |v7 => n7
  |v8 => n8
  |v9 => n9
  |va => na
  |vb => nb
  |vc => nc
  |vd => nd
  |ve => ne
  |vf => nf
  end.

Definition nib_to_byte_low (nib : nibble) :=
  nib_to_byte (n0, nib).

Definition nib_to_byte_high (nib : nibble) :=
  nib_to_byte (nib, n0).

End HelperDataTypesCode.

Section HelperDataTypesProof.

Lemma to_nat_less_256 : forall b,
    to_nat b < 256.
Proof.
  intros.
  destruct b ; simpl ; omega.
Qed.

Lemma word_to_nat_aux : forall b b0, 
  of_nat ((to_nat b + to_nat b0 * 256) / 256) = Some b0.
Proof.
  intros. rewrite Nat.div_add ; auto.
  rewrite Nat.div_small ; [|destruct b ; simpl ; omega].
  simpl. apply of_to_nat. 
Qed.
  
Lemma word_to_nat_le_soundness : forall w,
    nat_to_word_le (word_to_nat_le w) = w.
Proof.
  intro w. destruct w.
  unfold word_to_nat_le.
  unfold nat_to_word_le.
  rewrite PeanoNat.Nat.add_mod ; auto.
  specialize (PeanoNat.Nat.mod_mul (to_nat b0) 256) as H.
  rewrite PeanoNat.Nat.mul_comm. rewrite PeanoNat.Nat.mod_mul ; auto.
  destruct b eqn:E ; simpl ; specialize (word_to_nat_aux b) as H' ;
  rewrite E in H' ; simpl in H' ; rewrite H' ; reflexivity.
                                     Qed.
                                     
Lemma word_to_nat_be_soundness : forall w,
    nat_to_word_be (word_to_nat_be w) = w.
Proof.
  intro w. destruct w.
  unfold word_to_nat_be.
  unfold nat_to_word_be.
  rewrite word_to_nat_le_soundness. reflexivity.
Qed.
                                     
Lemma byte_to_nib_equality : forall b,
    byte_to_nib' b = byte_to_nib b. 
Proof.
  intros b.
  destruct b ; auto.
Qed.
  
Lemma byte_nibble_soundness : forall b,
    byte_to_nib' (nib_to_byte b) = b.
Proof.
  intros b. unfold nib_to_byte. unfold byte_to_nib'.
  destruct b eqn:E. destruct n, n10 ; auto.
Qed.

Theorem byte_to_Bvector_inverse : forall b,
    Bvector_to_byte (byte_to_Bvector b) = b.
Proof.
  intros.
  unfold Bvector_to_byte, byte_to_Bvector.
  destruct b ; simpl ; reflexivity.
Qed.

End HelperDataTypesProof.

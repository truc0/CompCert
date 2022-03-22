Require Import Coqlib Integers Errors.
Require Import Hex lib.Bits Memdata.
Require Import Util Encode.
Require Import EncDecRet RelSpec EncConsistency DecConsistency.
Import String Ascii.
Import List.
Import ListNotations.
Import Hex Bits.
Require Import BPProperty.
Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.


Ltac destr_para_name_type var name t Ht:=
  match goal with
  |[|-_] => destruct var as [name Ht]
  end.

Ltac simpl_bytes_to_bits :=
  repeat (try rewrite bytes_to_bits_opt_cons;
          rewrite bytes_to_bits_opt_correct;
          [|simpl; (try rewrite app_length; simpl);(try omega); auto]).

Ltac finalize_soundness:=
  repeat (split; simpl; try omega; auto).

Ltac try_hexize_value n:=
  let HHex := fresh "HHex" in
  match goal with
  |[|- context G[Byte.repr n]] =>
   try(hexize_byte_value n; rewrite HHex; clear HHex)
  end.

Ltac solve_bits_to_bytes_to_bits :=
  match goal with
  |[H: bits_to_bytes ?var = OK ?x |-
    context G[bytes_to_bits_opt ?x]]
   => rewrite (bits_to_bytes_to_bits _ _ H)
  end.

Ltac simpl_bytes_to_bits_in H :=
  try rewrite bytes_to_bits_opt_cons in H;
  rewrite bytes_to_bits_opt_correct in H;
  [|simpl; (try rewrite app_length; simpl);
    try omega;auto].



Lemma encode_AddrE_sound: 
forall i input lst,
encode_AddrE i input = OK lst
-> AddrE_spec (bytes_to_bits_opt lst) i.
Proof.
intros i input lst HEncode. 
induction i.

(**** AddrE12 *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_byte input.
rename b7 into inb7.
rename b6 into inb6.
rename b5 into inb5.
rename b4 into inb4.
rename b3 into inb3.
rename b2 into inb2.
rename b1 into inb1.
rename b0 into inb0.
simpl in HEncode.
destruct builtin_eq_dec eqn:EQB0 in HEncode; [inversion HEncode|].
destruct builtin_eq_dec eqn:EQB1 in HEncode; [inversion HEncode|].
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 0%Z.
try try_hexize_value 4%Z.
try try_hexize_value 5%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00"].
exists [inb5;inb4;inb3].
exists [uvar3_02;uvar3_01;uvar3_00].
finalize_soundness.

(**** AddrE11 *****)
destr_para_name_type uvar32_0 uvar32_0 u32 Huvar32_0.
destr_byte input.
rename b7 into inb7.
rename b6 into inb6.
rename b5 into inb5.
rename b4 into inb4.
rename b3 into inb3.
rename b2 into inb2.
rename b1 into inb1.
rename b0 into inb0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 0%Z.
try try_hexize_value 5%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00"].
exists [inb5;inb4;inb3].
exists b["101"].
exists uvar32_0.
finalize_soundness.

(**** AddrE10 *****)
destr_para_name_type uvar2_0 uvar2_0 u2 Huvar2_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
destr_para_name_type uvar3_2 uvar3_2 u3 Huvar3_2.
destr_byte input.
rename b7 into inb7.
rename b6 into inb6.
rename b5 into inb5.
rename b4 into inb4.
rename b3 into inb3.
rename b2 into inb2.
rename b1 into inb1.
rename b0 into inb0.
simpl in HEncode.
destruct builtin_eq_dec eqn:EQB0 in HEncode; [inversion HEncode|].
destruct builtin_eq_dec eqn:EQB1 in HEncode; [inversion HEncode|].
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 0%Z.
try try_hexize_value 4%Z.
try try_hexize_value 5%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar2_0.
rename b  into uvar2_01.
rename b0 into uvar2_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.
destr_list  uvar3_2.
rename b  into uvar3_22.
rename b0 into uvar3_21.
rename b1 into uvar3_20.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00"].
exists [inb5;inb4;inb3].
exists b["100"].
exists [uvar2_01;uvar2_00].
exists [uvar3_12;uvar3_11;uvar3_10].
exists [uvar3_22;uvar3_21;uvar3_20].
finalize_soundness.

(**** AddrE9 *****)
destr_para_name_type uvar2_0 uvar2_0 u2 Huvar2_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
destr_para_name_type uvar32_2 uvar32_2 u32 Huvar32_2.
destr_byte input.
rename b7 into inb7.
rename b6 into inb6.
rename b5 into inb5.
rename b4 into inb4.
rename b3 into inb3.
rename b2 into inb2.
rename b1 into inb1.
rename b0 into inb0.
simpl in HEncode.
destruct builtin_eq_dec eqn:EQB0 in HEncode; [inversion HEncode|].
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 0%Z.
try try_hexize_value 4%Z.
try try_hexize_value 5%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar2_0.
rename b  into uvar2_01.
rename b0 into uvar2_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00"].
exists [inb5;inb4;inb3].
exists b["100"].
exists [uvar2_01;uvar2_00].
exists [uvar3_12;uvar3_11;uvar3_10].
exists b["101"].
exists uvar32_2.
finalize_soundness.

(**** AddrE8 *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_byte input.
rename b7 into inb7.
rename b6 into inb6.
rename b5 into inb5.
rename b4 into inb4.
rename b3 into inb3.
rename b2 into inb2.
rename b1 into inb1.
rename b0 into inb0.
simpl in HEncode.
destruct builtin_eq_dec eqn:EQB0 in HEncode; [inversion HEncode|].
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 0%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.
try try_hexize_value 4%Z.
try try_hexize_value 5%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00"].
exists [inb5;inb4;inb3].
exists b["100"].
exists b["00"].
exists b["100"].
exists [uvar3_02;uvar3_01;uvar3_00].
finalize_soundness.

(**** AddrE7 *****)
destr_para_name_type uvar32_0 uvar32_0 u32 Huvar32_0.
destr_byte input.
rename b7 into inb7.
rename b6 into inb6.
rename b5 into inb5.
rename b4 into inb4.
rename b3 into inb3.
rename b2 into inb2.
rename b1 into inb1.
rename b0 into inb0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 0%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.
try try_hexize_value 4%Z.
try try_hexize_value 5%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00"].
exists [inb5;inb4;inb3].
exists b["100"].
exists b["00"].
exists b["100"].
exists b["101"].
exists uvar32_0.
finalize_soundness.

(**** AddrE6 *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar32_1 uvar32_1 u32 Huvar32_1.
destr_byte input.
rename b7 into inb7.
rename b6 into inb6.
rename b5 into inb5.
rename b4 into inb4.
rename b3 into inb3.
rename b2 into inb2.
rename b1 into inb1.
rename b0 into inb0.
simpl in HEncode.
destruct builtin_eq_dec eqn:EQB0 in HEncode; [inversion HEncode|].
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 2%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["10"].
exists [inb5;inb4;inb3].
exists [uvar3_02;uvar3_01;uvar3_00].
exists uvar32_1.
finalize_soundness.

(**** AddrE5 *****)
destr_para_name_type uvar2_0 uvar2_0 u2 Huvar2_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
destr_para_name_type uvar3_2 uvar3_2 u3 Huvar3_2.
destr_para_name_type uvar32_3 uvar32_3 u32 Huvar32_3.
destr_byte input.
rename b7 into inb7.
rename b6 into inb6.
rename b5 into inb5.
rename b4 into inb4.
rename b3 into inb3.
rename b2 into inb2.
rename b1 into inb1.
rename b0 into inb0.
simpl in HEncode.
destruct builtin_eq_dec eqn:EQB0 in HEncode; [inversion HEncode|].
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 2%Z.
try try_hexize_value 4%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar2_0.
rename b  into uvar2_01.
rename b0 into uvar2_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.
destr_list  uvar3_2.
rename b  into uvar3_22.
rename b0 into uvar3_21.
rename b1 into uvar3_20.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["10"].
exists [inb5;inb4;inb3].
exists b["100"].
exists [uvar2_01;uvar2_00].
exists [uvar3_12;uvar3_11;uvar3_10].
exists [uvar3_22;uvar3_21;uvar3_20].
exists uvar32_3.
finalize_soundness.

(**** AddrE4 *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar32_1 uvar32_1 u32 Huvar32_1.
destr_byte input.
rename b7 into inb7.
rename b6 into inb6.
rename b5 into inb5.
rename b4 into inb4.
rename b3 into inb3.
rename b2 into inb2.
rename b1 into inb1.
rename b0 into inb0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 2%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["10"].
exists [inb5;inb4;inb3].
exists b["100"].
exists b["00"].
exists b["100"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists uvar32_1.
finalize_soundness.

(**** AddrE0 *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_byte input.
rename b7 into inb7.
rename b6 into inb6.
rename b5 into inb5.
rename b4 into inb4.
rename b3 into inb3.
rename b2 into inb2.
rename b1 into inb1.
rename b0 into inb0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11"].
exists [inb5;inb4;inb3].
exists [uvar3_02;uvar3_01;uvar3_00].
finalize_soundness.
Qed.

Lemma encode_Instruction_sound: 
forall i lst,
encode_Instruction i = OK lst
-> Instruction_spec (bytes_to_bits_opt lst) i.
Proof.
intros i lst HEncode. 
induction i; simpl.

(**** Ptestq_EvGv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 133%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["10000101"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Ptestq_ri *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar32_4 uvar32_4 u32 Huvar32_4.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
; try rename EQ1 into HEnc1;
 try rename x0 into xx1
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 247%Z.
try try_hexize_value 0%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["11110111"].
exists [inb7;inb6].
exists b["000"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
exists uvar32_4.
finalize_soundness.

(**** Pcmpq_GvEv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 59%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["00111011"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pcmpq_EvGv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 57%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["00111001"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pcmpq_ri *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar32_4 uvar32_4 u32 Huvar32_4.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
; try rename EQ1 into HEnc1;
 try rename x0 into xx1
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 129%Z.
try try_hexize_value 7%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 7%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["10000001"].
exists [inb7;inb6].
exists b["111"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
exists uvar32_4.
finalize_soundness.

(**** Prorq_ri *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar8_4 uvar8_4 u8 Huvar8_4.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
; try rename EQ1 into HEnc1;
 try rename x0 into xx1
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 193%Z.
try try_hexize_value 1%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar8_4.
rename b  into uvar8_47.
rename b0 into uvar8_46.
rename b1 into uvar8_45.
rename b2 into uvar8_44.
rename b3 into uvar8_43.
rename b4 into uvar8_42.
rename b5 into uvar8_41.
rename b6 into uvar8_40.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 1%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["11000001"].
exists [inb7;inb6].
exists b["001"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
exists [uvar8_47;uvar8_46;uvar8_45;uvar8_44;uvar8_43;uvar8_42;uvar8_41;uvar8_40].
finalize_soundness.

(**** Psarq_ri *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar8_4 uvar8_4 u8 Huvar8_4.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
; try rename EQ1 into HEnc1;
 try rename x0 into xx1
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 193%Z.
try try_hexize_value 7%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar8_4.
rename b  into uvar8_47.
rename b0 into uvar8_46.
rename b1 into uvar8_45.
rename b2 into uvar8_44.
rename b3 into uvar8_43.
rename b4 into uvar8_42.
rename b5 into uvar8_41.
rename b6 into uvar8_40.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 7%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["11000001"].
exists [inb7;inb6].
exists b["111"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
exists [uvar8_47;uvar8_46;uvar8_45;uvar8_44;uvar8_43;uvar8_42;uvar8_41;uvar8_40].
finalize_soundness.

(**** Psarq_rcl *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 211%Z.
try try_hexize_value 7%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 7%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["11010011"].
exists [inb7;inb6].
exists b["111"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Psalq_ri *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar8_4 uvar8_4 u8 Huvar8_4.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
; try rename EQ1 into HEnc1;
 try rename x0 into xx1
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 193%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar8_4.
rename b  into uvar8_47.
rename b0 into uvar8_46.
rename b1 into uvar8_45.
rename b2 into uvar8_44.
rename b3 into uvar8_43.
rename b4 into uvar8_42.
rename b5 into uvar8_41.
rename b6 into uvar8_40.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 4%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["11000001"].
exists [inb7;inb6].
exists b["100"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
exists [uvar8_47;uvar8_46;uvar8_45;uvar8_44;uvar8_43;uvar8_42;uvar8_41;uvar8_40].
finalize_soundness.

(**** Psalq_rcl *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 211%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 4%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["11010011"].
exists [inb7;inb6].
exists b["100"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pnotq *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 247%Z.
try try_hexize_value 2%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 2%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["11110111"].
exists [inb7;inb6].
exists b["010"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pxorq_GvEv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 51%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["00110011"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pxorq_EvGv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 49%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["00110001"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pxorq_ri *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar32_4 uvar32_4 u32 Huvar32_4.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
; try rename EQ1 into HEnc1;
 try rename x0 into xx1
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 129%Z.
try try_hexize_value 6%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 6%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["10000001"].
exists [inb7;inb6].
exists b["110"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
exists uvar32_4.
finalize_soundness.

(**** Porq_GvEv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 11%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["00001011"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Porq_EvGv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 9%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["00001001"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Porq_ri *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar32_4 uvar32_4 u32 Huvar32_4.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
; try rename EQ1 into HEnc1;
 try rename x0 into xx1
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 129%Z.
try try_hexize_value 1%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 1%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["10000001"].
exists [inb7;inb6].
exists b["001"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
exists uvar32_4.
finalize_soundness.

(**** Pandq_GvEv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 35%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["00100011"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pandq_EvGv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 33%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["00100001"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pandq_ri *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar32_4 uvar32_4 u32 Huvar32_4.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
; try rename EQ1 into HEnc1;
 try rename x0 into xx1
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 129%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 4%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["10000001"].
exists [inb7;inb6].
exists b["100"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
exists uvar32_4.
finalize_soundness.

(**** Pdivq *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 0%Z.
try try_hexize_value 0%Z.
try try_hexize_value 247%Z.
try try_hexize_value 3%Z.
try try_hexize_value 6%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["0100"].
exists b["1"].
exists b["0"].
exists b["0"].
exists [uvar1_00].
exists b["11110111"].
exists b["11"].
exists b["110"].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pidivq *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 0%Z.
try try_hexize_value 0%Z.
try try_hexize_value 247%Z.
try try_hexize_value 3%Z.
try try_hexize_value 7%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["0100"].
exists b["1"].
exists b["0"].
exists b["0"].
exists [uvar1_00].
exists b["11110111"].
exists b["11"].
exists b["111"].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pmulq_r *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 0%Z.
try try_hexize_value 0%Z.
try try_hexize_value 247%Z.
try try_hexize_value 3%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["0100"].
exists b["1"].
exists b["0"].
exists b["0"].
exists [uvar1_00].
exists b["11110111"].
exists b["11"].
exists b["100"].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pimulq_GvEv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 15%Z.
try try_hexize_value 175%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["00001111"].
exists b["10101111"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pimulq_r *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 0%Z.
try try_hexize_value 0%Z.
try try_hexize_value 247%Z.
try try_hexize_value 3%Z.
try try_hexize_value 5%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["0100"].
exists b["1"].
exists b["0"].
exists b["0"].
exists [uvar1_00].
exists b["11110111"].
exists b["11"].
exists b["101"].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pimulq_ri *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar3_2 uvar3_2 u3 Huvar3_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
destr_para_name_type uvar32_4 uvar32_4 u32 Huvar32_4.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 0%Z.
try try_hexize_value 105%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar3_2.
rename b  into uvar3_22.
rename b0 into uvar3_21.
rename b1 into uvar3_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists b["0"].
exists [uvar1_10].
exists b["01101001"].
exists b["11"].
exists [uvar3_22;uvar3_21;uvar3_20].
exists [uvar3_32;uvar3_31;uvar3_30].
exists uvar32_4.
finalize_soundness.

(**** Psubq_GvEv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 43%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["00101011"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Psubq_EvGv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 41%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["00101001"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Psubq_ri *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar32_4 uvar32_4 u32 Huvar32_4.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
; try rename EQ1 into HEnc1;
 try rename x0 into xx1
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 129%Z.
try try_hexize_value 5%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 5%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["10000001"].
exists [inb7;inb6].
exists b["101"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
exists uvar32_4.
finalize_soundness.

(**** Paddq_GvEv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["00000011"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Paddq_EvGv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 1%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["00000001"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Paddq_ri *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar32_4 uvar32_4 u32 Huvar32_4.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
; try rename EQ1 into HEnc1;
 try rename x0 into xx1
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 129%Z.
try try_hexize_value 0%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["10000001"].
exists [inb7;inb6].
exists b["000"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
exists uvar32_4.
finalize_soundness.

(**** Pnegq *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 247%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 3%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["11110111"].
exists [inb7;inb6].
exists b["011"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pleaq *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 141%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["10001101"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovq_EvGv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 137%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["10001001"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovq_GvEv *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar1_1 uvar1_1 u1 Huvar1_1.
destr_para_name_type uvar1_2 uvar1_2 u1 Huvar1_2.
destr_para_name_type uvar3_3 uvar3_3 u3 Huvar3_3.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 139%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar1_1.
rename b  into uvar1_10.
try clear HLTail.
destr_list  uvar1_2.
rename b  into uvar1_20.
try clear HLTail.
destr_list  uvar3_3.
rename b  into uvar3_32.
rename b0 into uvar3_31.
rename b1 into uvar3_30.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["0100"].
exists b["1"].
exists [uvar1_00].
exists [uvar1_10].
exists [uvar1_20].
exists b["10001011"].
exists [inb7;inb6].
exists [uvar3_32;uvar3_31;uvar3_30].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovq_ri *****)
destr_para_name_type uvar1_0 uvar1_0 u1 Huvar1_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
destr_para_name_type uvar64_2 uvar64_2 u64 Huvar64_2.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 4%Z.
try try_hexize_value 1%Z.
try try_hexize_value 0%Z.
try try_hexize_value 0%Z.
try try_hexize_value 11%Z.
try try_hexize_value 1%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar1_0.
rename b  into uvar1_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["0100"].
exists b["1"].
exists b["0"].
exists b["0"].
exists [uvar1_00].
exists b["0001"].
exists b["1"].
exists [uvar3_12;uvar3_11;uvar3_10].
exists uvar64_2.
finalize_soundness.

(**** Psubl_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar32_1 uvar32_1 u32 Huvar32_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 129%Z.
try try_hexize_value 3%Z.
try try_hexize_value 5%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["10000001"].
exists b["11"].
exists b["101"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists uvar32_1.
finalize_soundness.

(**** Pbsqrtsd *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 242%Z.
try try_hexize_value 15%Z.
try try_hexize_value 81%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110010"].
exists b["00001111"].
exists b["01010001"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Psbbl_rr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 25%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00011001"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Prep_movsl *****)
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 243%Z.
try try_hexize_value 165%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110011"].
exists b["10100101"].
finalize_soundness.

(**** Pmovsq_rm *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 243%Z.
try try_hexize_value 15%Z.
try try_hexize_value 126%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["11110011"].
exists b["00001111"].
exists b["01111110"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovsq_mr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 102%Z.
try try_hexize_value 15%Z.
try try_hexize_value 214%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["01100110"].
exists b["00001111"].
exists b["11010110"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pminsd *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 242%Z.
try try_hexize_value 15%Z.
try try_hexize_value 93%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110010"].
exists b["00001111"].
exists b["01011101"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pmaxsd *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 242%Z.
try try_hexize_value 15%Z.
try try_hexize_value 95%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110010"].
exists b["00001111"].
exists b["01011111"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pbswap32 *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 15%Z.
try try_hexize_value 3%Z.
try try_hexize_value 1%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00001111"].
exists b["11"].
exists b["001"].
exists [uvar3_02;uvar3_01;uvar3_00].
finalize_soundness.

(**** Pbsrl *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 15%Z.
try try_hexize_value 189%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00001111"].
exists b["10111101"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pbsfl *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 15%Z.
try try_hexize_value 188%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00001111"].
exists b["10111100"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Paddl_mi *****)
destr_para_name_type uvar32_1 uvar32_1 u32 Huvar32_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
; try rename EQ1 into HEnc1;
 try rename x0 into xx1
).
 autounfold with bitfields.
try try_hexize_value 128%Z.
try try_hexize_value 0%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["10000000"].
exists [inb7;inb6].
exists b["000"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
exists uvar32_1.
finalize_soundness.

(**** Paddl_rr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 1%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00000001"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Padcl_rr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 17%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00010001"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Padcl_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar8_1 uvar8_1 u8 Huvar8_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 131%Z.
try try_hexize_value 3%Z.
try try_hexize_value 2%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar8_1.
rename b  into uvar8_17.
rename b0 into uvar8_16.
rename b1 into uvar8_15.
rename b2 into uvar8_14.
rename b3 into uvar8_13.
rename b4 into uvar8_12.
rename b5 into uvar8_11.
rename b6 into uvar8_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["10000011"].
exists b["11"].
exists b["010"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar8_17;uvar8_16;uvar8_15;uvar8_14;uvar8_13;uvar8_12;uvar8_11;uvar8_10].
finalize_soundness.

(**** Pjcc_rel *****)
destr_para_name_type uvar4_0 uvar4_0 u4 Huvar4_0.
destr_para_name_type uvar32_1 uvar32_1 u32 Huvar32_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 15%Z.
try try_hexize_value 8%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar4_0.
rename b  into uvar4_03.
rename b0 into uvar4_02.
rename b1 into uvar4_01.
rename b2 into uvar4_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00001111"].
exists b["1000"].
exists [uvar4_03;uvar4_02;uvar4_01;uvar4_00].
exists uvar32_1.
finalize_soundness.

(**** Pret_iw *****)
destr_para_name_type uvar16_0 uvar16_0 u16 Huvar16_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 194%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11000010"].
exists uvar16_0.
finalize_soundness.

(**** Pret *****)
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 195%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11000011"].
finalize_soundness.

(**** Pcall_r *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 255%Z.
try try_hexize_value 3%Z.
try try_hexize_value 2%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11111111"].
exists b["11"].
exists b["010"].
exists [uvar3_02;uvar3_01;uvar3_00].
finalize_soundness.

(**** Pcall_ofs *****)
destr_para_name_type uvar32_0 uvar32_0 u32 Huvar32_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 232%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11101000"].
exists uvar32_0.
finalize_soundness.

(**** Pnop *****)
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 144%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["10010000"].
finalize_soundness.

(**** Pjmp_Ev *****)
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 255%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 4%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["11111111"].
exists [inb7;inb6].
exists b["100"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pjmp_l_rel *****)
destr_para_name_type uvar32_0 uvar32_0 u32 Huvar32_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 233%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11101001"].
exists uvar32_0.
finalize_soundness.

(**** Pandps_fm *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 15%Z.
try try_hexize_value 88%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["00001111"].
exists b["01011000"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pxorps_GvEv *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 15%Z.
try try_hexize_value 87%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["00001111"].
exists b["01010111"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pxorpd_GvEv *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 102%Z.
try try_hexize_value 15%Z.
try try_hexize_value 87%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["01100110"].
exists b["00001111"].
exists b["01010111"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pcomisd_ff *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 102%Z.
try try_hexize_value 15%Z.
try try_hexize_value 47%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["01100110"].
exists b["00001111"].
exists b["00101111"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pdivss_ff *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 243%Z.
try try_hexize_value 15%Z.
try try_hexize_value 94%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110011"].
exists b["00001111"].
exists b["01011110"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pdivsd_ff *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 242%Z.
try try_hexize_value 15%Z.
try try_hexize_value 94%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110010"].
exists b["00001111"].
exists b["01011110"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pmuld_ff *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 242%Z.
try try_hexize_value 15%Z.
try try_hexize_value 89%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110010"].
exists b["00001111"].
exists b["01011001"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Psubd_ff *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 242%Z.
try try_hexize_value 15%Z.
try try_hexize_value 92%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110010"].
exists b["00001111"].
exists b["01011100"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Paddd_ff *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 242%Z.
try try_hexize_value 15%Z.
try try_hexize_value 88%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110010"].
exists b["00001111"].
exists b["01011000"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Psetcc *****)
destr_para_name_type uvar4_0 uvar4_0 u4 Huvar4_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 15%Z.
try try_hexize_value 9%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar4_0.
rename b  into uvar4_03.
rename b0 into uvar4_02.
rename b1 into uvar4_01.
rename b2 into uvar4_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00001111"].
exists b["1001"].
exists [uvar4_03;uvar4_02;uvar4_01;uvar4_00].
exists b["11"].
exists b["000"].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pcmov *****)
destr_para_name_type uvar4_0 uvar4_0 u4 Huvar4_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
destr_para_name_type uvar3_2 uvar3_2 u3 Huvar3_2.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 15%Z.
try try_hexize_value 4%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar4_0.
rename b  into uvar4_03.
rename b0 into uvar4_02.
rename b1 into uvar4_01.
rename b2 into uvar4_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.
destr_list  uvar3_2.
rename b  into uvar3_22.
rename b0 into uvar3_21.
rename b1 into uvar3_20.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00001111"].
exists b["0100"].
exists [uvar4_03;uvar4_02;uvar4_01;uvar4_00].
exists b["11"].
exists [uvar3_12;uvar3_11;uvar3_10].
exists [uvar3_22;uvar3_21;uvar3_20].
finalize_soundness.

(**** Ptestl_rr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 133%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["10000101"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Ptestl_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar32_1 uvar32_1 u32 Huvar32_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 247%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110111"].
exists b["11"].
exists b["000"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists uvar32_1.
finalize_soundness.

(**** Pcmpl_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar32_1 uvar32_1 u32 Huvar32_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 129%Z.
try try_hexize_value 3%Z.
try try_hexize_value 7%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["10000001"].
exists b["11"].
exists b["111"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists uvar32_1.
finalize_soundness.

(**** Pcmpl_rr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 57%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00111001"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Prorl_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar8_1 uvar8_1 u8 Huvar8_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 193%Z.
try try_hexize_value 1%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar8_1.
rename b  into uvar8_17.
rename b0 into uvar8_16.
rename b1 into uvar8_15.
rename b2 into uvar8_14.
rename b3 into uvar8_13.
rename b4 into uvar8_12.
rename b5 into uvar8_11.
rename b6 into uvar8_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11000001"].
exists b["11"].
exists b["001"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar8_17;uvar8_16;uvar8_15;uvar8_14;uvar8_13;uvar8_12;uvar8_11;uvar8_10].
finalize_soundness.

(**** Prolw_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar8_1 uvar8_1 u8 Huvar8_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 102%Z.
try try_hexize_value 193%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar8_1.
rename b  into uvar8_17.
rename b0 into uvar8_16.
rename b1 into uvar8_15.
rename b2 into uvar8_14.
rename b3 into uvar8_13.
rename b4 into uvar8_12.
rename b5 into uvar8_11.
rename b6 into uvar8_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["01100110"].
exists b["11000001"].
exists b["11"].
exists b["000"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar8_17;uvar8_16;uvar8_15;uvar8_14;uvar8_13;uvar8_12;uvar8_11;uvar8_10].
finalize_soundness.

(**** Pshld_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
destr_para_name_type uvar8_2 uvar8_2 u8 Huvar8_2.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 15%Z.
try try_hexize_value 164%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.
destr_list  uvar8_2.
rename b  into uvar8_27.
rename b0 into uvar8_26.
rename b1 into uvar8_25.
rename b2 into uvar8_24.
rename b3 into uvar8_23.
rename b4 into uvar8_22.
rename b5 into uvar8_21.
rename b6 into uvar8_20.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00001111"].
exists b["10100100"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
exists [uvar8_27;uvar8_26;uvar8_25;uvar8_24;uvar8_23;uvar8_22;uvar8_21;uvar8_20].
finalize_soundness.

(**** Psarl_rcl *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 211%Z.
try try_hexize_value 3%Z.
try try_hexize_value 7%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11010011"].
exists b["11"].
exists b["111"].
exists [uvar3_02;uvar3_01;uvar3_00].
finalize_soundness.

(**** Psarl_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar8_1 uvar8_1 u8 Huvar8_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 193%Z.
try try_hexize_value 3%Z.
try try_hexize_value 7%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar8_1.
rename b  into uvar8_17.
rename b0 into uvar8_16.
rename b1 into uvar8_15.
rename b2 into uvar8_14.
rename b3 into uvar8_13.
rename b4 into uvar8_12.
rename b5 into uvar8_11.
rename b6 into uvar8_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11000001"].
exists b["11"].
exists b["111"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar8_17;uvar8_16;uvar8_15;uvar8_14;uvar8_13;uvar8_12;uvar8_11;uvar8_10].
finalize_soundness.

(**** Pshrl_rcl *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 211%Z.
try try_hexize_value 3%Z.
try try_hexize_value 5%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11010011"].
exists b["11"].
exists b["101"].
exists [uvar3_02;uvar3_01;uvar3_00].
finalize_soundness.

(**** Pshrl_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar8_1 uvar8_1 u8 Huvar8_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 193%Z.
try try_hexize_value 3%Z.
try try_hexize_value 5%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar8_1.
rename b  into uvar8_17.
rename b0 into uvar8_16.
rename b1 into uvar8_15.
rename b2 into uvar8_14.
rename b3 into uvar8_13.
rename b4 into uvar8_12.
rename b5 into uvar8_11.
rename b6 into uvar8_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11000001"].
exists b["11"].
exists b["101"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar8_17;uvar8_16;uvar8_15;uvar8_14;uvar8_13;uvar8_12;uvar8_11;uvar8_10].
finalize_soundness.

(**** Psall_rcl *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 211%Z.
try try_hexize_value 3%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11010011"].
exists b["11"].
exists b["100"].
exists [uvar3_02;uvar3_01;uvar3_00].
finalize_soundness.

(**** Psall_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar8_1 uvar8_1 u8 Huvar8_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 193%Z.
try try_hexize_value 3%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar8_1.
rename b  into uvar8_17.
rename b0 into uvar8_16.
rename b1 into uvar8_15.
rename b2 into uvar8_14.
rename b3 into uvar8_13.
rename b4 into uvar8_12.
rename b5 into uvar8_11.
rename b6 into uvar8_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11000001"].
exists b["11"].
exists b["100"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar8_17;uvar8_16;uvar8_15;uvar8_14;uvar8_13;uvar8_12;uvar8_11;uvar8_10].
finalize_soundness.

(**** Pnotl *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 247%Z.
try try_hexize_value 3%Z.
try try_hexize_value 2%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110111"].
exists b["11"].
exists b["010"].
exists [uvar3_02;uvar3_01;uvar3_00].
finalize_soundness.

(**** Pxorl_rr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 49%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00110001"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pxorl_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar32_1 uvar32_1 u32 Huvar32_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 129%Z.
try try_hexize_value 3%Z.
try try_hexize_value 6%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["10000001"].
exists b["11"].
exists b["110"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists uvar32_1.
finalize_soundness.

(**** Porl_rr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 9%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00001001"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Porl_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar32_1 uvar32_1 u32 Huvar32_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 129%Z.
try try_hexize_value 3%Z.
try try_hexize_value 1%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["10000001"].
exists b["11"].
exists b["001"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists uvar32_1.
finalize_soundness.

(**** Pandl_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar32_1 uvar32_1 u32 Huvar32_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 129%Z.
try try_hexize_value 3%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["10000001"].
exists b["11"].
exists b["100"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists uvar32_1.
finalize_soundness.

(**** Pandl_rr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 33%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00100001"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pidivl_r *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 247%Z.
try try_hexize_value 3%Z.
try try_hexize_value 7%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110111"].
exists b["11"].
exists b["111"].
exists [uvar3_02;uvar3_01;uvar3_00].
finalize_soundness.

(**** Pdivl_r *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 247%Z.
try try_hexize_value 3%Z.
try try_hexize_value 6%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110111"].
exists b["11"].
exists b["110"].
exists [uvar3_02;uvar3_01;uvar3_00].
finalize_soundness.

(**** Pcltd *****)
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 153%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["10011001"].
finalize_soundness.

(**** Pmull_r *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 247%Z.
try try_hexize_value 3%Z.
try try_hexize_value 4%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110111"].
exists b["11"].
exists b["100"].
exists [uvar3_02;uvar3_01;uvar3_00].
finalize_soundness.

(**** Pimull_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
destr_para_name_type uvar32_2 uvar32_2 u32 Huvar32_2.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 105%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["01101001"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
exists uvar32_2.
finalize_soundness.

(**** Pimull_rr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 15%Z.
try try_hexize_value 175%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00001111"].
exists b["10101111"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Psubl_rr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 43%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["00101011"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Paddl_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar32_1 uvar32_1 u32 Huvar32_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 129%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["10000001"].
exists b["11"].
exists b["000"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists uvar32_1.
finalize_soundness.

(**** Pnegl *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 247%Z.
try try_hexize_value 3%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110111"].
exists b["11"].
exists b["011"].
exists [uvar3_02;uvar3_01;uvar3_00].
finalize_soundness.

(**** Pleal *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 141%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["10001101"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pcvttss2si_rf *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 243%Z.
try try_hexize_value 15%Z.
try try_hexize_value 44%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110011"].
exists b["00001111"].
exists b["00101100"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pcvtsi2sd_fr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 242%Z.
try try_hexize_value 15%Z.
try try_hexize_value 42%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110010"].
exists b["00001111"].
exists b["00101010"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pcvtsi2ss_fr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 243%Z.
try try_hexize_value 15%Z.
try try_hexize_value 42%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110011"].
exists b["00001111"].
exists b["00101010"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pcvttsd2si_rf *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 242%Z.
try try_hexize_value 15%Z.
try try_hexize_value 44%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110010"].
exists b["00001111"].
exists b["00101100"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pcvtss2sd_ff *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 243%Z.
try try_hexize_value 15%Z.
try try_hexize_value 90%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110011"].
exists b["00001111"].
exists b["01011010"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pcvtsd2ss_ff *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 242%Z.
try try_hexize_value 15%Z.
try try_hexize_value 90%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["11110010"].
exists b["00001111"].
exists b["01011010"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pmovsw_GvEv *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 15%Z.
try try_hexize_value 191%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["00001111"].
exists b["10111111"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovzw_GvEv *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 15%Z.
try try_hexize_value 183%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["00001111"].
exists b["10110111"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovsb_GvEv *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 15%Z.
try try_hexize_value 190%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["00001111"].
exists b["10111110"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovzb_rm *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 15%Z.
try try_hexize_value 182%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["00001111"].
exists b["10110110"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovw_rm *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 102%Z.
try try_hexize_value 139%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["01100110"].
exists b["10001011"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovw_mr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 102%Z.
try try_hexize_value 137%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["01100110"].
exists b["10001001"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovb_rm *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 138%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["10001010"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovb_mr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 136%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["10001000"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pxchg_rr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar3_1 uvar3_1 u3 Huvar3_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ).
 autounfold with bitfields.
try try_hexize_value 135%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.
destr_list  uvar3_1.
rename b  into uvar3_12.
rename b0 into uvar3_11.
rename b1 into uvar3_10.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["10000111"].
exists b["11"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [uvar3_12;uvar3_11;uvar3_10].
finalize_soundness.

(**** Pflds_m *****)
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 217%Z.
try try_hexize_value 0%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["11011001"].
exists [inb7;inb6].
exists b["000"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pfstps_m *****)
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 217%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 3%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["11011001"].
exists [inb7;inb6].
exists b["011"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pfstpl_m *****)
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 221%Z.
try try_hexize_value 3%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 3%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["11011101"].
exists [inb7;inb6].
exists b["011"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pfldl_m *****)
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 221%Z.
try try_hexize_value 0%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["11011101"].
exists [inb7;inb6].
exists b["000"].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovss_fm *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 243%Z.
try try_hexize_value 15%Z.
try try_hexize_value 16%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["11110011"].
exists b["00001111"].
exists b["00010000"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovss_mf *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 243%Z.
try try_hexize_value 15%Z.
try try_hexize_value 17%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["11110011"].
exists b["00001111"].
exists b["00010001"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovsd_fm *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 242%Z.
try try_hexize_value 15%Z.
try try_hexize_value 16%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["11110010"].
exists b["00001111"].
exists b["00010000"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovsd_mf *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 242%Z.
try try_hexize_value 15%Z.
try try_hexize_value 17%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["11110010"].
exists b["00001111"].
exists b["00010001"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovl_rm *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 139%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["10001011"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovl_mr *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 137%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.
hexize_byte_value 0%Z; try rewrite HHex in HEnc0; clear HHex.
autounfold with bitfields in HEnc0.
repeat simpl_bytes_to_bits_in HEnc0.
simpl in HEnc0.
solve_preserve_klass encode_AddrE encode_AddrE_preserve.
rename x  into inb7.
rename x0 into inb6.
rename x1 into inb2.
rename x2 into inb1.
rename x3 into inb0.
rename x4 into AddrE_instance.
repeat simpl_bytes_to_bits. simpl.
generalize (encode_AddrE_sound _ _ _ HEnc0).
intros HAddrE.
simpl_bytes_to_bits_in HAddrE.
constructor.
exists b["10001001"].
exists [inb7;inb6].
exists [uvar3_02;uvar3_01;uvar3_00].
exists [inb2;inb1;inb0].
exists (bytes_to_bits_opt AddrE_instance).
finalize_soundness.

(**** Pmovl_ri *****)
destr_para_name_type uvar3_0 uvar3_0 u3 Huvar3_0.
destr_para_name_type uvar32_1 uvar32_1 u32 Huvar32_1.
simpl in HEncode.
simpl in HEncode. try (monadInv HEncode ; try rename EQ  into HEnc0;
 try rename x  into xx0
).
 autounfold with bitfields.
try try_hexize_value 11%Z.
try try_hexize_value 1%Z.
try try_hexize_value 0%Z.

simpl_bytes_to_bits.
destr_list  uvar3_0.
rename b  into uvar3_02.
rename b0 into uvar3_01.
rename b1 into uvar3_00.
try clear HLTail.

simpl. simpl_bytes_to_bits. simpl.
repeat rewrite bytes_to_bits_opt_app.
repeat solve_bits_to_bytes_to_bits.

constructor.
exists b["1011"].
exists b["1"].
exists [uvar3_02;uvar3_01;uvar3_00].
exists uvar32_1.
finalize_soundness.
Qed.


Lemma decode_Instruction_sound:
  forall l l' i, decode_Instruction (l++l') = OK(i, length l)
                 -> Instruction_spec (bytes_to_bits_opt l) i.
Proof.
  intros l l' i H.
  generalize (decode_Instruction_consistency _ _ _ H).
  intros HEnc.
  generalize (encode_Instruction_sound _ _ HEnc).
  auto.
Qed.







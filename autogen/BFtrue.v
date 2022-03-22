Require Import Coqlib Integers Errors.
Require Import Hex lib.Bits Memdata.
Require Import Util Encode.
Import String Ascii.
Import List.
Import ListNotations.
Import Hex Bits.
Require Import EncDecRet  VerificationCondition.
Require Import BPProperty.
Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Lemma AddrE12_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
AddrE12_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b2=false/\b1=false/\[b6;b7;b8]<>[true;false;false]/\[b6;b7;b8]<>[true;false;true].

Proof.
idtac "AddrE12_bp_true Lemma 1/10".
unfold AddrE12_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b6;(
destruct b7;(
destruct b8;(
repeat split;simpl in Bp;try congruence))).
Qed.


Lemma AddrE11_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
AddrE11_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b2=false/\b1=false/\b8=true/\b7=false/\b6=true.

Proof.
idtac "AddrE11_bp_true Lemma 2/10".
unfold AddrE11_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma AddrE10_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
AddrE10_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b2=false/\b1=false/\b8=false/\b7=false/\b6=true/\[b14;b15;b16]<>[true;false;true]/\[b11;b12;b13]<>[true;false;false].

Proof.
idtac "AddrE10_bp_true Lemma 3/10".
unfold AddrE10_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b11;(
destruct b12;(
destruct b13;(
destruct b14;(
destruct b15;(
destruct b16;(
repeat split;simpl in Bp;try congruence)))))).
Qed.


Lemma AddrE9_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
AddrE9_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b2=false/\b1=false/\b8=false/\b7=false/\b6=true/\b16=true/\b15=false/\b14=true/\[b11;b12;b13]<>[true;false;false].

Proof.
idtac "AddrE9_bp_true Lemma 4/10".
unfold AddrE9_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b11;(
destruct b12;(
destruct b13;(
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence))).
Qed.


Lemma AddrE8_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
AddrE8_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b2=false/\b1=false/\b8=false/\b7=false/\b6=true/\b10=false/\b9=false/\b13=false/\b12=false/\b11=true/\[b14;b15;b16]<>[true;false;true].

Proof.
idtac "AddrE8_bp_true Lemma 5/10".
unfold AddrE8_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;(
destruct b15;(
destruct b16;(
repeat split;simpl in Bp;try congruence))).
Qed.


Lemma AddrE7_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
AddrE7_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b2=false/\b1=false/\b8=false/\b7=false/\b6=true/\b10=false/\b9=false/\b13=false/\b12=false/\b11=true/\b16=true/\b15=false/\b14=true.

Proof.
idtac "AddrE7_bp_true Lemma 6/10".
unfold AddrE7_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma AddrE6_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
AddrE6_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b2=false/\b1=true/\[b6;b7;b8]<>[true;false;false].

Proof.
idtac "AddrE6_bp_true Lemma 7/10".
unfold AddrE6_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b6;(
destruct b7;(
destruct b8;(
repeat split;simpl in Bp;try congruence))).
Qed.


Lemma AddrE5_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
AddrE5_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b2=false/\b1=true/\b8=false/\b7=false/\b6=true/\[b11;b12;b13]<>[true;false;false].

Proof.
idtac "AddrE5_bp_true Lemma 8/10".
unfold AddrE5_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b11;(
destruct b12;(
destruct b13;(
repeat split;simpl in Bp;try congruence))).
Qed.


Lemma AddrE4_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
AddrE4_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b2=false/\b1=true/\b8=false/\b7=false/\b6=true/\b10=false/\b9=false/\b13=false/\b12=false/\b11=true.

Proof.
idtac "AddrE4_bp_true Lemma 9/10".
unfold AddrE4_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma AddrE0_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
AddrE0_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b2=true/\b1=true.

Proof.
idtac "AddrE0_bp_true Lemma 10/10".
unfold AddrE0_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.




Lemma Ptestq_EvGv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Ptestq_EvGv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=true/\b13=false/\b12=false/\b11=false/\b10=false/\b9=true.

Proof.
idtac "Ptestq_EvGv_bp_true Lemma 1/127".
unfold Ptestq_EvGv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Ptestq_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Ptestq_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=true/\b14=true/\b13=false/\b12=true/\b11=true/\b10=true/\b9=true/\b21=false/\b20=false/\b19=false.

Proof.
idtac "Ptestq_ri_bp_true Lemma 2/127".
unfold Ptestq_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcmpq_GvEv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pcmpq_GvEv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=true/\b14=false/\b13=true/\b12=true/\b11=true/\b10=false/\b9=false.

Proof.
idtac "Pcmpq_GvEv_bp_true Lemma 3/127".
unfold Pcmpq_GvEv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcmpq_EvGv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pcmpq_EvGv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=true/\b12=true/\b11=true/\b10=false/\b9=false.

Proof.
idtac "Pcmpq_EvGv_bp_true Lemma 4/127".
unfold Pcmpq_EvGv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcmpq_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pcmpq_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=false/\b12=false/\b11=false/\b10=false/\b9=true/\b21=true/\b20=true/\b19=true.

Proof.
idtac "Pcmpq_ri_bp_true Lemma 5/127".
unfold Pcmpq_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Prorq_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Prorq_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=false/\b12=false/\b11=false/\b10=true/\b9=true/\b21=true/\b20=false/\b19=false.

Proof.
idtac "Prorq_ri_bp_true Lemma 6/127".
unfold Prorq_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psarq_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Psarq_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=false/\b12=false/\b11=false/\b10=true/\b9=true/\b21=true/\b20=true/\b19=true.

Proof.
idtac "Psarq_ri_bp_true Lemma 7/127".
unfold Psarq_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psarq_rcl_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Psarq_rcl_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=true/\b14=false/\b13=false/\b12=true/\b11=false/\b10=true/\b9=true/\b21=true/\b20=true/\b19=true.

Proof.
idtac "Psarq_rcl_bp_true Lemma 8/127".
unfold Psarq_rcl_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psalq_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Psalq_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=false/\b12=false/\b11=false/\b10=true/\b9=true/\b21=false/\b20=false/\b19=true.

Proof.
idtac "Psalq_ri_bp_true Lemma 9/127".
unfold Psalq_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psalq_rcl_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Psalq_rcl_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=true/\b14=false/\b13=false/\b12=true/\b11=false/\b10=true/\b9=true/\b21=false/\b20=false/\b19=true.

Proof.
idtac "Psalq_rcl_bp_true Lemma 10/127".
unfold Psalq_rcl_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pnotq_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pnotq_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=true/\b14=true/\b13=false/\b12=true/\b11=true/\b10=true/\b9=true/\b21=false/\b20=true/\b19=false.

Proof.
idtac "Pnotq_bp_true Lemma 11/127".
unfold Pnotq_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pxorq_GvEv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pxorq_GvEv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=true/\b14=false/\b13=false/\b12=true/\b11=true/\b10=false/\b9=false.

Proof.
idtac "Pxorq_GvEv_bp_true Lemma 12/127".
unfold Pxorq_GvEv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pxorq_EvGv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pxorq_EvGv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=false/\b12=true/\b11=true/\b10=false/\b9=false.

Proof.
idtac "Pxorq_EvGv_bp_true Lemma 13/127".
unfold Pxorq_EvGv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pxorq_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pxorq_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=false/\b12=false/\b11=false/\b10=false/\b9=true/\b21=false/\b20=true/\b19=true.

Proof.
idtac "Pxorq_ri_bp_true Lemma 14/127".
unfold Pxorq_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Porq_GvEv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Porq_GvEv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=true/\b14=false/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false.

Proof.
idtac "Porq_GvEv_bp_true Lemma 15/127".
unfold Porq_GvEv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Porq_EvGv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Porq_EvGv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false.

Proof.
idtac "Porq_EvGv_bp_true Lemma 16/127".
unfold Porq_EvGv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Porq_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Porq_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=false/\b12=false/\b11=false/\b10=false/\b9=true/\b21=true/\b20=false/\b19=false.

Proof.
idtac "Porq_ri_bp_true Lemma 17/127".
unfold Porq_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pandq_GvEv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pandq_GvEv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=true/\b14=false/\b13=false/\b12=false/\b11=true/\b10=false/\b9=false.

Proof.
idtac "Pandq_GvEv_bp_true Lemma 18/127".
unfold Pandq_GvEv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pandq_EvGv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pandq_EvGv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=false/\b12=false/\b11=true/\b10=false/\b9=false.

Proof.
idtac "Pandq_EvGv_bp_true Lemma 19/127".
unfold Pandq_EvGv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pandq_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pandq_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=false/\b12=false/\b11=false/\b10=false/\b9=true/\b21=false/\b20=false/\b19=true.

Proof.
idtac "Pandq_ri_bp_true Lemma 20/127".
unfold Pandq_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pdivq_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pdivq_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b6=false/\b7=false/\b16=true/\b15=true/\b14=true/\b13=false/\b12=true/\b11=true/\b10=true/\b9=true/\b18=true/\b17=true/\b21=false/\b20=true/\b19=true.

Proof.
idtac "Pdivq_bp_true Lemma 21/127".
unfold Pdivq_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[|ring_simplify in Bp;congruence];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pidivq_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pidivq_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b6=false/\b7=false/\b16=true/\b15=true/\b14=true/\b13=false/\b12=true/\b11=true/\b10=true/\b9=true/\b18=true/\b17=true/\b21=true/\b20=true/\b19=true.

Proof.
idtac "Pidivq_bp_true Lemma 22/127".
unfold Pidivq_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[|ring_simplify in Bp;congruence];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmulq_r_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pmulq_r_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b6=false/\b7=false/\b16=true/\b15=true/\b14=true/\b13=false/\b12=true/\b11=true/\b10=true/\b9=true/\b18=true/\b17=true/\b21=false/\b20=false/\b19=true.

Proof.
idtac "Pmulq_r_bp_true Lemma 23/127".
unfold Pmulq_r_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[|ring_simplify in Bp;congruence];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pimulq_GvEv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pimulq_GvEv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=true/\b23=true/\b22=true/\b21=true/\b20=false/\b19=true/\b18=false/\b17=true.

Proof.
idtac "Pimulq_GvEv_bp_true Lemma 24/127".
unfold Pimulq_GvEv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[|ring_simplify in Bp;congruence];
destruct b18;[ring_simplify in Bp;congruence|];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[|ring_simplify in Bp;congruence];
destruct b23;[|ring_simplify in Bp;congruence];
destruct b24;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pimulq_r_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pimulq_r_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b6=false/\b7=false/\b16=true/\b15=true/\b14=true/\b13=false/\b12=true/\b11=true/\b10=true/\b9=true/\b18=true/\b17=true/\b21=true/\b20=false/\b19=true.

Proof.
idtac "Pimulq_r_bp_true Lemma 25/127".
unfold Pimulq_r_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[|ring_simplify in Bp;congruence];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pimulq_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pimulq_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b7=false/\b16=true/\b15=false/\b14=false/\b13=true/\b12=false/\b11=true/\b10=true/\b9=false/\b18=true/\b17=true.

Proof.
idtac "Pimulq_ri_bp_true Lemma 26/127".
unfold Pimulq_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[|ring_simplify in Bp;congruence];
destruct b18;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psubq_GvEv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Psubq_GvEv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=true/\b14=false/\b13=true/\b12=false/\b11=true/\b10=false/\b9=false.

Proof.
idtac "Psubq_GvEv_bp_true Lemma 27/127".
unfold Psubq_GvEv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psubq_EvGv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Psubq_EvGv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=true/\b12=false/\b11=true/\b10=false/\b9=false.

Proof.
idtac "Psubq_EvGv_bp_true Lemma 28/127".
unfold Psubq_EvGv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psubq_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Psubq_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=false/\b12=false/\b11=false/\b10=false/\b9=true/\b21=true/\b20=false/\b19=true.

Proof.
idtac "Psubq_ri_bp_true Lemma 29/127".
unfold Psubq_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Paddq_GvEv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Paddq_GvEv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=true/\b14=false/\b13=false/\b12=false/\b11=false/\b10=false/\b9=false.

Proof.
idtac "Paddq_GvEv_bp_true Lemma 30/127".
unfold Paddq_GvEv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Paddq_EvGv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Paddq_EvGv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=false/\b12=false/\b11=false/\b10=false/\b9=false.

Proof.
idtac "Paddq_EvGv_bp_true Lemma 31/127".
unfold Paddq_EvGv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Paddq_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Paddq_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=false/\b12=false/\b11=false/\b10=false/\b9=true/\b21=false/\b20=false/\b19=false.

Proof.
idtac "Paddq_ri_bp_true Lemma 32/127".
unfold Paddq_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pnegq_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pnegq_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=true/\b14=true/\b13=false/\b12=true/\b11=true/\b10=true/\b9=true/\b21=true/\b20=true/\b19=false.

Proof.
idtac "Pnegq_bp_true Lemma 33/127".
unfold Pnegq_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pleaq_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pleaq_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=true.

Proof.
idtac "Pleaq_bp_true Lemma 34/127".
unfold Pleaq_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovq_EvGv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pmovq_EvGv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=false/\b14=false/\b13=true/\b12=false/\b11=false/\b10=false/\b9=true.

Proof.
idtac "Pmovq_EvGv_bp_true Lemma 35/127".
unfold Pmovq_EvGv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovq_GvEv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pmovq_GvEv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b16=true/\b15=true/\b14=false/\b13=true/\b12=false/\b11=false/\b10=false/\b9=true.

Proof.
idtac "Pmovq_GvEv_bp_true Lemma 36/127".
unfold Pmovq_GvEv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovq_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pmovq_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b4=false/\b3=false/\b2=true/\b1=false/\b5=true/\b6=false/\b7=false/\b13=true/\b12=true/\b11=false/\b10=false/\b9=false.

Proof.
idtac "Pmovq_ri_bp_true Lemma 37/127".
unfold Pmovq_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psubl_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Psubl_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=false/\b4=false/\b3=false/\b2=false/\b1=true/\b10=true/\b9=true/\b13=true/\b12=false/\b11=true.

Proof.
idtac "Psubl_ri_bp_true Lemma 38/127".
unfold Psubl_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pbsqrtsd_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 l,
Pbsqrtsd_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::bB[[b25;b26;b27;b28;b29;b30;b31;b32]]::l))=true->
b8=false/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=true/\b23=false/\b22=false/\b21=false/\b20=true/\b19=false/\b18=true/\b17=false/\b26=true/\b25=true.

Proof.
idtac "Pbsqrtsd_bp_true Lemma 39/127".
unfold Pbsqrtsd_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[ring_simplify in Bp;congruence|];
destruct b22;[ring_simplify in Bp;congruence|];
destruct b23;[ring_simplify in Bp;congruence|];
destruct b24;[|ring_simplify in Bp;congruence];
destruct b25;[|ring_simplify in Bp;congruence];
destruct b26;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psbbl_rr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Psbbl_rr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=true/\b4=true/\b3=false/\b2=false/\b1=false/\b10=true/\b9=true.

Proof.
idtac "Psbbl_rr_bp_true Lemma 40/127".
unfold Psbbl_rr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Prep_movsl_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Prep_movsl_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=false/\b14=true/\b13=false/\b12=false/\b11=true/\b10=false/\b9=true.

Proof.
idtac "Prep_movsl_bp_true Lemma 41/127".
unfold Prep_movsl_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovsq_rm_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pmovsq_rm_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b8=true/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=false/\b23=true/\b22=true/\b21=true/\b20=true/\b19=true/\b18=true/\b17=false.

Proof.
idtac "Pmovsq_rm_bp_true Lemma 42/127".
unfold Pmovsq_rm_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[|ring_simplify in Bp;congruence];
destruct b23;[|ring_simplify in Bp;congruence];
destruct b24;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovsq_mr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pmovsq_mr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b8=false/\b7=true/\b6=true/\b5=false/\b4=false/\b3=true/\b2=true/\b1=false/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=false/\b23=true/\b22=true/\b21=false/\b20=true/\b19=false/\b18=true/\b17=true.

Proof.
idtac "Pmovsq_mr_bp_true Lemma 43/127".
unfold Pmovsq_mr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[|ring_simplify in Bp;congruence];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[ring_simplify in Bp;congruence|];
destruct b22;[|ring_simplify in Bp;congruence];
destruct b23;[|ring_simplify in Bp;congruence];
destruct b24;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pminsd_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 l,
Pminsd_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::bB[[b25;b26;b27;b28;b29;b30;b31;b32]]::l))=true->
b8=false/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=true/\b23=false/\b22=true/\b21=true/\b20=true/\b19=false/\b18=true/\b17=false/\b26=true/\b25=true.

Proof.
idtac "Pminsd_bp_true Lemma 44/127".
unfold Pminsd_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[|ring_simplify in Bp;congruence];
destruct b23;[ring_simplify in Bp;congruence|];
destruct b24;[|ring_simplify in Bp;congruence];
destruct b25;[|ring_simplify in Bp;congruence];
destruct b26;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmaxsd_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 l,
Pmaxsd_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::bB[[b25;b26;b27;b28;b29;b30;b31;b32]]::l))=true->
b8=false/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=true/\b23=true/\b22=true/\b21=true/\b20=true/\b19=false/\b18=true/\b17=false/\b26=true/\b25=true.

Proof.
idtac "Pmaxsd_bp_true Lemma 45/127".
unfold Pmaxsd_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[|ring_simplify in Bp;congruence];
destruct b23;[|ring_simplify in Bp;congruence];
destruct b24;[|ring_simplify in Bp;congruence];
destruct b25;[|ring_simplify in Bp;congruence];
destruct b26;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pbswap32_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pbswap32_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=false/\b3=false/\b2=false/\b1=false/\b10=true/\b9=true/\b13=true/\b12=false/\b11=false.

Proof.
idtac "Pbswap32_bp_true Lemma 46/127".
unfold Pbswap32_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pbsrl_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pbsrl_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=false/\b3=false/\b2=false/\b1=false/\b16=true/\b15=false/\b14=true/\b13=true/\b12=true/\b11=true/\b10=false/\b9=true/\b18=true/\b17=true.

Proof.
idtac "Pbsrl_bp_true Lemma 47/127".
unfold Pbsrl_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[|ring_simplify in Bp;congruence];
destruct b18;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pbsfl_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pbsfl_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=false/\b3=false/\b2=false/\b1=false/\b16=false/\b15=false/\b14=true/\b13=true/\b12=true/\b11=true/\b10=false/\b9=true/\b18=true/\b17=true.

Proof.
idtac "Pbsfl_bp_true Lemma 48/127".
unfold Pbsfl_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[ring_simplify in Bp;congruence|];
destruct b17;[|ring_simplify in Bp;congruence];
destruct b18;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Paddl_mi_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Paddl_mi_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=false/\b7=false/\b6=false/\b5=false/\b4=false/\b3=false/\b2=false/\b1=true/\b13=false/\b12=false/\b11=false.

Proof.
idtac "Paddl_mi_bp_true Lemma 49/127".
unfold Paddl_mi_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Paddl_rr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Paddl_rr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=false/\b4=false/\b3=false/\b2=false/\b1=false/\b10=true/\b9=true.

Proof.
idtac "Paddl_rr_bp_true Lemma 50/127".
unfold Paddl_rr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Padcl_rr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Padcl_rr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=false/\b4=true/\b3=false/\b2=false/\b1=false/\b10=true/\b9=true.

Proof.
idtac "Padcl_rr_bp_true Lemma 51/127".
unfold Padcl_rr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Padcl_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Padcl_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=false/\b5=false/\b4=false/\b3=false/\b2=false/\b1=true/\b10=true/\b9=true/\b13=false/\b12=true/\b11=false.

Proof.
idtac "Padcl_ri_bp_true Lemma 52/127".
unfold Padcl_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pjcc_rel_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pjcc_rel_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=false/\b3=false/\b2=false/\b1=false/\b12=false/\b11=false/\b10=false/\b9=true.

Proof.
idtac "Pjcc_rel_bp_true Lemma 53/127".
unfold Pjcc_rel_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pret_iw_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
Pret_iw_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b8=false/\b7=true/\b6=false/\b5=false/\b4=false/\b3=false/\b2=true/\b1=true.

Proof.
idtac "Pret_iw_bp_true Lemma 54/127".
unfold Pret_iw_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pret_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
Pret_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b8=true/\b7=true/\b6=false/\b5=false/\b4=false/\b3=false/\b2=true/\b1=true.

Proof.
idtac "Pret_bp_true Lemma 55/127".
unfold Pret_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcall_r_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pcall_r_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=true/\b3=true/\b2=true/\b1=true/\b10=true/\b9=true/\b13=false/\b12=true/\b11=false.

Proof.
idtac "Pcall_r_bp_true Lemma 56/127".
unfold Pcall_r_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcall_ofs_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
Pcall_ofs_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b8=false/\b7=false/\b6=false/\b5=true/\b4=false/\b3=true/\b2=true/\b1=true.

Proof.
idtac "Pcall_ofs_bp_true Lemma 57/127".
unfold Pcall_ofs_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pnop_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
Pnop_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b8=false/\b7=false/\b6=false/\b5=false/\b4=true/\b3=false/\b2=false/\b1=true.

Proof.
idtac "Pnop_bp_true Lemma 58/127".
unfold Pnop_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pjmp_Ev_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pjmp_Ev_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=true/\b3=true/\b2=true/\b1=true/\b13=false/\b12=false/\b11=true.

Proof.
idtac "Pjmp_Ev_bp_true Lemma 59/127".
unfold Pjmp_Ev_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pjmp_l_rel_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
Pjmp_l_rel_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=true/\b4=false/\b3=true/\b2=true/\b1=true.

Proof.
idtac "Pjmp_l_rel_bp_true Lemma 60/127".
unfold Pjmp_l_rel_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pandps_fm_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pandps_fm_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=false/\b3=false/\b2=false/\b1=false/\b16=false/\b15=false/\b14=false/\b13=true/\b12=true/\b11=false/\b10=true/\b9=false.

Proof.
idtac "Pandps_fm_bp_true Lemma 61/127".
unfold Pandps_fm_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pxorps_GvEv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pxorps_GvEv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=false/\b3=false/\b2=false/\b1=false/\b16=true/\b15=true/\b14=true/\b13=false/\b12=true/\b11=false/\b10=true/\b9=false.

Proof.
idtac "Pxorps_GvEv_bp_true Lemma 62/127".
unfold Pxorps_GvEv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pxorpd_GvEv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pxorpd_GvEv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b8=false/\b7=true/\b6=true/\b5=false/\b4=false/\b3=true/\b2=true/\b1=false/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=true/\b23=true/\b22=true/\b21=false/\b20=true/\b19=false/\b18=true/\b17=false.

Proof.
idtac "Pxorpd_GvEv_bp_true Lemma 63/127".
unfold Pxorpd_GvEv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[ring_simplify in Bp;congruence|];
destruct b22;[|ring_simplify in Bp;congruence];
destruct b23;[|ring_simplify in Bp;congruence];
destruct b24;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcomisd_ff_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 l,
Pcomisd_ff_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::bB[[b25;b26;b27;b28;b29;b30;b31;b32]]::l))=true->
b8=false/\b7=true/\b6=true/\b5=false/\b4=false/\b3=true/\b2=true/\b1=false/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=true/\b23=true/\b22=true/\b21=true/\b20=false/\b19=true/\b18=false/\b17=false/\b26=true/\b25=true.

Proof.
idtac "Pcomisd_ff_bp_true Lemma 64/127".
unfold Pcomisd_ff_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[ring_simplify in Bp;congruence|];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[|ring_simplify in Bp;congruence];
destruct b23;[|ring_simplify in Bp;congruence];
destruct b24;[|ring_simplify in Bp;congruence];
destruct b25;[|ring_simplify in Bp;congruence];
destruct b26;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pdivss_ff_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 l,
Pdivss_ff_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::bB[[b25;b26;b27;b28;b29;b30;b31;b32]]::l))=true->
b8=true/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=false/\b23=true/\b22=true/\b21=true/\b20=true/\b19=false/\b18=true/\b17=false/\b26=true/\b25=true.

Proof.
idtac "Pdivss_ff_bp_true Lemma 65/127".
unfold Pdivss_ff_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[|ring_simplify in Bp;congruence];
destruct b23;[|ring_simplify in Bp;congruence];
destruct b24;[ring_simplify in Bp;congruence|];
destruct b25;[|ring_simplify in Bp;congruence];
destruct b26;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pdivsd_ff_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 l,
Pdivsd_ff_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::bB[[b25;b26;b27;b28;b29;b30;b31;b32]]::l))=true->
b8=false/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=false/\b23=true/\b22=true/\b21=true/\b20=true/\b19=false/\b18=true/\b17=false/\b26=true/\b25=true.

Proof.
idtac "Pdivsd_ff_bp_true Lemma 66/127".
unfold Pdivsd_ff_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[|ring_simplify in Bp;congruence];
destruct b23;[|ring_simplify in Bp;congruence];
destruct b24;[ring_simplify in Bp;congruence|];
destruct b25;[|ring_simplify in Bp;congruence];
destruct b26;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmuld_ff_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 l,
Pmuld_ff_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::bB[[b25;b26;b27;b28;b29;b30;b31;b32]]::l))=true->
b8=false/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=true/\b23=false/\b22=false/\b21=true/\b20=true/\b19=false/\b18=true/\b17=false/\b26=true/\b25=true.

Proof.
idtac "Pmuld_ff_bp_true Lemma 67/127".
unfold Pmuld_ff_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[ring_simplify in Bp;congruence|];
destruct b23;[ring_simplify in Bp;congruence|];
destruct b24;[|ring_simplify in Bp;congruence];
destruct b25;[|ring_simplify in Bp;congruence];
destruct b26;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psubd_ff_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 l,
Psubd_ff_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::bB[[b25;b26;b27;b28;b29;b30;b31;b32]]::l))=true->
b8=false/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=false/\b23=false/\b22=true/\b21=true/\b20=true/\b19=false/\b18=true/\b17=false/\b26=true/\b25=true.

Proof.
idtac "Psubd_ff_bp_true Lemma 68/127".
unfold Psubd_ff_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[|ring_simplify in Bp;congruence];
destruct b23;[ring_simplify in Bp;congruence|];
destruct b24;[ring_simplify in Bp;congruence|];
destruct b25;[|ring_simplify in Bp;congruence];
destruct b26;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Paddd_ff_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 l,
Paddd_ff_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::bB[[b25;b26;b27;b28;b29;b30;b31;b32]]::l))=true->
b8=false/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=false/\b23=false/\b22=false/\b21=true/\b20=true/\b19=false/\b18=true/\b17=false/\b26=true/\b25=true.

Proof.
idtac "Paddd_ff_bp_true Lemma 69/127".
unfold Paddd_ff_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[ring_simplify in Bp;congruence|];
destruct b23;[ring_simplify in Bp;congruence|];
destruct b24;[ring_simplify in Bp;congruence|];
destruct b25;[|ring_simplify in Bp;congruence];
destruct b26;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psetcc_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Psetcc_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=false/\b3=false/\b2=false/\b1=false/\b12=true/\b11=false/\b10=false/\b9=true/\b18=true/\b17=true/\b21=false/\b20=false/\b19=false.

Proof.
idtac "Psetcc_bp_true Lemma 70/127".
unfold Psetcc_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b17;[|ring_simplify in Bp;congruence];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcmov_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pcmov_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=false/\b3=false/\b2=false/\b1=false/\b12=false/\b11=false/\b10=true/\b9=false/\b18=true/\b17=true.

Proof.
idtac "Pcmov_bp_true Lemma 71/127".
unfold Pcmov_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b17;[|ring_simplify in Bp;congruence];
destruct b18;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Ptestl_rr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Ptestl_rr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=true/\b5=false/\b4=false/\b3=false/\b2=false/\b1=true/\b10=true/\b9=true.

Proof.
idtac "Ptestl_rr_bp_true Lemma 72/127".
unfold Ptestl_rr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Ptestl_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Ptestl_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b10=true/\b9=true/\b13=false/\b12=false/\b11=false.

Proof.
idtac "Ptestl_ri_bp_true Lemma 73/127".
unfold Ptestl_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcmpl_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pcmpl_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=false/\b4=false/\b3=false/\b2=false/\b1=true/\b10=true/\b9=true/\b13=true/\b12=true/\b11=true.

Proof.
idtac "Pcmpl_ri_bp_true Lemma 74/127".
unfold Pcmpl_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcmpl_rr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pcmpl_rr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=true/\b4=true/\b3=true/\b2=false/\b1=false/\b10=true/\b9=true.

Proof.
idtac "Pcmpl_rr_bp_true Lemma 75/127".
unfold Pcmpl_rr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Prorl_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Prorl_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=false/\b4=false/\b3=false/\b2=true/\b1=true/\b13=true/\b12=false/\b11=false/\b10=true/\b9=true.

Proof.
idtac "Prorl_ri_bp_true Lemma 76/127".
unfold Prorl_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Prolw_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Prolw_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b8=false/\b7=true/\b6=true/\b5=false/\b4=false/\b3=true/\b2=true/\b1=false/\b16=true/\b15=false/\b14=false/\b13=false/\b12=false/\b11=false/\b10=true/\b9=true/\b18=true/\b17=true/\b21=false/\b20=false/\b19=false.

Proof.
idtac "Prolw_ri_bp_true Lemma 77/127".
unfold Prolw_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[|ring_simplify in Bp;congruence];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pshld_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pshld_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=false/\b3=false/\b2=false/\b1=false/\b16=false/\b15=false/\b14=true/\b13=false/\b12=false/\b11=true/\b10=false/\b9=true/\b18=true/\b17=true.

Proof.
idtac "Pshld_ri_bp_true Lemma 78/127".
unfold Pshld_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[ring_simplify in Bp;congruence|];
destruct b17;[|ring_simplify in Bp;congruence];
destruct b18;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psarl_rcl_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Psarl_rcl_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=false/\b5=false/\b4=true/\b3=false/\b2=true/\b1=true/\b10=true/\b9=true/\b13=true/\b12=true/\b11=true.

Proof.
idtac "Psarl_rcl_bp_true Lemma 79/127".
unfold Psarl_rcl_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psarl_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Psarl_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=false/\b4=false/\b3=false/\b2=true/\b1=true/\b10=true/\b9=true/\b13=true/\b12=true/\b11=true.

Proof.
idtac "Psarl_ri_bp_true Lemma 80/127".
unfold Psarl_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pshrl_rcl_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pshrl_rcl_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=false/\b5=false/\b4=true/\b3=false/\b2=true/\b1=true/\b10=true/\b9=true/\b13=true/\b12=false/\b11=true.

Proof.
idtac "Pshrl_rcl_bp_true Lemma 81/127".
unfold Pshrl_rcl_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pshrl_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pshrl_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=false/\b4=false/\b3=false/\b2=true/\b1=true/\b10=true/\b9=true/\b13=true/\b12=false/\b11=true.

Proof.
idtac "Pshrl_ri_bp_true Lemma 82/127".
unfold Pshrl_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psall_rcl_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Psall_rcl_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=false/\b5=false/\b4=true/\b3=false/\b2=true/\b1=true/\b10=true/\b9=true/\b13=false/\b12=false/\b11=true.

Proof.
idtac "Psall_rcl_bp_true Lemma 83/127".
unfold Psall_rcl_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psall_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Psall_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=false/\b4=false/\b3=false/\b2=true/\b1=true/\b10=true/\b9=true/\b13=false/\b12=false/\b11=true.

Proof.
idtac "Psall_ri_bp_true Lemma 84/127".
unfold Psall_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pnotl_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pnotl_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b10=true/\b9=true/\b13=false/\b12=true/\b11=false.

Proof.
idtac "Pnotl_bp_true Lemma 85/127".
unfold Pnotl_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pxorl_rr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pxorl_rr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=false/\b4=true/\b3=true/\b2=false/\b1=false/\b10=true/\b9=true.

Proof.
idtac "Pxorl_rr_bp_true Lemma 86/127".
unfold Pxorl_rr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pxorl_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pxorl_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=false/\b4=false/\b3=false/\b2=false/\b1=true/\b10=true/\b9=true/\b13=false/\b12=true/\b11=true.

Proof.
idtac "Pxorl_ri_bp_true Lemma 87/127".
unfold Pxorl_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Porl_rr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Porl_rr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=true/\b4=false/\b3=false/\b2=false/\b1=false/\b10=true/\b9=true.

Proof.
idtac "Porl_rr_bp_true Lemma 88/127".
unfold Porl_rr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Porl_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Porl_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=false/\b4=false/\b3=false/\b2=false/\b1=true/\b10=true/\b9=true/\b13=true/\b12=false/\b11=false.

Proof.
idtac "Porl_ri_bp_true Lemma 89/127".
unfold Porl_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pandl_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pandl_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=false/\b4=false/\b3=false/\b2=false/\b1=true/\b10=true/\b9=true/\b13=false/\b12=false/\b11=true.

Proof.
idtac "Pandl_ri_bp_true Lemma 90/127".
unfold Pandl_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pandl_rr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pandl_rr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=false/\b4=false/\b3=true/\b2=false/\b1=false/\b10=true/\b9=true.

Proof.
idtac "Pandl_rr_bp_true Lemma 91/127".
unfold Pandl_rr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pidivl_r_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pidivl_r_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b10=true/\b9=true/\b13=true/\b12=true/\b11=true.

Proof.
idtac "Pidivl_r_bp_true Lemma 92/127".
unfold Pidivl_r_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pdivl_r_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pdivl_r_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b10=true/\b9=true/\b13=false/\b12=true/\b11=true.

Proof.
idtac "Pdivl_r_bp_true Lemma 93/127".
unfold Pdivl_r_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcltd_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
Pcltd_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=true/\b4=true/\b3=false/\b2=false/\b1=true.

Proof.
idtac "Pcltd_bp_true Lemma 94/127".
unfold Pcltd_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmull_r_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pmull_r_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b10=true/\b9=true/\b13=false/\b12=false/\b11=true.

Proof.
idtac "Pmull_r_bp_true Lemma 95/127".
unfold Pmull_r_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pimull_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pimull_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=true/\b4=false/\b3=true/\b2=true/\b1=false/\b10=true/\b9=true.

Proof.
idtac "Pimull_ri_bp_true Lemma 96/127".
unfold Pimull_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pimull_rr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pimull_rr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=false/\b3=false/\b2=false/\b1=false/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=true/\b10=false/\b9=true/\b18=true/\b17=true.

Proof.
idtac "Pimull_rr_bp_true Lemma 97/127".
unfold Pimull_rr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[|ring_simplify in Bp;congruence];
destruct b18;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Psubl_rr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Psubl_rr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=false/\b5=true/\b4=false/\b3=true/\b2=false/\b1=false/\b10=true/\b9=true.

Proof.
idtac "Psubl_rr_bp_true Lemma 98/127".
unfold Psubl_rr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Paddl_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Paddl_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=false/\b4=false/\b3=false/\b2=false/\b1=true/\b10=true/\b9=true/\b13=false/\b12=false/\b11=false.

Proof.
idtac "Paddl_ri_bp_true Lemma 99/127".
unfold Paddl_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pnegl_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pnegl_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b10=true/\b9=true/\b13=true/\b12=true/\b11=false.

Proof.
idtac "Pnegl_bp_true Lemma 100/127".
unfold Pnegl_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pleal_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
Pleal_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b8=true/\b7=false/\b6=true/\b5=true/\b4=false/\b3=false/\b2=false/\b1=true.

Proof.
idtac "Pleal_bp_true Lemma 101/127".
unfold Pleal_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcvttss2si_rf_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 l,
Pcvttss2si_rf_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::bB[[b25;b26;b27;b28;b29;b30;b31;b32]]::l))=true->
b8=true/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=false/\b23=false/\b22=true/\b21=true/\b20=false/\b19=true/\b18=false/\b17=false/\b26=true/\b25=true.

Proof.
idtac "Pcvttss2si_rf_bp_true Lemma 102/127".
unfold Pcvttss2si_rf_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[ring_simplify in Bp;congruence|];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[|ring_simplify in Bp;congruence];
destruct b23;[ring_simplify in Bp;congruence|];
destruct b24;[ring_simplify in Bp;congruence|];
destruct b25;[|ring_simplify in Bp;congruence];
destruct b26;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcvtsi2sd_fr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 l,
Pcvtsi2sd_fr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::bB[[b25;b26;b27;b28;b29;b30;b31;b32]]::l))=true->
b8=false/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=false/\b23=true/\b22=false/\b21=true/\b20=false/\b19=true/\b18=false/\b17=false/\b26=true/\b25=true.

Proof.
idtac "Pcvtsi2sd_fr_bp_true Lemma 103/127".
unfold Pcvtsi2sd_fr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[ring_simplify in Bp;congruence|];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[ring_simplify in Bp;congruence|];
destruct b23;[|ring_simplify in Bp;congruence];
destruct b24;[ring_simplify in Bp;congruence|];
destruct b25;[|ring_simplify in Bp;congruence];
destruct b26;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcvtsi2ss_fr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 l,
Pcvtsi2ss_fr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::bB[[b25;b26;b27;b28;b29;b30;b31;b32]]::l))=true->
b8=true/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=false/\b23=true/\b22=false/\b21=true/\b20=false/\b19=true/\b18=false/\b17=false/\b26=true/\b25=true.

Proof.
idtac "Pcvtsi2ss_fr_bp_true Lemma 104/127".
unfold Pcvtsi2ss_fr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[ring_simplify in Bp;congruence|];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[ring_simplify in Bp;congruence|];
destruct b23;[|ring_simplify in Bp;congruence];
destruct b24;[ring_simplify in Bp;congruence|];
destruct b25;[|ring_simplify in Bp;congruence];
destruct b26;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcvttsd2si_rf_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 l,
Pcvttsd2si_rf_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::bB[[b25;b26;b27;b28;b29;b30;b31;b32]]::l))=true->
b8=false/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=false/\b23=false/\b22=true/\b21=true/\b20=false/\b19=true/\b18=false/\b17=false/\b26=true/\b25=true.

Proof.
idtac "Pcvttsd2si_rf_bp_true Lemma 105/127".
unfold Pcvttsd2si_rf_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[ring_simplify in Bp;congruence|];
destruct b19;[|ring_simplify in Bp;congruence];
destruct b20;[ring_simplify in Bp;congruence|];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[|ring_simplify in Bp;congruence];
destruct b23;[ring_simplify in Bp;congruence|];
destruct b24;[ring_simplify in Bp;congruence|];
destruct b25;[|ring_simplify in Bp;congruence];
destruct b26;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcvtss2sd_ff_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 l,
Pcvtss2sd_ff_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::bB[[b25;b26;b27;b28;b29;b30;b31;b32]]::l))=true->
b8=true/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=false/\b23=true/\b22=false/\b21=true/\b20=true/\b19=false/\b18=true/\b17=false/\b26=true/\b25=true.

Proof.
idtac "Pcvtss2sd_ff_bp_true Lemma 106/127".
unfold Pcvtss2sd_ff_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[ring_simplify in Bp;congruence|];
destruct b23;[|ring_simplify in Bp;congruence];
destruct b24;[ring_simplify in Bp;congruence|];
destruct b25;[|ring_simplify in Bp;congruence];
destruct b26;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pcvtsd2ss_ff_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 l,
Pcvtsd2ss_ff_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::bB[[b25;b26;b27;b28;b29;b30;b31;b32]]::l))=true->
b8=false/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=false/\b23=true/\b22=false/\b21=true/\b20=true/\b19=false/\b18=true/\b17=false/\b26=true/\b25=true.

Proof.
idtac "Pcvtsd2ss_ff_bp_true Lemma 107/127".
unfold Pcvtsd2ss_ff_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[|ring_simplify in Bp;congruence];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[|ring_simplify in Bp;congruence];
destruct b22;[ring_simplify in Bp;congruence|];
destruct b23;[|ring_simplify in Bp;congruence];
destruct b24;[ring_simplify in Bp;congruence|];
destruct b25;[|ring_simplify in Bp;congruence];
destruct b26;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovsw_GvEv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pmovsw_GvEv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=false/\b3=false/\b2=false/\b1=false/\b16=true/\b15=true/\b14=true/\b13=true/\b12=true/\b11=true/\b10=false/\b9=true.

Proof.
idtac "Pmovsw_GvEv_bp_true Lemma 108/127".
unfold Pmovsw_GvEv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovzw_GvEv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pmovzw_GvEv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=false/\b3=false/\b2=false/\b1=false/\b16=true/\b15=true/\b14=true/\b13=false/\b12=true/\b11=true/\b10=false/\b9=true.

Proof.
idtac "Pmovzw_GvEv_bp_true Lemma 109/127".
unfold Pmovzw_GvEv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovsb_GvEv_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pmovsb_GvEv_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=false/\b3=false/\b2=false/\b1=false/\b16=false/\b15=true/\b14=true/\b13=true/\b12=true/\b11=true/\b10=false/\b9=true.

Proof.
idtac "Pmovsb_GvEv_bp_true Lemma 110/127".
unfold Pmovsb_GvEv_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovzb_rm_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pmovzb_rm_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=true/\b4=false/\b3=false/\b2=false/\b1=false/\b16=false/\b15=true/\b14=true/\b13=false/\b12=true/\b11=true/\b10=false/\b9=true.

Proof.
idtac "Pmovzb_rm_bp_true Lemma 111/127".
unfold Pmovzb_rm_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[|ring_simplify in Bp;congruence];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[ring_simplify in Bp;congruence|];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovw_rm_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pmovw_rm_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=false/\b7=true/\b6=true/\b5=false/\b4=false/\b3=true/\b2=true/\b1=false/\b16=true/\b15=true/\b14=false/\b13=true/\b12=false/\b11=false/\b10=false/\b9=true.

Proof.
idtac "Pmovw_rm_bp_true Lemma 112/127".
unfold Pmovw_rm_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovw_mr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pmovw_mr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=false/\b7=true/\b6=true/\b5=false/\b4=false/\b3=true/\b2=true/\b1=false/\b16=true/\b15=false/\b14=false/\b13=true/\b12=false/\b11=false/\b10=false/\b9=true.

Proof.
idtac "Pmovw_mr_bp_true Lemma 113/127".
unfold Pmovw_mr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[ring_simplify in Bp;congruence|];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[ring_simplify in Bp;congruence|];
destruct b15;[ring_simplify in Bp;congruence|];
destruct b16;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovb_rm_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
Pmovb_rm_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b8=false/\b7=true/\b6=false/\b5=true/\b4=false/\b3=false/\b2=false/\b1=true.

Proof.
idtac "Pmovb_rm_bp_true Lemma 114/127".
unfold Pmovb_rm_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovb_mr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
Pmovb_mr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b8=false/\b7=false/\b6=false/\b5=true/\b4=false/\b3=false/\b2=false/\b1=true.

Proof.
idtac "Pmovb_mr_bp_true Lemma 115/127".
unfold Pmovb_mr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pxchg_rr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pxchg_rr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=true/\b6=true/\b5=false/\b4=false/\b3=false/\b2=false/\b1=true/\b10=true/\b9=true.

Proof.
idtac "Pxchg_rr_bp_true Lemma 116/127".
unfold Pxchg_rr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[|ring_simplify in Bp;congruence];
destruct b10;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pflds_m_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pflds_m_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=true/\b4=true/\b3=false/\b2=true/\b1=true/\b13=false/\b12=false/\b11=false.

Proof.
idtac "Pflds_m_bp_true Lemma 117/127".
unfold Pflds_m_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pfstps_m_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pfstps_m_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=true/\b4=true/\b3=false/\b2=true/\b1=true/\b13=true/\b12=true/\b11=false.

Proof.
idtac "Pfstps_m_bp_true Lemma 118/127".
unfold Pfstps_m_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pfstpl_m_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pfstpl_m_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=true/\b5=true/\b4=true/\b3=false/\b2=true/\b1=true/\b13=true/\b12=true/\b11=false.

Proof.
idtac "Pfstpl_m_bp_true Lemma 119/127".
unfold Pfstpl_m_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[|ring_simplify in Bp;congruence];
destruct b13;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pfldl_m_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 l,
Pfldl_m_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::l))=true->
b8=true/\b7=false/\b6=true/\b5=true/\b4=true/\b3=false/\b2=true/\b1=true/\b13=false/\b12=false/\b11=false.

Proof.
idtac "Pfldl_m_bp_true Lemma 120/127".
unfold Pfldl_m_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[|ring_simplify in Bp;congruence];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovss_fm_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pmovss_fm_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b8=true/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=false/\b23=false/\b22=false/\b21=false/\b20=true/\b19=false/\b18=false/\b17=false.

Proof.
idtac "Pmovss_fm_bp_true Lemma 121/127".
unfold Pmovss_fm_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[ring_simplify in Bp;congruence|];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[ring_simplify in Bp;congruence|];
destruct b22;[ring_simplify in Bp;congruence|];
destruct b23;[ring_simplify in Bp;congruence|];
destruct b24;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovss_mf_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pmovss_mf_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b8=true/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=true/\b23=false/\b22=false/\b21=false/\b20=true/\b19=false/\b18=false/\b17=false.

Proof.
idtac "Pmovss_mf_bp_true Lemma 122/127".
unfold Pmovss_mf_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[ring_simplify in Bp;congruence|];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[ring_simplify in Bp;congruence|];
destruct b22;[ring_simplify in Bp;congruence|];
destruct b23;[ring_simplify in Bp;congruence|];
destruct b24;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovsd_fm_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pmovsd_fm_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b8=false/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=false/\b23=false/\b22=false/\b21=false/\b20=true/\b19=false/\b18=false/\b17=false.

Proof.
idtac "Pmovsd_fm_bp_true Lemma 123/127".
unfold Pmovsd_fm_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[ring_simplify in Bp;congruence|];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[ring_simplify in Bp;congruence|];
destruct b22;[ring_simplify in Bp;congruence|];
destruct b23;[ring_simplify in Bp;congruence|];
destruct b24;[ring_simplify in Bp;congruence|];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovsd_mf_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 l,
Pmovsd_mf_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::bB[[b9;b10;b11;b12;b13;b14;b15;b16]]::bB[[b17;b18;b19;b20;b21;b22;b23;b24]]::l))=true->
b8=false/\b7=true/\b6=false/\b5=false/\b4=true/\b3=true/\b2=true/\b1=true/\b16=true/\b15=true/\b14=true/\b13=true/\b12=false/\b11=false/\b10=false/\b9=false/\b24=true/\b23=false/\b22=false/\b21=false/\b20=true/\b19=false/\b18=false/\b17=false.

Proof.
idtac "Pmovsd_mf_bp_true Lemma 124/127".
unfold Pmovsd_mf_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[|ring_simplify in Bp;congruence];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[ring_simplify in Bp;congruence|];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[ring_simplify in Bp;congruence|];
destruct b9;[ring_simplify in Bp;congruence|];
destruct b10;[ring_simplify in Bp;congruence|];
destruct b11;[ring_simplify in Bp;congruence|];
destruct b12;[ring_simplify in Bp;congruence|];
destruct b13;[|ring_simplify in Bp;congruence];
destruct b14;[|ring_simplify in Bp;congruence];
destruct b15;[|ring_simplify in Bp;congruence];
destruct b16;[|ring_simplify in Bp;congruence];
destruct b17;[ring_simplify in Bp;congruence|];
destruct b18;[ring_simplify in Bp;congruence|];
destruct b19;[ring_simplify in Bp;congruence|];
destruct b20;[|ring_simplify in Bp;congruence];
destruct b21;[ring_simplify in Bp;congruence|];
destruct b22;[ring_simplify in Bp;congruence|];
destruct b23;[ring_simplify in Bp;congruence|];
destruct b24;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovl_rm_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
Pmovl_rm_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b8=true/\b7=true/\b6=false/\b5=true/\b4=false/\b3=false/\b2=false/\b1=true.

Proof.
idtac "Pmovl_rm_bp_true Lemma 125/127".
unfold Pmovl_rm_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[|ring_simplify in Bp;congruence];
destruct b8;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovl_mr_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
Pmovl_mr_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b8=true/\b7=false/\b6=false/\b5=true/\b4=false/\b3=false/\b2=false/\b1=true.

Proof.
idtac "Pmovl_mr_bp_true Lemma 126/127".
unfold Pmovl_mr_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[ring_simplify in Bp;congruence|];
destruct b4;[ring_simplify in Bp;congruence|];
destruct b5;[|ring_simplify in Bp;congruence];
destruct b6;[ring_simplify in Bp;congruence|];
destruct b7;[ring_simplify in Bp;congruence|];
destruct b8;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.


Lemma Pmovl_ri_bp_true: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l,
Pmovl_ri_bp (bytes_to_bits_opt (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l))=true->
b4=true/\b3=true/\b2=false/\b1=true/\b5=true.

Proof.
idtac "Pmovl_ri_bp_true Lemma 127/127".
unfold Pmovl_ri_bp.
intros until l.
repeat rewrite bytes_to_bits_cons_correct by auto.
intro Bp.
destruct b1;[|ring_simplify in Bp;congruence];
destruct b2;[ring_simplify in Bp;congruence|];
destruct b3;[|ring_simplify in Bp;congruence];
destruct b4;[|ring_simplify in Bp;congruence];
destruct b5;[|ring_simplify in Bp;congruence];
repeat split;simpl in Bp;try congruence.
Qed.





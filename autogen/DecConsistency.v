Require Import Coqlib Integers Errors.
Require Import Hex lib.Bits Memdata.
Require Import Util Encode.
Import String Ascii.
Import List.
Import ListNotations.
Import Hex Bits.
Require Import EncDecRet VerificationCondition.
Require Import BFtrue.
Require Import BPProperty.
Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Arguments builtin_eq_dec l l' : simpl never.


(*speed up ltac*)
Ltac save48 H:=
  match type of H with
  |(if _ then _ else if _ then _ else if _ then _ else
    if _ then _ else if _ then _ else if _ then _ else 
    if _ then _ else if _ then _ else if _ then _ else
    if _ then _ else if _ then _ else if _ then _ else

    if _ then _ else if _ then _ else if _ then _ else
    if _ then _ else if _ then _ else if _ then _ else 
    if _ then _ else if _ then _ else if _ then _ else
    if _ then _ else if _ then _ else if _ then _ else 

    if _ then _ else if _ then _ else if _ then _ else
    if _ then _ else if _ then _ else if _ then _ else 
    if _ then _ else if _ then _ else if _ then _ else
    if _ then _ else if _ then _ else if _ then _ else

    if _ then _ else if _ then _ else if _ then _ else
    if _ then _ else if _ then _ else if _ then _ else 
    if _ then _ else if _ then _ else if _ then _ else
    if _ then _ else if _ then _ else if _ then _ else ?b0) = _ =>
    set (Hsave0:=b0) in H;

    try match b0 with
    |(if _ then _ else if _ then _ else if _ then _ else
      if _ then _ else if _ then _ else if _ then _ else 
      if _ then _ else if _ then _ else if _ then _ else
      if _ then _ else if _ then _ else if _ then _ else 
      
      if _ then _ else if _ then _ else if _ then _ else
      if _ then _ else if _ then _ else if _ then _ else 
      if _ then _ else if _ then _ else if _ then _ else
      if _ then _ else if _ then _ else if _ then _ else 
      
      if _ then _ else if _ then _ else if _ then _ else
      if _ then _ else if _ then _ else if _ then _ else 
      if _ then _ else if _ then _ else if _ then _ else
      if _ then _ else if _ then _ else if _ then _ else

      if _ then _ else if _ then _ else if _ then _ else
      if _ then _ else if _ then _ else if _ then _ else 
      if _ then _ else if _ then _ else if _ then _ else
      if _ then _ else if _ then _ else if _ then _ else ?b1)  =>
      set (Hsave1:=b1) in Hsave0;

      try match b1 with
      |(if _ then _ else if _ then _ else if _ then _ else
        if _ then _ else if _ then _ else if _ then _ else 
        if _ then _ else if _ then _ else if _ then _ else
        if _ then _ else if _ then _ else if _ then _ else 
        
        if _ then _ else if _ then _ else if _ then _ else
        if _ then _ else if _ then _ else if _ then _ else 
        if _ then _ else if _ then _ else if _ then _ else
        if _ then _ else if _ then _ else if _ then _ else 
        if _ then _ else if _ then _ else if _ then _ else

        if _ then _ else if _ then _ else if _ then _ else 
        if _ then _ else if _ then _ else if _ then _ else
        if _ then _ else if _ then _ else if _ then _ else

        if _ then _ else if _ then _ else if _ then _ else
        if _ then _ else if _ then _ else if _ then _ else 
        if _ then _ else if _ then _ else if _ then _ else
        if _ then _ else if _ then _ else if _ then _ else ?b2)  =>
      set (Hsave2:=b2) in Hsave1;

        try match b2 with
        |(if _ then _ else if _ then _ else if _ then _ else
          if _ then _ else if _ then _ else if _ then _ else 
          if _ then _ else if _ then _ else if _ then _ else
          if _ then _ else if _ then _ else if _ then _ else 
          
          if _ then _ else if _ then _ else if _ then _ else
          if _ then _ else if _ then _ else if _ then _ else 
          if _ then _ else if _ then _ else if _ then _ else
          if _ then _ else if _ then _ else if _ then _ else 
          
          if _ then _ else if _ then _ else if _ then _ else
          if _ then _ else if _ then _ else if _ then _ else 
          if _ then _ else if _ then _ else if _ then _ else
          if _ then _ else if _ then _ else if _ then _ else
      
          if _ then _ else if _ then _ else if _ then _ else
          if _ then _ else if _ then _ else if _ then _ else 
          if _ then _ else if _ then _ else if _ then _ else
          if _ then _ else if _ then _ else if _ then _ else ?b3)  =>
        set (Hsave3:=b3) in Hsave2
        end
        end
        end
end.  

Lemma decode_AddrE_consistency: 
forall b1 b2 b3 b4 b5 b6 b7 b8 l len k, 
decode_AddrE (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l) = OK (k,len) ->
exists l1 l2, l=l1++l2 /\ len=S (length l1) /\ encode_AddrE k bB[[false;false;b3;b4;b5;false;false;false]] = OK (bB[[b1;b2;b3;b4;b5;b6;b7;b8]]::l1).
Proof.
idtac "========== Start to prove Decode AddrE Consistency ==========".
intros until k. 
intro Dec. unfold decode_AddrE in Dec. 
(*prove AddrE12*)
idtac "Decode Consistency: AddrE12 1/10".
try clear Bp.
destruct AddrE12_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].

apply AddrE12_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove AddrE11*)
idtac "Decode Consistency: AddrE11 2/10".
try clear Bp.
destruct AddrE11_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].

apply AddrE11_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
solve_try_first_n_decode EQ1 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove AddrE10*)
idtac "Decode Consistency: AddrE10 3/10".
try clear Bp.
destruct AddrE10_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *.
unfold AddrE10_bp in Bp;simpl in Bp;congruence.
destr_byte ii.

apply AddrE10_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove AddrE9*)
idtac "Decode Consistency: AddrE9 4/10".
try clear Bp.
destruct AddrE9_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *.
unfold AddrE9_bp in Bp;simpl in Bp;congruence.
destr_byte ii.

apply AddrE9_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove AddrE8*)
idtac "Decode Consistency: AddrE8 5/10".
try clear Bp.
destruct AddrE8_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *.
unfold AddrE8_bp in Bp;simpl in Bp;congruence.
destr_byte ii.

apply AddrE8_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove AddrE7*)
idtac "Decode Consistency: AddrE7 6/10".
try clear Bp.
destruct AddrE7_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *.
unfold AddrE7_bp in Bp;simpl in Bp;congruence.
destr_byte ii.

apply AddrE7_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_first_n_decode EQ0 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ2.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove AddrE6*)
idtac "Decode Consistency: AddrE6 7/10".
try clear Bp.
destruct AddrE6_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].

apply AddrE6_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_first_n_decode EQ0 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ2.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove AddrE5*)
idtac "Decode Consistency: AddrE5 8/10".
try clear Bp.
destruct AddrE5_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *.
unfold AddrE5_bp in Bp;simpl in Bp;congruence.
destr_byte ii.

apply AddrE5_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove AddrE4*)
idtac "Decode Consistency: AddrE4 9/10".
try clear Bp.
destruct AddrE4_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *.
unfold AddrE4_bp in Bp;simpl in Bp;congruence.
destr_byte ii.

apply AddrE4_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove AddrE0*)
idtac "Decode Consistency: AddrE0 10/10".
try clear Bp.
destruct AddrE0_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].

apply AddrE0_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

congruence.


Qed.

Lemma decode_AddrE_len: 
forall l len k, decode_AddrE l=OK(k,len)->
len>=1.
Proof.
idtac "========== Start to prove Decode AddrE Gt Len ==========".
intros until k.
induction k;
intro Dec;
unfold decode_AddrE in Dec.
idtac "Decode Gt Len: AddrE12 1/10".
do 0 simpl_branch_decode Dec.
destruct AddrE12_bp eqn:Bp;[|do 9 simpl_branch_decode Dec].
monadInv_decode Dec.
omega.

idtac "Decode Gt Len: AddrE11 2/10".
do 1 simpl_branch_decode Dec.
destruct AddrE11_bp eqn:Bp;[|do 8 simpl_branch_decode Dec].
monadInv_decode Dec.
omega.

idtac "Decode Gt Len: AddrE10 3/10".
do 2 simpl_branch_decode Dec.
destruct AddrE10_bp eqn:Bp;[|do 7 simpl_branch_decode Dec].
monadInv_decode Dec.
omega.

idtac "Decode Gt Len: AddrE9 4/10".
do 3 simpl_branch_decode Dec.
destruct AddrE9_bp eqn:Bp;[|do 6 simpl_branch_decode Dec].
monadInv_decode Dec.
omega.

idtac "Decode Gt Len: AddrE8 5/10".
do 4 simpl_branch_decode Dec.
destruct AddrE8_bp eqn:Bp;[|do 5 simpl_branch_decode Dec].
monadInv_decode Dec.
omega.

idtac "Decode Gt Len: AddrE7 6/10".
do 5 simpl_branch_decode Dec.
destruct AddrE7_bp eqn:Bp;[|do 4 simpl_branch_decode Dec].
monadInv_decode Dec.
omega.

idtac "Decode Gt Len: AddrE6 7/10".
do 6 simpl_branch_decode Dec.
destruct AddrE6_bp eqn:Bp;[|do 3 simpl_branch_decode Dec].
monadInv_decode Dec.
omega.

idtac "Decode Gt Len: AddrE5 8/10".
do 7 simpl_branch_decode Dec.
destruct AddrE5_bp eqn:Bp;[|do 2 simpl_branch_decode Dec].
monadInv_decode Dec.
omega.

idtac "Decode Gt Len: AddrE4 9/10".
do 8 simpl_branch_decode Dec.
destruct AddrE4_bp eqn:Bp;[|do 1 simpl_branch_decode Dec].
monadInv_decode Dec.
omega.

idtac "Decode Gt Len: AddrE0 10/10".
do 9 simpl_branch_decode Dec.
destruct AddrE0_bp eqn:Bp;[|congruence].
monadInv_decode Dec.
omega.

Qed.


Lemma decode_Instruction_consistency: 
forall l l' k, decode_Instruction (l++l') = OK (k,length l) ->
encode_Instruction k = OK l.
Proof.
idtac "========== Start to prove Decode Instruction Consistency ==========".
intros until k. 
intro Dec. unfold decode_Instruction in Dec. 
save48 Dec.
(*prove Ptestq_EvGv*)
idtac "Decode Consistency: Ptestq_EvGv 1/127".
try clear Bp.
destruct Ptestq_EvGv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Ptestq_EvGv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 133%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Ptestq_ri*)
idtac "Decode Consistency: Ptestq_ri 2/127".
try clear Bp.
destruct Ptestq_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.

apply Ptestq_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 247%Z.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
solve_try_first_n_decode EQ4 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ5.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcmpq_GvEv*)
idtac "Decode Consistency: Pcmpq_GvEv 3/127".
try clear Bp.
destruct Pcmpq_GvEv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pcmpq_GvEv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 59%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcmpq_EvGv*)
idtac "Decode Consistency: Pcmpq_EvGv 4/127".
try clear Bp.
destruct Pcmpq_EvGv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pcmpq_EvGv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 57%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcmpq_ri*)
idtac "Decode Consistency: Pcmpq_ri 5/127".
try clear Bp.
destruct Pcmpq_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.

apply Pcmpq_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 129%Z.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
solve_try_first_n_decode EQ4 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ5.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Prorq_ri*)
idtac "Decode Consistency: Prorq_ri 6/127".
try clear Bp.
destruct Prorq_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.

apply Prorq_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 193%Z.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
solve_try_first_n_decode EQ4 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ5.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psarq_ri*)
idtac "Decode Consistency: Psarq_ri 7/127".
try clear Bp.
destruct Psarq_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.

apply Psarq_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 193%Z.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
solve_try_first_n_decode EQ4 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ5.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psarq_rcl*)
idtac "Decode Consistency: Psarq_rcl 8/127".
try clear Bp.
destruct Psarq_rcl_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.

apply Psarq_rcl_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 211%Z.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psalq_ri*)
idtac "Decode Consistency: Psalq_ri 9/127".
try clear Bp.
destruct Psalq_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.

apply Psalq_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 193%Z.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
solve_try_first_n_decode EQ4 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ5.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psalq_rcl*)
idtac "Decode Consistency: Psalq_rcl 10/127".
try clear Bp.
destruct Psalq_rcl_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.

apply Psalq_rcl_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 211%Z.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pnotq*)
idtac "Decode Consistency: Pnotq 11/127".
try clear Bp.
destruct Pnotq_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.

apply Pnotq_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 247%Z.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pxorq_GvEv*)
idtac "Decode Consistency: Pxorq_GvEv 12/127".
try clear Bp.
destruct Pxorq_GvEv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pxorq_GvEv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 51%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pxorq_EvGv*)
idtac "Decode Consistency: Pxorq_EvGv 13/127".
try clear Bp.
destruct Pxorq_EvGv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pxorq_EvGv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 49%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pxorq_ri*)
idtac "Decode Consistency: Pxorq_ri 14/127".
try clear Bp.
destruct Pxorq_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.

apply Pxorq_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 129%Z.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
solve_try_first_n_decode EQ4 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ5.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Porq_GvEv*)
idtac "Decode Consistency: Porq_GvEv 15/127".
try clear Bp.
destruct Porq_GvEv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Porq_GvEv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 11%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Porq_EvGv*)
idtac "Decode Consistency: Porq_EvGv 16/127".
try clear Bp.
destruct Porq_EvGv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Porq_EvGv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 9%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Porq_ri*)
idtac "Decode Consistency: Porq_ri 17/127".
try clear Bp.
destruct Porq_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.

apply Porq_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 129%Z.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
solve_try_first_n_decode EQ4 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ5.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pandq_GvEv*)
idtac "Decode Consistency: Pandq_GvEv 18/127".
try clear Bp.
destruct Pandq_GvEv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pandq_GvEv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 35%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pandq_EvGv*)
idtac "Decode Consistency: Pandq_EvGv 19/127".
try clear Bp.
destruct Pandq_EvGv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pandq_EvGv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 33%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pandq_ri*)
idtac "Decode Consistency: Pandq_ri 20/127".
try clear Bp.
destruct Pandq_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.

apply Pandq_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 129%Z.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
solve_try_first_n_decode EQ4 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ5.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pdivq*)
idtac "Decode Consistency: Pdivq 21/127".
try clear Bp.
destruct Pdivq_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pdivq_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 247%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pidivq*)
idtac "Decode Consistency: Pidivq 22/127".
try clear Bp.
destruct Pidivq_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pidivq_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 247%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmulq_r*)
idtac "Decode Consistency: Pmulq_r 23/127".
try clear Bp.
destruct Pmulq_r_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pmulq_r_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 247%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pimulq_GvEv*)
idtac "Decode Consistency: Pimulq_GvEv 24/127".
try clear Bp.
destruct Pimulq_GvEv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pimulq_GvEv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ2.
destruct_const_byte_rewrite 175%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ4;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ3.
solve_kls_decode EQ4 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ5.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pimulq_r*)
idtac "Decode Consistency: Pimulq_r 25/127".
try clear Bp.
destruct Pimulq_r_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pimulq_r_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 247%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pimulq_ri*)
idtac "Decode Consistency: Pimulq_ri 26/127".
try clear Bp.
destruct Pimulq_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pimulq_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 105%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
solve_try_first_n_decode EQ4 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ5.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psubq_GvEv*)
idtac "Decode Consistency: Psubq_GvEv 27/127".
try clear Bp.
destruct Psubq_GvEv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Psubq_GvEv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 43%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psubq_EvGv*)
idtac "Decode Consistency: Psubq_EvGv 28/127".
try clear Bp.
destruct Psubq_EvGv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Psubq_EvGv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 41%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psubq_ri*)
idtac "Decode Consistency: Psubq_ri 29/127".
try clear Bp.
destruct Psubq_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.

apply Psubq_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 129%Z.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
solve_try_first_n_decode EQ4 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ5.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Paddq_GvEv*)
idtac "Decode Consistency: Paddq_GvEv 30/127".
try clear Bp.
destruct Paddq_GvEv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Paddq_GvEv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 3%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Paddq_EvGv*)
idtac "Decode Consistency: Paddq_EvGv 31/127".
try clear Bp.
destruct Paddq_EvGv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Paddq_EvGv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 1%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Paddq_ri*)
idtac "Decode Consistency: Paddq_ri 32/127".
try clear Bp.
destruct Paddq_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.

apply Paddq_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 129%Z.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
solve_try_first_n_decode EQ4 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ5.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pnegq*)
idtac "Decode Consistency: Pnegq 33/127".
try clear Bp.
destruct Pnegq_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.

apply Pnegq_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 247%Z.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pleaq*)
idtac "Decode Consistency: Pleaq 34/127".
try clear Bp.
destruct Pleaq_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pleaq_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 141%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovq_EvGv*)
idtac "Decode Consistency: Pmovq_EvGv 35/127".
try clear Bp.
destruct Pmovq_EvGv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovq_EvGv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 137%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovq_GvEv*)
idtac "Decode Consistency: Pmovq_GvEv 36/127".
try clear Bp.
destruct Pmovq_GvEv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovq_GvEv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 139%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovq_ri*)
idtac "Decode Consistency: Pmovq_ri 37/127".
try clear Bp.
destruct Pmovq_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovq_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_get_n_decode EQ0.
solve_try_skip_n_decode EQ2.
solve_try_first_n_decode EQ3 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psubl_ri*)
idtac "Decode Consistency: Psubl_ri 38/127".
try clear Bp.
destruct Psubl_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Psubl_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 129%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pbsqrtsd*)
idtac "Decode Consistency: Pbsqrtsd 39/127".
try clear Bp.
destruct Pbsqrtsd_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pbsqrtsd_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 242%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 81%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psbbl_rr*)
idtac "Decode Consistency: Psbbl_rr 40/127".
try clear Bp.
destruct Psbbl_rr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Psbbl_rr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 25%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Prep_movsl*)
idtac "Decode Consistency: Prep_movsl 41/127".
try clear Bp.
destruct Prep_movsl_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Prep_movsl_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 243%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 165%Z.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovsq_rm*)
idtac "Decode Consistency: Pmovsq_rm 42/127".
try clear Bp.
destruct Pmovsq_rm_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovsq_rm_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 243%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 126%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovsq_mr*)
idtac "Decode Consistency: Pmovsq_mr 43/127".
try clear Bp.
destruct Pmovsq_mr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovsq_mr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 102%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 214%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pminsd*)
idtac "Decode Consistency: Pminsd 44/127".
try clear Bp.
destruct Pminsd_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pminsd_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 242%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 93%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmaxsd*)
idtac "Decode Consistency: Pmaxsd 45/127".
try clear Bp.
destruct Pmaxsd_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pmaxsd_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 242%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 95%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pbswap32*)
idtac "Decode Consistency: Pbswap32 46/127".
try clear Bp.
destruct Pbswap32_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pbswap32_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 15%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pbsrl*)
idtac "Decode Consistency: Pbsrl 47/127".
try clear Bp.
destruct Pbsrl_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pbsrl_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 189%Z.
solve_try_get_n_decode EQ0.
solve_try_skip_n_decode EQ2.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pbsfl*)
idtac "Decode Consistency: Pbsfl 48/127".
try clear Bp.
destruct Pbsfl_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pbsfl_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 188%Z.
solve_try_get_n_decode EQ0.
solve_try_skip_n_decode EQ2.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Paddl_mi*)
idtac "Decode Consistency: Paddl_mi 49/127".
try clear Bp.
unfold Hsave0 in Dec.
destruct Paddl_mi_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ1;simpl in Decode_Len;omega.
destr_byte ii.

apply Paddl_mi_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 128%Z.
solve_kls_decode EQ1 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Paddl_rr*)
idtac "Decode Consistency: Paddl_rr 50/127".
try clear Bp.
destruct Paddl_rr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Paddl_rr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 1%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Padcl_rr*)
idtac "Decode Consistency: Padcl_rr 51/127".
try clear Bp.
destruct Padcl_rr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Padcl_rr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 17%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Padcl_ri*)
idtac "Decode Consistency: Padcl_ri 52/127".
try clear Bp.
destruct Padcl_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Padcl_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 131%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pjcc_rel*)
idtac "Decode Consistency: Pjcc_rel 53/127".
try clear Bp.
destruct Pjcc_rel_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pjcc_rel_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 15%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pret_iw*)
idtac "Decode Consistency: Pret_iw 54/127".
try clear Bp.
destruct Pret_iw_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pret_iw_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 194%Z.
solve_try_first_n_decode EQ1 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pret*)
idtac "Decode Consistency: Pret 55/127".
try clear Bp.
destruct Pret_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pret_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 195%Z.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcall_r*)
idtac "Decode Consistency: Pcall_r 56/127".
try clear Bp.
destruct Pcall_r_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pcall_r_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 255%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcall_ofs*)
idtac "Decode Consistency: Pcall_ofs 57/127".
try clear Bp.
destruct Pcall_ofs_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pcall_ofs_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 232%Z.
solve_try_first_n_decode EQ1 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pnop*)
idtac "Decode Consistency: Pnop 58/127".
try clear Bp.
destruct Pnop_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pnop_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 144%Z.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pjmp_Ev*)
idtac "Decode Consistency: Pjmp_Ev 59/127".
try clear Bp.
destruct Pjmp_Ev_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ1;simpl in Decode_Len;omega.
destr_byte ii.

apply Pjmp_Ev_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 255%Z.
solve_kls_decode EQ1 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pjmp_l_rel*)
idtac "Decode Consistency: Pjmp_l_rel 60/127".
try clear Bp.
destruct Pjmp_l_rel_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pjmp_l_rel_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 233%Z.
solve_try_first_n_decode EQ1 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pandps_fm*)
idtac "Decode Consistency: Pandps_fm 61/127".
try clear Bp.
destruct Pandps_fm_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pandps_fm_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 88%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ0.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pxorps_GvEv*)
idtac "Decode Consistency: Pxorps_GvEv 62/127".
try clear Bp.
destruct Pxorps_GvEv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pxorps_GvEv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 87%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ0.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pxorpd_GvEv*)
idtac "Decode Consistency: Pxorpd_GvEv 63/127".
try clear Bp.
destruct Pxorpd_GvEv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pxorpd_GvEv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 102%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 87%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcomisd_ff*)
idtac "Decode Consistency: Pcomisd_ff 64/127".
try clear Bp.
destruct Pcomisd_ff_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pcomisd_ff_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 102%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 47%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pdivss_ff*)
idtac "Decode Consistency: Pdivss_ff 65/127".
try clear Bp.
destruct Pdivss_ff_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pdivss_ff_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 243%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 94%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pdivsd_ff*)
idtac "Decode Consistency: Pdivsd_ff 66/127".
try clear Bp.
destruct Pdivsd_ff_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pdivsd_ff_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 242%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 94%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmuld_ff*)
idtac "Decode Consistency: Pmuld_ff 67/127".
try clear Bp.
destruct Pmuld_ff_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pmuld_ff_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 242%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 89%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psubd_ff*)
idtac "Decode Consistency: Psubd_ff 68/127".
try clear Bp.
destruct Psubd_ff_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Psubd_ff_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 242%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 92%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Paddd_ff*)
idtac "Decode Consistency: Paddd_ff 69/127".
try clear Bp.
destruct Paddd_ff_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Paddd_ff_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 242%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 88%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psetcc*)
idtac "Decode Consistency: Psetcc 70/127".
try clear Bp.
destruct Psetcc_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Psetcc_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 15%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcmov*)
idtac "Decode Consistency: Pcmov 71/127".
try clear Bp.
destruct Pcmov_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pcmov_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 15%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Ptestl_rr*)
idtac "Decode Consistency: Ptestl_rr 72/127".
try clear Bp.
destruct Ptestl_rr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Ptestl_rr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 133%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Ptestl_ri*)
idtac "Decode Consistency: Ptestl_ri 73/127".
try clear Bp.
destruct Ptestl_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Ptestl_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 247%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcmpl_ri*)
idtac "Decode Consistency: Pcmpl_ri 74/127".
try clear Bp.
destruct Pcmpl_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pcmpl_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 129%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcmpl_rr*)
idtac "Decode Consistency: Pcmpl_rr 75/127".
try clear Bp.
destruct Pcmpl_rr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pcmpl_rr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 57%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Prorl_ri*)
idtac "Decode Consistency: Prorl_ri 76/127".
try clear Bp.
destruct Prorl_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Prorl_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 193%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Prolw_ri*)
idtac "Decode Consistency: Prolw_ri 77/127".
try clear Bp.
destruct Prolw_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Prolw_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 102%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 193%Z.
solve_try_get_n_decode EQ0.
solve_try_skip_n_decode EQ2.
solve_try_first_n_decode EQ3 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pshld_ri*)
idtac "Decode Consistency: Pshld_ri 78/127".
try clear Bp.
destruct Pshld_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pshld_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 164%Z.
solve_try_get_n_decode EQ0.
solve_try_skip_n_decode EQ2.
solve_try_first_n_decode EQ3 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psarl_rcl*)
idtac "Decode Consistency: Psarl_rcl 79/127".
try clear Bp.
destruct Psarl_rcl_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Psarl_rcl_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 211%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psarl_ri*)
idtac "Decode Consistency: Psarl_ri 80/127".
try clear Bp.
destruct Psarl_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Psarl_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 193%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pshrl_rcl*)
idtac "Decode Consistency: Pshrl_rcl 81/127".
try clear Bp.
destruct Pshrl_rcl_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pshrl_rcl_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 211%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pshrl_ri*)
idtac "Decode Consistency: Pshrl_ri 82/127".
try clear Bp.
destruct Pshrl_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pshrl_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 193%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psall_rcl*)
idtac "Decode Consistency: Psall_rcl 83/127".
try clear Bp.
destruct Psall_rcl_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Psall_rcl_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 211%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psall_ri*)
idtac "Decode Consistency: Psall_ri 84/127".
try clear Bp.
destruct Psall_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Psall_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 193%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pnotl*)
idtac "Decode Consistency: Pnotl 85/127".
try clear Bp.
destruct Pnotl_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pnotl_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 247%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pxorl_rr*)
idtac "Decode Consistency: Pxorl_rr 86/127".
try clear Bp.
destruct Pxorl_rr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pxorl_rr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 49%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pxorl_ri*)
idtac "Decode Consistency: Pxorl_ri 87/127".
try clear Bp.
destruct Pxorl_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pxorl_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 129%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Porl_rr*)
idtac "Decode Consistency: Porl_rr 88/127".
try clear Bp.
destruct Porl_rr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Porl_rr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 9%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Porl_ri*)
idtac "Decode Consistency: Porl_ri 89/127".
try clear Bp.
destruct Porl_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Porl_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 129%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pandl_ri*)
idtac "Decode Consistency: Pandl_ri 90/127".
try clear Bp.
destruct Pandl_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pandl_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 129%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pandl_rr*)
idtac "Decode Consistency: Pandl_rr 91/127".
try clear Bp.
destruct Pandl_rr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pandl_rr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 33%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pidivl_r*)
idtac "Decode Consistency: Pidivl_r 92/127".
try clear Bp.
destruct Pidivl_r_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pidivl_r_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 247%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pdivl_r*)
idtac "Decode Consistency: Pdivl_r 93/127".
try clear Bp.
destruct Pdivl_r_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pdivl_r_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 247%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcltd*)
idtac "Decode Consistency: Pcltd 94/127".
try clear Bp.
destruct Pcltd_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pcltd_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 153%Z.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmull_r*)
idtac "Decode Consistency: Pmull_r 95/127".
try clear Bp.
destruct Pmull_r_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pmull_r_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 247%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pimull_ri*)
idtac "Decode Consistency: Pimull_ri 96/127".
try clear Bp.
destruct Pimull_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pimull_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 105%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pimull_rr*)
idtac "Decode Consistency: Pimull_rr 97/127".
try clear Bp.
unfold Hsave1 in Dec.
destruct Pimull_rr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pimull_rr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 175%Z.
solve_try_get_n_decode EQ0.
solve_try_skip_n_decode EQ2.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Psubl_rr*)
idtac "Decode Consistency: Psubl_rr 98/127".
try clear Bp.
destruct Psubl_rr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Psubl_rr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 43%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Paddl_ri*)
idtac "Decode Consistency: Paddl_ri 99/127".
try clear Bp.
destruct Paddl_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Paddl_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 129%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
solve_try_first_n_decode EQ2 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pnegl*)
idtac "Decode Consistency: Pnegl 100/127".
try clear Bp.
destruct Pnegl_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pnegl_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 247%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pleal*)
idtac "Decode Consistency: Pleal 101/127".
try clear Bp.
destruct Pleal_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pleal_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 141%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ0;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ1.
solve_kls_decode EQ0 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ2.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcvttss2si_rf*)
idtac "Decode Consistency: Pcvttss2si_rf 102/127".
try clear Bp.
destruct Pcvttss2si_rf_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pcvttss2si_rf_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 243%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 44%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcvtsi2sd_fr*)
idtac "Decode Consistency: Pcvtsi2sd_fr 103/127".
try clear Bp.
destruct Pcvtsi2sd_fr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pcvtsi2sd_fr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 242%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 42%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcvtsi2ss_fr*)
idtac "Decode Consistency: Pcvtsi2ss_fr 104/127".
try clear Bp.
destruct Pcvtsi2ss_fr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pcvtsi2ss_fr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 243%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 42%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcvttsd2si_rf*)
idtac "Decode Consistency: Pcvttsd2si_rf 105/127".
try clear Bp.
destruct Pcvttsd2si_rf_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pcvttsd2si_rf_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 242%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 44%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcvtss2sd_ff*)
idtac "Decode Consistency: Pcvtss2sd_ff 106/127".
try clear Bp.
destruct Pcvtss2sd_ff_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pcvtss2sd_ff_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 243%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 90%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pcvtsd2ss_ff*)
idtac "Decode Consistency: Pcvtsd2ss_ff 107/127".
try clear Bp.
destruct Pcvtsd2ss_ff_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pcvtsd2ss_ff_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 242%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 90%Z.
solve_try_get_n_decode EQ2.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovsw_GvEv*)
idtac "Decode Consistency: Pmovsw_GvEv 108/127".
try clear Bp.
destruct Pmovsw_GvEv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovsw_GvEv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 191%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ0.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovzw_GvEv*)
idtac "Decode Consistency: Pmovzw_GvEv 109/127".
try clear Bp.
destruct Pmovzw_GvEv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovzw_GvEv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 183%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ0.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovsb_GvEv*)
idtac "Decode Consistency: Pmovsb_GvEv 110/127".
try clear Bp.
destruct Pmovsb_GvEv_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovsb_GvEv_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 190%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ0.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovzb_rm*)
idtac "Decode Consistency: Pmovzb_rm 111/127".
try clear Bp.
destruct Pmovzb_rm_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovzb_rm_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 182%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ0.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovw_rm*)
idtac "Decode Consistency: Pmovw_rm 112/127".
try clear Bp.
destruct Pmovw_rm_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovw_rm_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 102%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 139%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ0.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovw_mr*)
idtac "Decode Consistency: Pmovw_mr 113/127".
try clear Bp.
destruct Pmovw_mr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovw_mr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 102%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 137%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ2;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ0.
solve_kls_decode EQ2 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ3.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovb_rm*)
idtac "Decode Consistency: Pmovb_rm 114/127".
try clear Bp.
destruct Pmovb_rm_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovb_rm_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 138%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ0;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ1.
solve_kls_decode EQ0 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ2.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovb_mr*)
idtac "Decode Consistency: Pmovb_mr 115/127".
try clear Bp.
destruct Pmovb_mr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovb_mr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 136%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ0;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ1.
solve_kls_decode EQ0 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ2.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pxchg_rr*)
idtac "Decode Consistency: Pxchg_rr 116/127".
try clear Bp.
destruct Pxchg_rr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l;[|simpl in Decode_Len;congruence].

apply Pxchg_rr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 135%Z.
solve_try_get_n_decode EQ1.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pflds_m*)
idtac "Decode Consistency: Pflds_m 117/127".
try clear Bp.
destruct Pflds_m_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ1;simpl in Decode_Len;omega.
destr_byte ii.

apply Pflds_m_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 217%Z.
solve_kls_decode EQ1 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pfstps_m*)
idtac "Decode Consistency: Pfstps_m 118/127".
try clear Bp.
destruct Pfstps_m_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ1;simpl in Decode_Len;omega.
destr_byte ii.

apply Pfstps_m_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 217%Z.
solve_kls_decode EQ1 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pfstpl_m*)
idtac "Decode Consistency: Pfstpl_m 119/127".
try clear Bp.
destruct Pfstpl_m_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ1;simpl in Decode_Len;omega.
destr_byte ii.

apply Pfstpl_m_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 221%Z.
solve_kls_decode EQ1 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pfldl_m*)
idtac "Decode Consistency: Pfldl_m 120/127".
try clear Bp.
destruct Pfldl_m_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
apply decode_AddrE_len in EQ1;simpl in Decode_Len;omega.
destr_byte ii.

apply Pfldl_m_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 221%Z.
solve_kls_decode EQ1 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ0.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovss_fm*)
idtac "Decode Consistency: Pmovss_fm 121/127".
try clear Bp.
destruct Pmovss_fm_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovss_fm_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 243%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 16%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovss_mf*)
idtac "Decode Consistency: Pmovss_mf 122/127".
try clear Bp.
destruct Pmovss_mf_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovss_mf_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 243%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 17%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovsd_fm*)
idtac "Decode Consistency: Pmovsd_fm 123/127".
try clear Bp.
destruct Pmovsd_fm_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovsd_fm_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 242%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 16%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovsd_mf*)
idtac "Decode Consistency: Pmovsd_mf 124/127".
try clear Bp.
destruct Pmovsd_mf_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovsd_mf_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 242%Z.
solve_try_skip_n_decode EQ1.
destruct_const_byte_rewrite 15%Z.
solve_try_skip_n_decode EQ0.
destruct_const_byte_rewrite 17%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ3;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ2.
solve_kls_decode EQ3 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ4.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovl_rm*)
idtac "Decode Consistency: Pmovl_rm 125/127".
try clear Bp.
destruct Pmovl_rm_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovl_rm_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 139%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ0;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ1.
solve_kls_decode EQ0 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ2.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovl_mr*)
idtac "Decode Consistency: Pmovl_mr 126/127".
try clear Bp.
destruct Pmovl_mr_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovl_mr_bp_true in Bp.
destruct_conjunction Bp.
solve_try_skip_n_decode EQ.
destruct_const_byte_rewrite 137%Z.
destruct l as [|ii l];cbn [app] in *.
apply decode_AddrE_len in EQ0;simpl in Decode_Len;omega.
destr_byte ii.
solve_try_get_n_decode EQ1.
solve_kls_decode EQ0 Decode_Len decode_AddrE_consistency decode_AddrE.
repeat solve_zero_len_list.
solve_try_skip_n_decode EQ2.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

(*prove Pmovl_ri*)
idtac "Decode Consistency: Pmovl_ri 127/127".
try clear Bp.
destruct Pmovl_ri_bp eqn:Bp in Dec.
monadInv_decode Dec.
simpl.
autounfold with bitfields.
repeat destruct_const_byte_rewrite 0%Z.
cbn [proj1_sig].
destruct l as [|ii l];cbn [app] in *;
simpl in Decode_Len;try injection Decode_Len as Decode_Len.
congruence.
destr_byte ii.

apply Pmovl_ri_bp_true in Bp.
destruct_conjunction Bp.
solve_try_get_n_decode EQ.
solve_try_skip_n_decode EQ1.
solve_try_first_n_decode EQ0 Decode_Len.
rewrite bytes_to_bits_to_bytes;cbn [bind].
solve_try_skip_n_decode EQ2.
repeat solve_builtin_eq_dec_decode.
repeat rewrite bytes_to_bits_opt_correct by auto;unfold char_to_bool;simpl.
repeat eexists;simpl;auto.

congruence.


Qed.


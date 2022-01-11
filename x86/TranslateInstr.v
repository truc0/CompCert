Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Globalenvs.
Require Import UserAsm RelocProgram.
Require Import Hex compcert.encode.Bits Memdata Encode SeqTable.
Require Import Reloctablesgen.
Require Import SymbolString.
(* Import Hex compcert.encode.Bits.Bits. *)
Require Import Coq.Logic.Eqdep_dec.
Require Import RelocBingen RelocBinDecode.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope nat_scope.

Definition assertLength {A} (l:list A) n: {length l = n} +
                                          {length l <> n}.
Proof.
  decide equality.
Defined.

Definition builtIn (n:nat): Type := {d:list bool| length d = n}.

Lemma builtin_inj: forall {n} (a b:builtIn n),
    proj1_sig a = proj1_sig b -> a = b.
Proof.
  intros n a b H.
  induction a, b.
  simpl in H.
  subst x0.
  f_equal.
  apply UIP_dec.
  apply Nat.eq_dec.
Qed.

Definition u2 := builtIn 2.

Definition u3 := builtIn 3.

Definition u4 := builtIn 4.

Definition u8 := builtIn 8.

Definition u16 := builtIn 16.

Definition u32 := builtIn 32.

Definition nat_to_bits8_opt n : bits :=
  [( n/128 mod 2 =? 1);
  ( n/64 mod 2 =? 1);
  ( n/32 mod 2 =? 1);
  ( n/16 mod 2 =? 1);
  ( n/8 mod 2 =? 1);
  ( n/4 mod 2 =? 1);
  ( n/2 mod 2 =? 1);
  ( n mod 2 =? 1)].

Fixpoint bytes_to_bits_opt (lb:list byte) : bits :=
  match lb with
  | [] => []
  | b::lb' =>(nat_to_bits8_opt (Z.to_nat (Byte.unsigned b))) ++
                                                           (bytes_to_bits_opt lb')
  end.
Program Definition zero32 : u32 :=
  bytes_to_bits_opt (bytes_of_int 4 0).

Program Definition encode_ireg_u3 (r:ireg) : res u3 :=
  do b <- encode_ireg r;
  if assertLength b 3 then    
    OK (exist _ b _)
  else Error (msg "impossible").

Program Definition encode_scale_u2 (ss: Z) :res u2 :=
  do s <- encode_scale ss;
  if assertLength s 2 then    
    OK (exist _ s _)
  else Error (msg "impossible").

Program Definition encode_ofs_u32 (ofs :Z) :res u32 :=
  let ofs32 := bytes_to_bits_opt (bytes_of_int 4 ofs) in
  if assertLength ofs32 32 then
    OK (exist _ ofs32 _)
  else Error (msg "impossible").


Inductive AddrE: Type :=
| AddrE12(uvar3_0:u3)
| AddrE11(uvar32_0:u32)
| AddrE10(uvar2_0:u2)(uvar3_1:u3)(uvar3_2:u3)
| AddrE9(uvar2_0:u2)(uvar3_1:u3)(uvar32_2:u32)
| AddrE8(uvar3_0:u3)
| AddrE7(uvar32_0:u32)
| AddrE6(uvar3_0:u3)(uvar32_1:u32)
| AddrE5(uvar2_0:u2)(uvar3_1:u3)(uvar3_2:u3)(uvar32_3:u32)
| AddrE4(uvar3_0:u3)(uvar32_1:u32)
| AddrE0(uvar3_0:u3).

Inductive AddrM: Type :=
| AddrM11(uvar3_0:u3)
| AddrM10(uvar32_0:u32)
| AddrM9(uvar2_0:u2)(uvar3_1:u3)(uvar3_2:u3)
| AddrM8(uvar2_0:u2)(uvar3_1:u3)(uvar32_2:u32)
| AddrM7(uvar3_0:u3)
| AddrM6(uvar32_0:u32)
| AddrM5(uvar3_0:u3)(uvar32_1:u32)
| AddrM4(uvar2_0:u2)(uvar3_1:u3)(uvar3_2:u3)(uvar32_3:u32)
| AddrM3(uvar3_0:u3)(uvar32_1:u32).

Inductive Instruction: Type :=
| Psubl_ri(uvar3_0:u3)(uvar32_1:u32)
| Pbsqrtsd(uvar3_0:u3)(uvar3_1:u3)
| Psbbl_rr(uvar3_0:u3)(uvar3_1:u3)
| Prep_movsl
| Pmovsq_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovsq_mr(AddrE:AddrE)(uvar3_0:u3)
| Pminsd(uvar3_0:u3)(uvar3_1:u3)
| Pmaxsd(uvar3_0:u3)(uvar3_1:u3)
| Pbswap32(uvar3_0:u3)
| Pbsrl(uvar3_0:u3)(uvar3_1:u3)
| Pbsfl(uvar3_0:u3)(uvar3_1:u3)
| ADD_Ev_Gv(AddrE:AddrE)(uvar3_0:u3)
| ADC_Ev_Gv(AddrE:AddrE)(uvar3_0:u3)
| ADCI_Ev_Ib(AddrE:AddrE)(uvar8_1:u8)
| Pjcc_rel(uvar4_0:u4)(uvar32_1:u32)
| Pret_Iw(uvar16_0:u16)
| Pret
| nCALL_Ev(AddrE:AddrE)
| Pcall_ofs(uvar32_0:u32)
| Pnop
| Pjmp_m(AddrE:AddrE)
| Pjmp_l_rel(uvar32_0:u32)
| Pandps_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pxorps_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pcomisd_ff(uvar3_0:u3)(uvar3_1:u3)
| Pdivsd_ff(uvar3_0:u3)(uvar3_1:u3)
| Pmuld_ff(uvar3_0:u3)(uvar3_1:u3)
| Psubd_ff(uvar3_0:u3)(uvar3_1:u3)
| Paddd_ff(uvar3_0:u3)(uvar3_1:u3)
| Psetcc(uvar4_0:u4)(uvar3_1:u3)
| Pcmov(uvar4_0:u4)(uvar3_1:u3)(uvar3_2:u3)
| Ptestl_rr(uvar3_0:u3)(uvar3_1:u3)
| Ptestl_ri(uvar3_0:u3)(uvar32_1:u32)
| CMPI_Ev_Iz(AddrE:AddrE)(uvar32_1:u32)
| CMP_Ev_Gv(AddrE:AddrE)(uvar3_0:u3)
| Prorl_ri(AddrE:AddrE)(uvar8_1:u8)
| Prolw_ri(AddrE:AddrE)(uvar8_1:u8)
| Pshld_ri(uvar3_0:u3)(uvar3_1:u3)(uvar8_2:u8)
| Psarl_rcl(uvar3_0:u3)
| Psarl_EvIb(AddrE:AddrE)(uvar8_1:u8)
| Pshrl_rcl(uvar3_0:u3)
| Pshrl_EvIb(AddrE:AddrE)(uvar8_1:u8)
| Psall_rcl(uvar3_0:u3)
| Psall_EvIb(AddrE:AddrE)(uvar8_1:u8)
| Pnotl(uvar3_0:u3)
| Pxorl_rr(uvar3_0:u3)(uvar3_1:u3)
| Pxorl_EvIz(AddrE:AddrE)(uvar32_1:u32)
| Porl_rr(uvar3_0:u3)(uvar3_1:u3)
| Porl_EvIz(AddrE:AddrE)(uvar32_1:u32)
| ANDI_Ev_Iz(AddrE:AddrE)(uvar32_1:u32)
| AND_Ev_Gv(AddrE:AddrE)(uvar3_0:u3)
| IDIV_Ev(AddrE:AddrE)
| DIV_Ev(AddrE:AddrE)
| CDQ
| Pmull_r(uvar3_0:u3)
| IMUL_Gv_Ev_Iz(AddrE:AddrE)(uvar3_0:u3)(uvar32_2:u32)
| Pimull_rr(uvar3_0:u3)(uvar3_1:u3)
| Psubl_rr(uvar3_0:u3)(uvar3_1:u3)
| ADDI_Ev_Iz(AddrE:AddrE)(uvar32_1:u32)
| Pnegl(uvar3_0:u3)
| LEA_Gv_M(AddrM:AddrM)(uvar3_0:u3)
| Pcvttss2si_rf(uvar3_0:u3)(uvar3_1:u3)
| Pcvttsi2sd_fr(uvar3_0:u3)(uvar3_1:u3)
| Pcvtsi2ss_fr(uvar3_0:u3)(uvar3_1:u3)
| Pcvttsd2si_rf(uvar3_0:u3)(uvar3_1:u3)
| Pcvtss2sd_ff(uvar3_0:u3)(uvar3_1:u3)
| Pcvtsd2ss_ff(uvar3_0:u3)(uvar3_1:u3)
| Pmovsw_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pmovzw_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pmovsb_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pmovzb_GvEv(AddrE:AddrE)(uvar3_0:u3)
| Pmovw_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovw_mr(AddrE:AddrE)(uvar3_0:u3)
| Pmovb_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovb_mr(AddrE:AddrE)(uvar3_0:u3)
| Pflds_m(AddrE:AddrE)
| Pfstps_m(AddrE:AddrE)
| Pfstpl_m(AddrE:AddrE)
| Pfldl_m(AddrE:AddrE)
| Pmovss_fEv(AddrE:AddrE)(uvar3_0:u3)
| Pmovss_Evf(AddrE:AddrE)(uvar3_0:u3)
| Pmovsd_fEv(AddrE:AddrE)(uvar3_0:u3)
| Pmovsd_Evf(AddrE:AddrE)(uvar3_0:u3)
| Pmovl_rm(AddrE:AddrE)(uvar3_0:u3)
| Pmovl_mr(AddrE:AddrE)(uvar3_0:u3)
| Pmovl_ri(uvar3_0:u3)(uvar32_1:u32).


Section WITH_RELOC_OFS_MAP.

Variable rtbl_ofs_map: reloc_ofs_map_type.

Definition translate_Addrmode_AddrE (sofs: Z) (i:instruction) (addr:addrmode): res AddrE :=
  match addr with
  | Addrmode obase oindex disp  =>
    match disp with
    | inr (id, ofs) =>
      match id with
      | xH =>
        do iofs <- instr_reloc_offset i;
        do addend <- get_instr_reloc_addend' rtbl_ofs_map (iofs + sofs);
        if Z.eqb (Ptrofs.unsigned ofs) addend then
          match obase,oindex with
          | None,None =>                    
            OK (AddrE11 zero32)
          | Some base,None =>
            do r <- encode_ireg_u3 base;
              OK (AddrE6 r zero32)
          | None,Some (idx,ss) =>
            do index <- encode_ireg_u3 idx;          
            do scale <- encode_scale_u2 ss;                    
                OK (AddrE9 scale index zero32)
          | Some base,Some (idx,ss) =>
            do scale <- encode_scale_u2 ss;
            do index <- encode_ireg_u3 idx;
            do breg <- encode_ireg_u3 base;          
            if ireg_eq idx RSP then
              Error (msg "index can not be RSP")
                    (* OK (AddrE4 breg zero32)            *)      
            else                                                   
              OK (AddrE5 scale index breg zero32)
          end
        else Error (msg "addend is not equal to ofs")
      | _ => Error(msg "id must be 1")
      end
    | inl ofs =>
      do iofs <- instr_reloc_offset i;
      match ZTree.get (iofs + sofs)%Z rtbl_ofs_map with
      | None =>
        do ofs32 <- encode_ofs_u32 ofs;        
        match obase,oindex with
        | None,None =>            
          OK (AddrE11 ofs32)
        | Some base,None =>
          do r <- encode_ireg_u3 base;          
          OK (AddrE6 r ofs32)             
        | None,Some (idx,ss) =>
          do r <- encode_ireg_u3 idx;
          do scale <- encode_scale_u2 ss;
          OK (AddrE9 scale r ofs32)                          
        | Some base,Some (idx,ss) =>
          do scale <- encode_scale_u2 ss;
          do index <- encode_ireg_u3 idx;
          do breg <- encode_ireg_u3 base;            
          if ireg_eq idx RSP then
            Error (msg "index can not be RSP")
                  (* OK (AddrE4 breg_sig ofs32) *)
          else
            OK (AddrE5 scale index breg ofs32)
        end          
      | _ => Error (msg "impossible")
      end
    end
  end.

Definition decode_ireg (bs:bits) : res ireg :=
  let n := bits_to_Z bs in
  if Z.eqb n 0 then OK(RAX)
  else Error(msg "reg not found")
.

Definition translate_AddrE_Addrmode (sofs: Z) (i:instruction) (addr:AddrE) : res addrmode :=
  (* need to relocate? *)
  do iofs <- instr_reloc_offset i;
  match ZTree.get (iofs + sofs)%Z rtbl_ofs_map with
  | None =>
    match addr with
    | AddrE11 disp =>
      OK (Addrmode None None (inl (bits_to_Z (proj1_sig disp))))
    | AddrE9 ss idx disp =>
      do index <- decode_ireg (proj1_sig idx);      
      OK (Addrmode None (Some (index,(bits_to_Z (proj1_sig ss)))) (inl (bits_to_Z (proj1_sig disp))) )
    | AddrE6 base disp =>
      do b <- decode_ireg (proj1_sig base);
      OK (Addrmode (Some b) None (inl (bits_to_Z (proj1_sig disp))) )
    (* | AddrE4 base disp => *)
    (*   do b <- decode_ireg (proj1_sig base); *)
    (*   OK (Addr) *)
    | AddrE5 ss idx base disp =>
      do index <- decode_ireg (proj1_sig idx);
      do b <- decode_ireg (proj1_sig base);
      if ireg_eq index RSP then
        Error (msg "index can not be RSP")
      else OK (Addrmode (Some b) (Some (index,(bits_to_Z (proj1_sig ss)))) (inl (bits_to_Z (proj1_sig disp))) )
    | _ => Error (msg "unsupported or impossible")
    end
  | Some _ =>
    do addend <- get_instr_reloc_addend' rtbl_ofs_map (iofs + sofs);
    match addr with
    | AddrE11 _ =>
      OK (Addrmode None None (inr (xH,Ptrofs.repr addend)))
    | AddrE9 ss idx disp =>
      do index <- decode_ireg (proj1_sig idx);      
      OK (Addrmode None (Some (index,(bits_to_Z (proj1_sig ss)))) (inr (xH,Ptrofs.repr addend)) )
    | AddrE6 base disp =>
      do b <- decode_ireg (proj1_sig base);
      OK (Addrmode (Some b) None (inr (xH,Ptrofs.repr addend)))
    (* | AddrE4 base disp => *)
    (*   do b <- decode_ireg (proj1_sig base); *)
    (*   OK (Addr) *)
    | AddrE5 ss idx base disp =>
      do index <- decode_ireg (proj1_sig idx);
      do b <- decode_ireg (proj1_sig base);
      if ireg_eq index RSP then
        Error (msg "index can not be RSP")
      else OK (Addrmode (Some b) (Some (index,(bits_to_Z (proj1_sig ss)))) (inr (xH,Ptrofs.repr addend)) )
    | _ => Error (msg "unsupported or impossible")
    end
  end.


Lemma translate_consistency1 : forall ofs i addr addrE,
    translate_Addrmode_AddrE ofs i addr = OK addrE ->
    translate_AddrE_Addrmode ofs i addrE = OK addr.
  intros. destruct addr.
  unfold translate_Addrmode_AddrE in H.
  unfold translate_AddrE_Addrmode.
  destruct base;destruct ofs0;try destruct p;destruct const.  
  - monadInv H.
    rewrite EQ.
    cbn [bind].    
    destruct (ZTree.get (x + ofs)%Z rtbl_ofs_map);try congruence.
    monadInv EQ0.
    destruct (ireg_eq i1 RSP);try congruence.
    monadInv EQ5.
Admitted.

Definition translate_instr (ofs: Z) (i:instruction) :Instruction :=
  match i with
  | Pmov_rr rd r1 =>
    do rdbits <- encode_ireg_u3 rd;
    do r1bits <- encode_ireg_u3 r1;
    Pmovl_rr rdbits r1bits
  | UserAsm.Pmovl_rm rd addr =>
    do rdbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE ofs i addr;
    Pmovl_rm a rdbits
  | UserAsm.Pmovl_ri rd imm =>
    do rdbits <- encode_ireg_u3 rd;
    do imm32 <- encode_ofs_u32 imm;
    Pmovl_ri rdbits imm32
  | UserAsm.Pmovl_mr addr r =>
    do rbits <- encode_ireg_u3 r;
    do a <- translate_Addrmode_AddrE ofs i addr;
    Pmovl_mr a rbits
  | UserAsm.Pmovsd_ff rd r1 =>
    do rdbits <- encode_ireg_u3 rd;
    do r1bits <- encode_ireg_u3 r1;
    Pmovsd_ff rdbits r1bits
  | Pmovsd_fm r addr =>
    do rbits <- encode_ireg_u3 r;
    do a <- translate_Addrmode_AddrE ofs i addr;
    Pmovsd_fEv a rbits
  | Pmovsd_mf addr r =>
    do rbits <- encode_ireg_u3 r;
    do a <- translate_Addrmode_AddrE ofs i addr;
    Pmovsd_Evf a rbits
  | Pmovss_fm r addr =>
    do rbits <- encode_ireg_u3 r;
    do a <- translate_Addrmode_AddrE ofs i addr;
    Pmovss_fEv a rdbits
  | Pmovss_mf addr r =>
    do rbits <- encode_ireg_u3 r;
    do a <- translate_Addrmode_AddrE ofs i addr;
    Pmovss_Evf a rdbits
  | UserAsm.Pfldl_m addr =>
    do a <- translate_Addrmode_AddrE ofs i addr;
    Pfldl_m a
  | Pfstpl_m addr =>
    do a <- translate_Addrmode_AddrE ofs i addr;
    Pfstpl_m a
  | 
    
       

      
    

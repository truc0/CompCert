Require Import Coqlib Integers AST Memdata Maps (*StackADT*).
Require Import Asm UserAsm (*Asmgen*) UserRealAsm.
Require Import Errors.
Require Import Memtype.
Import ListNotations.

Local Open Scope error_monad_scope.
Close Scope nat_scope.

Definition transf_ireg (r: Asm.ireg): UserAsm.ireg :=
  match r with
  | Asm.RAX => RAX | Asm.RBX => RBX | Asm.RCX => RCX | Asm.RDX => RDX
  | Asm.RSI => RSI | Asm.RDI => RDI | Asm.RBP => RBP | Asm.RSP => RSP
  | Asm.R8 => R8   | Asm.R9 => R9   | Asm.R10 => R10 | Asm.R11 => R11
  | Asm.R12 => R12 | Asm.R13 => R13 | Asm.R14 => R14 | Asm.R15 => R15
  end.

Definition transf_freg (r: Asm.freg): UserAsm.freg :=
  match r with
  | Asm.XMM0 => XMM0   | Asm.XMM1 => XMM1   | Asm.XMM2 => XMM2   | Asm.XMM3 => XMM3
  | Asm.XMM4 => XMM4   | Asm.XMM5 => XMM5   | Asm.XMM6 => XMM6   | Asm.XMM7 => XMM7
  | Asm.XMM8 => XMM8   | Asm.XMM9 => XMM9   | Asm.XMM10 => XMM10 | Asm.XMM11 => XMM11
  | Asm.XMM12 => XMM12 | Asm.XMM13 => XMM13 | Asm.XMM14 => XMM14 | Asm.XMM15 => XMM15
  end.

Definition transf_crbit (c: Asm.crbit): UserAsm.crbit :=
  match c with
  | Asm.ZF => ZF | Asm.CF => CF | Asm.PF => PF | Asm.SF => SF | Asm.OF => OF
  end.

Definition transf_preg (p: Asm.preg): UserAsm.preg :=
  match p with
  | Asm.PC => PC
  | Asm.IR i => IR (transf_ireg i)
  | Asm.FR f => FR (transf_freg f)
  | Asm.ST0 => ST0
  | Asm.CR c => CR (transf_crbit c)
  | Asm.RA => RA
  end.

Definition transf_ofs (ofs: Asm.ireg * Z): ireg * Z :=
  match ofs with
  | (i, x) => (transf_ireg i, x)
  end.

Definition transf_addrmode (a: Asm.addrmode): UserAsm.addrmode :=
  match a with
  | Asm.Addrmode base ofs const => Addrmode (option_map transf_ireg base) (option_map transf_ofs ofs) (const)
  end.

Definition transf_testcond (c: Asm.testcond) : UserAsm.testcond :=
  match c with
  | Asm.Cond_e => Cond_e | Asm.Cond_ne => Cond_ne
  | Asm.Cond_b => Cond_b | Asm.Cond_be => Cond_be | Asm.Cond_ae => Cond_ae | Asm.Cond_a => Cond_a
  | Asm.Cond_l => Cond_l | Asm.Cond_le => Cond_le | Asm.Cond_ge => Cond_ge | Asm.Cond_g => Cond_g
  | Asm.Cond_p => Cond_p | Asm.Cond_np => Cond_np
  end.

Definition transf_instr (i: Asm.instruction): list UserAsm.instruction :=
  match i with
  (** Moves *)
  | Asm.Pmov_rr rd r1 => [ Pmov_rr (transf_ireg rd) (transf_ireg r1) ]
  | Asm.Pmovl_ri rd n => [ Pmovl_ri (transf_ireg rd) (n) ]
  | Asm.Pmovq_ri rd n => [ Pmovq_ri (transf_ireg rd) (n) ]
  | Asm.Pmov_rs rd id => [ Pmov_rs (transf_ireg rd) (id) ]
  | Asm.Pmovl_rm rd a => [ Pmovl_rm (transf_ireg rd) (transf_addrmode a) ]
  | Asm.Pmovq_rm rd a => [ Pmovq_rm (transf_ireg rd) (transf_addrmode a) ]
  | Asm.Pmovl_mr a rs => [ Pmovl_mr (transf_addrmode a) (transf_ireg rs) ]
  | Asm.Pmovq_mr a rs => [ Pmovq_mr (transf_addrmode a) (transf_ireg rs) ]
  (* | Pmovsd_ff (rd: freg) (r1: freg) *)
  (* | Pmovsd_fi (rd: freg) (n: float) *)
  (* | Pmovsd_fm (rd: freg) (a: addrmode) *)
  (* | Pmovsd_mf (a: addrmode) (r1: freg) *)
  (* | Pmovss_fi (rd: freg) (n: float32) *)
  (* | Pmovss_fm (rd: freg) (a: addrmode) *)
  (* | Pmovss_mf (a: addrmode) (r1: freg) *)
  (* | Pfldl_m (a: addrmode) *)
  (* | Pfstpl_m (a: addrmode) *)
  (* | Pflds_m (a: addrmode) *)
  (* | Pfstps_m (a: addrmode) *)

  (** Moves with conversion *)
  (* | Pmovb_mr (a: addrmode) (rs: ireg) *)
  (* | Pmovw_mr (a: addrmode) (rs: ireg) *)
  (* | Pmovzb_rr (rd: ireg) (rs: ireg) *)
  (* | Pmovzb_rm (rd: ireg) (a: addrmode) *)
  (* | Pmovsb_rr (rd: ireg) (rs: ireg) *)
  (* | Pmovsb_rm (rd: ireg) (a: addrmode) *)
  (* | Pmovzw_rr (rd: ireg) (rs: ireg) *)
  (* | Pmovzw_rm (rd: ireg) (a: addrmode) *)
  (* | Pmovsw_rr (rd: ireg) (rs: ireg) *)
  (* | Pmovsw_rm (rd: ireg) (a: addrmode) *)
  (* | Pmovzl_rr (rd: ireg) (rs: ireg) *)
  (* | Pmovsl_rr (rd: ireg) (rs: ireg) *)
  (* | Pmovls_rr (rd: ireg) *)
  (* | Pcvtsd2ss_ff (rd: freg) (r1: freg) *)
  (* | Pcvtss2sd_ff (rd: freg) (r1: freg) *)
  (* | Pcvttsd2si_rf (rd: ireg) (r1: freg) *)
  (* | Pcvtsi2sd_fr (rd: freg) (r1: ireg) *)
  (* | Pcvttss2si_rf (rd: ireg) (r1: freg) *)
  (* | Pcvtsi2ss_fr (rd: freg) (r1: ireg) *)
  (* | Pcvttsd2sl_rf (rd: ireg) (r1: freg) *)
  (* | Pcvtsl2sd_fr (rd: freg) (r1: ireg) *)
  (* | Pcvttss2sl_rf (rd: ireg) (r1: freg) *)
  (* | Pcvtsl2ss_fr (rd: freg) (r1: ireg) *)

  (** Integer arithmetic *)
  | Asm.Pleal rd a => [ Pleal (transf_ireg rd) (transf_addrmode a) ]
  | Asm.Pleaq rd a => [ Pleaq (transf_ireg rd) (transf_addrmode a) ]
  (* | Pnegl (rd: ireg) *)
  (* | Pnegq (rd: ireg) *)
  | Asm.Paddl_ri rd n => [ Paddl_ri (transf_ireg rd: ireg) (n: int) ]
  | Asm.Paddq_ri rd n => [ Paddq_ri (transf_ireg rd: ireg) (n: int64) ]
  | Asm.Psubl_rr rd r1 => [ Psubl_rr (transf_ireg rd: ireg) (transf_ireg r1: ireg) ]
  | Asm.Psubq_rr rd r1 => [ Psubq_rr (transf_ireg rd: ireg) (transf_ireg r1: ireg) ]
  (* | Pimull_rr (rd: ireg) (r1: ireg) *)
  (* | Pimulq_rr (rd: ireg) (r1: ireg) *)
  (* | Pimull_ri (rd: ireg) (n: int) *)
  (* | Pimulq_ri (rd: ireg) (n: int64) *)
  (* | Pimull_r (r1: ireg) *)
  (* | Pimulq_r (r1: ireg) *)
  (* | Pmull_r (r1: ireg) *)
  (* | Pmulq_r (r1: ireg) *)
  (* | Pcltd *)
  (* | Pcqto *)
  (* | Pdivl (r1: ireg) *)
  (* | Pdivq (r1: ireg) *)
  (* | Pidivl (r1: ireg) *)
  (* | Pidivq (r1: ireg) *)
  (* | Pandl_rr (rd: ireg) (r1: ireg) *)
  (* | Pandq_rr (rd: ireg) (r1: ireg) *)
  (* | Pandl_ri (rd: ireg) (n: int) *)
  (* | Pandq_ri (rd: ireg) (n: int64) *)
  (* | Porl_rr (rd: ireg) (r1: ireg) *)
  (* | Porq_rr (rd: ireg) (r1: ireg) *)
  (* | Porl_ri (rd: ireg) (n: int) *)
  (* | Porq_ri (rd: ireg) (n: int64) *)
  | Asm.Pxorl_r rd => [ Pxorl_r (transf_ireg rd: ireg) ]                  (**r [xor] with self = set to zero *)
  | Asm.Pxorq_r rd => [ Pxorq_r (transf_ireg rd: ireg) ]
  (* | Pxorl_rr (rd: ireg) (r1: ireg) *)
  (* | Pxorq_rr (rd: ireg) (r1: ireg) *)
  (* | Pxorl_ri (rd: ireg) (n: int) *)
  (* | Pxorq_ri (rd: ireg) (n: int64) *)
  (* | Pnotl (rd: ireg) *)
  (* | Pnotq (rd: ireg) *)
  (* | Psall_rcl (rd: ireg) *)
  (* | Psalq_rcl (rd: ireg) *)
  (* | Psall_ri (rd: ireg) (n: int) *)
  (* | Psalq_ri (rd: ireg) (n: int) *)
  (* | Pshrl_rcl (rd: ireg) *)
  (* | Pshrq_rcl (rd: ireg) *)
  (* | Pshrl_ri (rd: ireg) (n: int) *)
  (* | Pshrq_ri (rd: ireg) (n: int) *)
  (* | Psarl_rcl (rd: ireg) *)
  (* | Psarq_rcl (rd: ireg) *)
  (* | Psarl_ri (rd: ireg) (n: int) *)
  (* | Psarq_ri (rd: ireg) (n: int) *)
  (* | Pshld_ri (rd: ireg) (r1: ireg) (n: int) *)
  (* | Prorl_ri (rd: ireg) (n: int) *)
  (* | Prorq_ri (rd: ireg) (n: int) *)
  (* | Pcmpl_rr (r1 r2: ireg) *)
  (* | Pcmpq_rr (r1 r2: ireg) *)
  | Asm.Pcmpl_ri r1 n => [ Pcmpl_ri (transf_ireg r1) (n) ]
  | Asm.Pcmpq_ri r1 n => [ Pcmpq_ri (transf_ireg r1) (n) ]
  (* | Ptestl_rr (r1 r2: ireg) *)
  (* | Ptestq_rr (r1 r2: ireg) *)
  (* | Ptestl_ri (r1: ireg) (n: int) *)
  (* | Ptestq_ri (r1: ireg) (n: int64) *)
  (* | Pcmov (c: testcond) (rd: ireg) (r1: ireg) *)
  (* | Psetcc (c: testcond) (rd: ireg) *)

  (** Floating-point arithmetic *)
  (* | Paddd_ff (rd: freg) (r1: freg) *)
  (* | Psubd_ff (rd: freg) (r1: freg) *)
  (* | Pmuld_ff (rd: freg) (r1: freg) *)
  (* | Pdivd_ff (rd: freg) (r1: freg) *)
  (* | Pnegd (rd: freg) *)
  (* | Pabsd (rd: freg) *)
  (* | Pcomisd_ff (r1 r2: freg) *)
  (* | Pxorpd_f (rd: freg)	              (**r [xor] with self = set to zero *) *)
  (* | Padds_ff (rd: freg) (r1: freg) *)
  (* | Psubs_ff (rd: freg) (r1: freg) *)
  (* | Pmuls_ff (rd: freg) (r1: freg) *)
  (* | Pdivs_ff (rd: freg) (r1: freg) *)
  (* | Pnegs (rd: freg) *)
  (* | Pabss (rd: freg) *)
  (* | Pcomiss_ff (r1 r2: freg) *)
  (* | Pxorps_f (rd: freg)	              (**r [xor] with self = set to zero *) *)

  (** Branches and calls *)
  | Asm.Pjmp_l l => [ Pjmp_l (l: label) ]
  (* | Pjmp_s (symb: ident) (sg: signature) *)
  (* | Pjmp_r (r: ireg) (sg: signature) *)
  | Asm.Pjcc c l => [ Pjcc (transf_testcond c)(l) ]
  (* | Pjcc2 (c1 c2: testcond)(l: label)   (**r pseudo *) *)
  (* | Pjmptbl (r: ireg) (tbl: list label) (**r pseudo *) *)
  | Asm.Pcall_s symb sg => [ Pcall (inr symb) (sg: signature) ]
  (* | Pcall_r (r: ireg) (sg: signature) *)
  | Asm.Pret => [ Pret ]

  (** Saving and restoring registers *)
  | Asm.Pmov_rm_a rd a => [ Pmov_rm_a (transf_ireg rd: ireg) (transf_addrmode a: addrmode) ]  (**r like [Pmov_rm], using [Many64] chunk *)
  | Asm.Pmov_mr_a a rs => [ Pmov_mr_a (transf_addrmode a: addrmode) (transf_ireg rs: ireg) ]  (**r like [Pmov_mr], using [Many64] chunk *)
  (* | Pmovsd_fm_a (rd: freg) (a: addrmode) (**r like [Pmovsd_fm], using [Many64] chunk *) *)
  (* | Pmovsd_mf_a (a: addrmode) (r1: freg) (**r like [Pmovsd_mf], using [Many64] chunk *) *)

  (** Pseudo-instructions *)
  | Asm.Plabel l => [ Plabel(l: label) ]
  (* TODO *)
  | Asm.Pallocframe sz ofs_ra ofs_link => [ Pallocframe(sz: Z)(ofs_ra: ptrofs) ]
  | Asm.Pfreeframe sz ofs_ra ofs_link => [ Pfreeframe(sz: Z)(ofs_ra: ptrofs) ]
  (* | Pbuiltin(ef: external_function)(args: list (builtin_arg preg))(res: builtin_res preg) *)

  (** Instructions not generated by [Asmgen] -- TO CHECK *)
  (* | Padcl_ri (rd: ireg) (n: int) *)
  (* | Padcl_rr (rd: ireg) (r2: ireg) *)
  (* | Paddl_mi (a: addrmode) (n: int) *)
  (* | Paddl_rr (rd: ireg) (r2: ireg) *)
  (* | Pbsfl (rd: ireg) (r1: ireg) *)
  (* | Pbsfq (rd: ireg) (r1: ireg) *)
  (* | Pbsrl (rd: ireg) (r1: ireg) *)
  (* | Pbsrq (rd: ireg) (r1: ireg) *)
  (* | Pbswap64 (rd: ireg) *)
  (* | Pbswap32 (rd: ireg) *)
  (* | Pbswap16 (rd: ireg) *)
  | Asm.Pcfi_adjust n => [ Pcfi_adjust (n: int) ]
  (* | Pfmadd132 (rd: freg) (r2: freg) (r3: freg) *)
  (* | Pfmadd213 (rd: freg) (r2: freg) (r3: freg) *)
  (* | Pfmadd231 (rd: freg) (r2: freg) (r3: freg) *)
  (* | Pfmsub132 (rd: freg) (r2: freg) (r3: freg) *)
  (* | Pfmsub213 (rd: freg) (r2: freg) (r3: freg) *)
  (* | Pfmsub231 (rd: freg) (r2: freg) (r3: freg) *)
  (* | Pfnmadd132 (rd: freg) (r2: freg) (r3: freg) *)
  (* | Pfnmadd213 (rd: freg) (r2: freg) (r3: freg) *)
  (* | Pfnmadd231 (rd: freg) (r2: freg) (r3: freg) *)
  (* | Pfnmsub132 (rd: freg) (r2: freg) (r3: freg) *)
  (* | Pfnmsub213 (rd: freg) (r2: freg) (r3: freg) *)
  (* | Pfnmsub231 (rd: freg) (r2: freg) (r3: freg) *)
  (* | Pmaxsd (rd: freg) (r2: freg) *)
  (* | Pminsd (rd: freg) (r2: freg) *)
  (* | Pmovb_rm (rd: ireg) (a: addrmode) *)
  (* | Pmovq_rf (rd: ireg) (r1: freg) *)
  (* | Pmovsq_mr  (a: addrmode) (rs: freg) *)
  (* | Pmovsq_rm (rd: freg) (a: addrmode) *)
  (* | Pmovsb *)
  (* | Pmovsw *)
  (* | Pmovw_rm (rd: ireg) (ad: addrmode) *)
  (* | Pnop *)
  (* | Prep_movsl *)
  (* | Psbbl_rr (rd: ireg) (r2: ireg) *)
  (* | Psqrtsd (rd: freg) (r1: freg) *)
  (* | Psubl_ri (rd: ireg) (n: int) *)
  (* | Psubq_ri (rd: ireg) (n: int64). *)
  (* | _ => [ Pnop ] *)
  | _ => [ Pmovsb ]
  end.

Definition transf_code (c: Asm.code) : code :=
  concat (map transf_instr c).

Definition transf_function (f: Asm.function) : function :=
  {|
    fn_sig := Asm.fn_sig f;
    fn_code := transf_code (Asm.fn_code f);
    fn_stacksize := Asm.fn_stacksize f;
  |}.

Definition transf_fundef := AST.transf_fundef transf_function.

Definition transf_program (p: Asm.program) : UserAsm.program :=
  AST.transform_program transf_fundef p.

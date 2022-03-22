Require Import Coqlib Integers Errors.
Require Import Hex lib.Bits Memdata.
Require Import Util Encode.
Require Import EncDecRet.
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

Inductive AddrE12_spec: list bool -> u3 -> Prop :=
|cons_AddrE12:
forall lst uvar3_0
(CONS: exists mod0 reg_op0 rm0,
lst = mod0 ++ reg_op0 ++ rm0
 /\ length mod0 = 2 /\ length reg_op0 = 3 /\ length rm0 = 3 /\ mod0 = b["00"] /\ rm0 <> b["100"] /\ rm0 <> b["101"] /\ rm0 = (proj1_sig uvar3_0)),
AddrE12_spec lst uvar3_0.
Inductive AddrE11_spec: list bool -> u32 -> Prop :=
|cons_AddrE11:
forall lst uvar32_0
(CONS: exists mod0 reg_op0 rm0 imm321,
lst = mod0 ++ reg_op0 ++ rm0 ++ imm321
 /\ length mod0 = 2 /\ length reg_op0 = 3 /\ length rm0 = 3 /\ mod0 = b["00"] /\ rm0 = b["101"] /\ length imm321 = 32 /\ imm321 = (proj1_sig uvar32_0)),
AddrE11_spec lst uvar32_0.
Inductive AddrE10_spec: list bool -> u2 -> u3 -> u3 -> Prop :=
|cons_AddrE10:
forall lst uvar2_0 uvar3_1 uvar3_2
(CONS: exists mod0 reg_op0 rm0 scale1 index1 base1,
lst = mod0 ++ reg_op0 ++ rm0 ++ scale1 ++ index1 ++ base1
 /\ length mod0 = 2 /\ length reg_op0 = 3 /\ length rm0 = 3 /\ mod0 = b["00"] /\ rm0 = b["100"] /\ length scale1 = 2 /\ length index1 = 3 /\ length base1 = 3 /\ base1 <> b["101"] /\ index1 <> b["100"] /\ scale1 = (proj1_sig uvar2_0) /\ index1 = (proj1_sig uvar3_1) /\ base1 = (proj1_sig uvar3_2)),
AddrE10_spec lst uvar2_0 uvar3_1 uvar3_2.
Inductive AddrE9_spec: list bool -> u2 -> u3 -> u32 -> Prop :=
|cons_AddrE9:
forall lst uvar2_0 uvar3_1 uvar32_2
(CONS: exists mod0 reg_op0 rm0 scale1 index1 base1 imm322,
lst = mod0 ++ reg_op0 ++ rm0 ++ scale1 ++ index1 ++ base1 ++ imm322
 /\ length mod0 = 2 /\ length reg_op0 = 3 /\ length rm0 = 3 /\ mod0 = b["00"] /\ rm0 = b["100"] /\ length scale1 = 2 /\ length index1 = 3 /\ length base1 = 3 /\ base1 = b["101"] /\ index1 <> b["100"] /\ scale1 = (proj1_sig uvar2_0) /\ index1 = (proj1_sig uvar3_1) /\ length imm322 = 32 /\ imm322 = (proj1_sig uvar32_2)),
AddrE9_spec lst uvar2_0 uvar3_1 uvar32_2.
Inductive AddrE8_spec: list bool -> u3 -> Prop :=
|cons_AddrE8:
forall lst uvar3_0
(CONS: exists mod0 reg_op0 rm0 scale1 index1 base1,
lst = mod0 ++ reg_op0 ++ rm0 ++ scale1 ++ index1 ++ base1
 /\ length mod0 = 2 /\ length reg_op0 = 3 /\ length rm0 = 3 /\ mod0 = b["00"] /\ rm0 = b["100"] /\ length scale1 = 2 /\ length index1 = 3 /\ length base1 = 3 /\ scale1 = b["00"] /\ index1 = b["100"] /\ base1 <> b["101"] /\ base1 = (proj1_sig uvar3_0)),
AddrE8_spec lst uvar3_0.
Inductive AddrE7_spec: list bool -> u32 -> Prop :=
|cons_AddrE7:
forall lst uvar32_0
(CONS: exists mod0 reg_op0 rm0 scale1 index1 base1 imm322,
lst = mod0 ++ reg_op0 ++ rm0 ++ scale1 ++ index1 ++ base1 ++ imm322
 /\ length mod0 = 2 /\ length reg_op0 = 3 /\ length rm0 = 3 /\ mod0 = b["00"] /\ rm0 = b["100"] /\ length scale1 = 2 /\ length index1 = 3 /\ length base1 = 3 /\ scale1 = b["00"] /\ index1 = b["100"] /\ base1 = b["101"] /\ length imm322 = 32 /\ imm322 = (proj1_sig uvar32_0)),
AddrE7_spec lst uvar32_0.
Inductive AddrE6_spec: list bool -> u3 -> u32 -> Prop :=
|cons_AddrE6:
forall lst uvar3_0 uvar32_1
(CONS: exists mod0 reg_op0 rm0 imm321,
lst = mod0 ++ reg_op0 ++ rm0 ++ imm321
 /\ length mod0 = 2 /\ length reg_op0 = 3 /\ length rm0 = 3 /\ mod0 = b["10"] /\ rm0 <> b["100"] /\ rm0 = (proj1_sig uvar3_0) /\ length imm321 = 32 /\ imm321 = (proj1_sig uvar32_1)),
AddrE6_spec lst uvar3_0 uvar32_1.
Inductive AddrE5_spec: list bool -> u2 -> u3 -> u3 -> u32 -> Prop :=
|cons_AddrE5:
forall lst uvar2_0 uvar3_1 uvar3_2 uvar32_3
(CONS: exists mod0 reg_op0 rm0 scale1 index1 base1 imm322,
lst = mod0 ++ reg_op0 ++ rm0 ++ scale1 ++ index1 ++ base1 ++ imm322
 /\ length mod0 = 2 /\ length reg_op0 = 3 /\ length rm0 = 3 /\ mod0 = b["10"] /\ rm0 = b["100"] /\ length scale1 = 2 /\ length index1 = 3 /\ length base1 = 3 /\ index1 <> b["100"] /\ scale1 = (proj1_sig uvar2_0) /\ index1 = (proj1_sig uvar3_1) /\ base1 = (proj1_sig uvar3_2) /\ length imm322 = 32 /\ imm322 = (proj1_sig uvar32_3)),
AddrE5_spec lst uvar2_0 uvar3_1 uvar3_2 uvar32_3.
Inductive AddrE4_spec: list bool -> u3 -> u32 -> Prop :=
|cons_AddrE4:
forall lst uvar3_0 uvar32_1
(CONS: exists mod0 reg_op0 rm0 scale1 index1 base1 imm322,
lst = mod0 ++ reg_op0 ++ rm0 ++ scale1 ++ index1 ++ base1 ++ imm322
 /\ length mod0 = 2 /\ length reg_op0 = 3 /\ length rm0 = 3 /\ mod0 = b["10"] /\ rm0 = b["100"] /\ length scale1 = 2 /\ length index1 = 3 /\ length base1 = 3 /\ scale1 = b["00"] /\ index1 = b["100"] /\ base1 = (proj1_sig uvar3_0) /\ length imm322 = 32 /\ imm322 = (proj1_sig uvar32_1)),
AddrE4_spec lst uvar3_0 uvar32_1.
Inductive AddrE0_spec: list bool -> u3 -> Prop :=
|cons_AddrE0:
forall lst uvar3_0
(CONS: exists mod0 reg_op0 rm0,
lst = mod0 ++ reg_op0 ++ rm0
 /\ length mod0 = 2 /\ length reg_op0 = 3 /\ length rm0 = 3 /\ mod0 = b["11"] /\ rm0 = (proj1_sig uvar3_0)),
AddrE0_spec lst uvar3_0.
Definition AddrE_spec lst  element : Prop :=
	match element with
| AddrE12 uvar3_0 => AddrE12_spec lst uvar3_0
| AddrE11 uvar32_0 => AddrE11_spec lst uvar32_0
| AddrE10 uvar2_0 uvar3_1 uvar3_2 => AddrE10_spec lst uvar2_0 uvar3_1 uvar3_2
| AddrE9 uvar2_0 uvar3_1 uvar32_2 => AddrE9_spec lst uvar2_0 uvar3_1 uvar32_2
| AddrE8 uvar3_0 => AddrE8_spec lst uvar3_0
| AddrE7 uvar32_0 => AddrE7_spec lst uvar32_0
| AddrE6 uvar3_0 uvar32_1 => AddrE6_spec lst uvar3_0 uvar32_1
| AddrE5 uvar2_0 uvar3_1 uvar3_2 uvar32_3 => AddrE5_spec lst uvar2_0 uvar3_1 uvar3_2 uvar32_3
| AddrE4 uvar3_0 uvar32_1 => AddrE4_spec lst uvar3_0 uvar32_1
| AddrE0 uvar3_0 => AddrE0_spec lst uvar3_0
end.

Inductive Ptestq_EvGv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Ptestq_EvGv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["10000101"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Ptestq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Ptestq_ri_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u32 -> Prop :=
|cons_Ptestq_ri:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2 imm323,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2 ++ imm323
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["11110111"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = b["000"] /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE /\ length imm323 = 32 /\ imm323 = (proj1_sig uvar32_4)),
Ptestq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4.
Inductive Pcmpq_GvEv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Pcmpq_GvEv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["00111011"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pcmpq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Pcmpq_EvGv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Pcmpq_EvGv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["00111001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pcmpq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Pcmpq_ri_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u32 -> Prop :=
|cons_Pcmpq_ri:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2 imm323,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2 ++ imm323
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["10000001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = b["111"] /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE /\ length imm323 = 32 /\ imm323 = (proj1_sig uvar32_4)),
Pcmpq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4.
Inductive Prorq_ri_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u8 -> Prop :=
|cons_Prorq_ri:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar8_4
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2 imm83,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2 ++ imm83
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["11000001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = b["001"] /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE /\ length imm83 = 8 /\ imm83 = (proj1_sig uvar8_4)),
Prorq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar8_4.
Inductive Psarq_ri_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u8 -> Prop :=
|cons_Psarq_ri:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar8_4
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2 imm83,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2 ++ imm83
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["11000001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = b["111"] /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE /\ length imm83 = 8 /\ imm83 = (proj1_sig uvar8_4)),
Psarq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar8_4.
Inductive Psarq_rcl_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> Prop :=
|cons_Psarq_rcl:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["11010011"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = b["111"] /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Psarq_rcl_spec lst AddrE uvar1_0 uvar1_1 uvar1_2.
Inductive Psalq_ri_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u8 -> Prop :=
|cons_Psalq_ri:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar8_4
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2 imm83,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2 ++ imm83
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["11000001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = b["100"] /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE /\ length imm83 = 8 /\ imm83 = (proj1_sig uvar8_4)),
Psalq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar8_4.
Inductive Psalq_rcl_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> Prop :=
|cons_Psalq_rcl:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["11010011"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = b["100"] /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Psalq_rcl_spec lst AddrE uvar1_0 uvar1_1 uvar1_2.
Inductive Pnotq_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> Prop :=
|cons_Pnotq:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["11110111"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = b["010"] /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pnotq_spec lst AddrE uvar1_0 uvar1_1 uvar1_2.
Inductive Pxorq_GvEv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Pxorq_GvEv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["00110011"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pxorq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Pxorq_EvGv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Pxorq_EvGv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["00110001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pxorq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Pxorq_ri_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u32 -> Prop :=
|cons_Pxorq_ri:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2 imm323,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2 ++ imm323
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["10000001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = b["110"] /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE /\ length imm323 = 32 /\ imm323 = (proj1_sig uvar32_4)),
Pxorq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4.
Inductive Porq_GvEv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Porq_GvEv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["00001011"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Porq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Porq_EvGv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Porq_EvGv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["00001001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Porq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Porq_ri_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u32 -> Prop :=
|cons_Porq_ri:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2 imm323,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2 ++ imm323
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["10000001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = b["001"] /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE /\ length imm323 = 32 /\ imm323 = (proj1_sig uvar32_4)),
Porq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4.
Inductive Pandq_GvEv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Pandq_GvEv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["00100011"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pandq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Pandq_EvGv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Pandq_EvGv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["00100001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pandq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Pandq_ri_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u32 -> Prop :=
|cons_Pandq_ri:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2 imm323,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2 ++ imm323
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["10000001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = b["100"] /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE /\ length imm323 = 32 /\ imm323 = (proj1_sig uvar32_4)),
Pandq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4.
Inductive Pdivq_spec: list bool -> u1 -> u3 -> Prop :=
|cons_Pdivq:
forall lst uvar1_0 uvar3_1
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = b["0"] /\ X0 = b["0"] /\ B0 = (proj1_sig uvar1_0) /\ length Opcode1 = 8 /\ Opcode1 = b["11110111"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ mod2 = b["11"] /\ reg_op2 = b["110"] /\ rm2 = (proj1_sig uvar3_1)),
Pdivq_spec lst uvar1_0 uvar3_1.
Inductive Pidivq_spec: list bool -> u1 -> u3 -> Prop :=
|cons_Pidivq:
forall lst uvar1_0 uvar3_1
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = b["0"] /\ X0 = b["0"] /\ B0 = (proj1_sig uvar1_0) /\ length Opcode1 = 8 /\ Opcode1 = b["11110111"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ mod2 = b["11"] /\ reg_op2 = b["111"] /\ rm2 = (proj1_sig uvar3_1)),
Pidivq_spec lst uvar1_0 uvar3_1.
Inductive Pmulq_r_spec: list bool -> u1 -> u3 -> Prop :=
|cons_Pmulq_r:
forall lst uvar1_0 uvar3_1
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = b["0"] /\ X0 = b["0"] /\ B0 = (proj1_sig uvar1_0) /\ length Opcode1 = 8 /\ Opcode1 = b["11110111"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ mod2 = b["11"] /\ reg_op2 = b["100"] /\ rm2 = (proj1_sig uvar3_1)),
Pmulq_r_spec lst uvar1_0 uvar3_1.
Inductive Pimulq_GvEv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Pimulq_GvEv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 Opcode2 mod3 reg_op3 rm3 AddrE3,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3 ++ AddrE3
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["10101111"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ reg_op3 = (proj1_sig uvar3_3) /\ AddrE_spec (mod3 ++ reg_op3 ++ rm3 ++ AddrE3) AddrE),
Pimulq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Pimulq_r_spec: list bool -> u1 -> u3 -> Prop :=
|cons_Pimulq_r:
forall lst uvar1_0 uvar3_1
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = b["0"] /\ X0 = b["0"] /\ B0 = (proj1_sig uvar1_0) /\ length Opcode1 = 8 /\ Opcode1 = b["11110111"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ mod2 = b["11"] /\ reg_op2 = b["101"] /\ rm2 = (proj1_sig uvar3_1)),
Pimulq_r_spec lst uvar1_0 uvar3_1.
Inductive Pimulq_ri_spec: list bool -> u1 -> u1 -> u3 -> u3 -> u32 -> Prop :=
|cons_Pimulq_ri:
forall lst uvar1_0 uvar1_1 uvar3_2 uvar3_3 uvar32_4
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 imm323,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ imm323
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ X0 = b["0"] /\ R0 = (proj1_sig uvar1_0) /\ B0 = (proj1_sig uvar1_1) /\ length Opcode1 = 8 /\ Opcode1 = b["01101001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ mod2 = b["11"] /\ reg_op2 = (proj1_sig uvar3_2) /\ rm2 = (proj1_sig uvar3_3) /\ length imm323 = 32 /\ imm323 = (proj1_sig uvar32_4)),
Pimulq_ri_spec lst uvar1_0 uvar1_1 uvar3_2 uvar3_3 uvar32_4.
Inductive Psubq_GvEv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Psubq_GvEv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["00101011"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Psubq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Psubq_EvGv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Psubq_EvGv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["00101001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Psubq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Psubq_ri_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u32 -> Prop :=
|cons_Psubq_ri:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2 imm323,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2 ++ imm323
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["10000001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = b["101"] /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE /\ length imm323 = 32 /\ imm323 = (proj1_sig uvar32_4)),
Psubq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4.
Inductive Paddq_GvEv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Paddq_GvEv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["00000011"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Paddq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Paddq_EvGv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Paddq_EvGv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["00000001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Paddq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Paddq_ri_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u32 -> Prop :=
|cons_Paddq_ri:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2 imm323,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2 ++ imm323
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["10000001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = b["000"] /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE /\ length imm323 = 32 /\ imm323 = (proj1_sig uvar32_4)),
Paddq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4.
Inductive Pnegq_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> Prop :=
|cons_Pnegq:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["11110111"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = b["011"] /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pnegq_spec lst AddrE uvar1_0 uvar1_1 uvar1_2.
Inductive Pleaq_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Pleaq:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["10001101"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pleaq_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Pmovq_EvGv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Pmovq_EvGv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["10001001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pmovq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Pmovq_GvEv_spec: list bool -> AddrE -> u1 -> u1 -> u1 -> u3 -> Prop :=
|cons_Pmovq_GvEv:
forall lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
(CONS: exists rmagic0 W0 R0 X0 B0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = (proj1_sig uvar1_0) /\ X0 = (proj1_sig uvar1_1) /\ B0 = (proj1_sig uvar1_2) /\ length Opcode1 = 8 /\ Opcode1 = b["10001011"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_3) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pmovq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3.
Inductive Pmovq_ri_spec: list bool -> u1 -> u3 -> u64 -> Prop :=
|cons_Pmovq_ri:
forall lst uvar1_0 uvar3_1 uvar64_2
(CONS: exists rmagic0 W0 R0 X0 B0 row1 page1 col1 imm642,
lst = rmagic0 ++ W0 ++ R0 ++ X0 ++ B0 ++ row1 ++ page1 ++ col1 ++ imm642
 /\ length rmagic0 = 4 /\ length W0 = 1 /\ length R0 = 1 /\ length X0 = 1 /\ length B0 = 1 /\ rmagic0 = b["0100"] /\ W0 = b["1"] /\ R0 = b["0"] /\ X0 = b["0"] /\ B0 = (proj1_sig uvar1_0) /\ length row1 = 4 /\ length page1 = 1 /\ length col1 = 3 /\ page1 = b["1"] /\ row1 = b["0001"] /\ col1 = (proj1_sig uvar3_1) /\ length imm642 = 64 /\ imm642 = (proj1_sig uvar64_2)),
Pmovq_ri_spec lst uvar1_0 uvar3_1 uvar64_2.
Inductive Psubl_ri_spec: list bool -> u3 -> u32 -> Prop :=
|cons_Psubl_ri:
forall lst uvar3_0 uvar32_1
(CONS: exists Opcode0 mod1 reg_op1 rm1 imm322,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ imm322
 /\ length Opcode0 = 8 /\ Opcode0 = b["10000001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["101"] /\ rm1 = (proj1_sig uvar3_0) /\ length imm322 = 32 /\ imm322 = (proj1_sig uvar32_1)),
Psubl_ri_spec lst uvar3_0 uvar32_1.
Inductive Pbsqrtsd_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pbsqrtsd:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110010"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["01010001"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ mod3 = b["11"] /\ reg_op3 = (proj1_sig uvar3_0) /\ rm3 = (proj1_sig uvar3_1)),
Pbsqrtsd_spec lst uvar3_0 uvar3_1.
Inductive Psbbl_rr_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Psbbl_rr:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["00011001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = (proj1_sig uvar3_0) /\ rm1 = (proj1_sig uvar3_1)),
Psbbl_rr_spec lst uvar3_0 uvar3_1.
Inductive Prep_movsl_spec: list bool -> Prop :=
|cons_Prep_movsl:
forall lst
(CONS: exists Opcode0 Opcode1,
lst = Opcode0 ++ Opcode1
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110011"] /\ length Opcode1 = 8 /\ Opcode1 = b["10100101"]),
Prep_movsl_spec lst.
Inductive Pmovsq_rm_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovsq_rm:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3 AddrE3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3 ++ AddrE3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110011"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["01111110"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ reg_op3 = (proj1_sig uvar3_0) /\ AddrE_spec (mod3 ++ reg_op3 ++ rm3 ++ AddrE3) AddrE),
Pmovsq_rm_spec lst AddrE uvar3_0.
Inductive Pmovsq_mr_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovsq_mr:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3 AddrE3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3 ++ AddrE3
 /\ length Opcode0 = 8 /\ Opcode0 = b["01100110"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["11010110"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ reg_op3 = (proj1_sig uvar3_0) /\ AddrE_spec (mod3 ++ reg_op3 ++ rm3 ++ AddrE3) AddrE),
Pmovsq_mr_spec lst AddrE uvar3_0.
Inductive Pminsd_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pminsd:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110010"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["01011101"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ mod3 = b["11"] /\ reg_op3 = (proj1_sig uvar3_0) /\ rm3 = (proj1_sig uvar3_1)),
Pminsd_spec lst uvar3_0 uvar3_1.
Inductive Pmaxsd_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pmaxsd:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110010"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["01011111"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ mod3 = b["11"] /\ reg_op3 = (proj1_sig uvar3_0) /\ rm3 = (proj1_sig uvar3_1)),
Pmaxsd_spec lst uvar3_0 uvar3_1.
Inductive Pbswap32_spec: list bool -> u3 -> Prop :=
|cons_Pbswap32:
forall lst uvar3_0
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["00001111"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["001"] /\ rm1 = (proj1_sig uvar3_0)),
Pbswap32_spec lst uvar3_0.
Inductive Pbsrl_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pbsrl:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 mod2 reg_op2 rm2,
lst = Opcode0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2
 /\ length Opcode0 = 8 /\ Opcode0 = b["00001111"] /\ length Opcode1 = 8 /\ Opcode1 = b["10111101"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ mod2 = b["11"] /\ reg_op2 = (proj1_sig uvar3_0) /\ rm2 = (proj1_sig uvar3_1)),
Pbsrl_spec lst uvar3_0 uvar3_1.
Inductive Pbsfl_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pbsfl:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 mod2 reg_op2 rm2,
lst = Opcode0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2
 /\ length Opcode0 = 8 /\ Opcode0 = b["00001111"] /\ length Opcode1 = 8 /\ Opcode1 = b["10111100"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ mod2 = b["11"] /\ reg_op2 = (proj1_sig uvar3_0) /\ rm2 = (proj1_sig uvar3_1)),
Pbsfl_spec lst uvar3_0 uvar3_1.
Inductive Paddl_mi_spec: list bool -> AddrE -> u32 -> Prop :=
|cons_Paddl_mi:
forall lst AddrE uvar32_1
(CONS: exists Opcode0 mod1 reg_op1 rm1 AddrE1 imm322,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ AddrE1 ++ imm322
 /\ length Opcode0 = 8 /\ Opcode0 = b["10000000"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ reg_op1 = b["000"] /\ AddrE_spec (mod1 ++ reg_op1 ++ rm1 ++ AddrE1) AddrE /\ length imm322 = 32 /\ imm322 = (proj1_sig uvar32_1)),
Paddl_mi_spec lst AddrE uvar32_1.
Inductive Paddl_rr_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Paddl_rr:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["00000001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = (proj1_sig uvar3_0) /\ rm1 = (proj1_sig uvar3_1)),
Paddl_rr_spec lst uvar3_0 uvar3_1.
Inductive Padcl_rr_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Padcl_rr:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["00010001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = (proj1_sig uvar3_0) /\ rm1 = (proj1_sig uvar3_1)),
Padcl_rr_spec lst uvar3_0 uvar3_1.
Inductive Padcl_ri_spec: list bool -> u3 -> u8 -> Prop :=
|cons_Padcl_ri:
forall lst uvar3_0 uvar8_1
(CONS: exists Opcode0 mod1 reg_op1 rm1 imm82,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ imm82
 /\ length Opcode0 = 8 /\ Opcode0 = b["10000011"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["010"] /\ rm1 = (proj1_sig uvar3_0) /\ length imm82 = 8 /\ imm82 = (proj1_sig uvar8_1)),
Padcl_ri_spec lst uvar3_0 uvar8_1.
Inductive Pjcc_rel_spec: list bool -> u4 -> u32 -> Prop :=
|cons_Pjcc_rel:
forall lst uvar4_0 uvar32_1
(CONS: exists Opcode0 cprefix1 cccode1 imm322,
lst = Opcode0 ++ cprefix1 ++ cccode1 ++ imm322
 /\ length Opcode0 = 8 /\ Opcode0 = b["00001111"] /\ length cprefix1 = 4 /\ length cccode1 = 4 /\ cprefix1 = b["1000"] /\ cccode1 = (proj1_sig uvar4_0) /\ length imm322 = 32 /\ imm322 = (proj1_sig uvar32_1)),
Pjcc_rel_spec lst uvar4_0 uvar32_1.
Inductive Pret_iw_spec: list bool -> u16 -> Prop :=
|cons_Pret_iw:
forall lst uvar16_0
(CONS: exists Opcode0 imm161,
lst = Opcode0 ++ imm161
 /\ length Opcode0 = 8 /\ Opcode0 = b["11000010"] /\ length imm161 = 16 /\ imm161 = (proj1_sig uvar16_0)),
Pret_iw_spec lst uvar16_0.
Inductive Pret_spec: list bool -> Prop :=
|cons_Pret:
forall lst
(CONS: exists Opcode0,
lst = Opcode0
 /\ length Opcode0 = 8 /\ Opcode0 = b["11000011"]),
Pret_spec lst.
Inductive Pcall_r_spec: list bool -> u3 -> Prop :=
|cons_Pcall_r:
forall lst uvar3_0
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["11111111"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["010"] /\ rm1 = (proj1_sig uvar3_0)),
Pcall_r_spec lst uvar3_0.
Inductive Pcall_ofs_spec: list bool -> u32 -> Prop :=
|cons_Pcall_ofs:
forall lst uvar32_0
(CONS: exists Opcode0 imm321,
lst = Opcode0 ++ imm321
 /\ length Opcode0 = 8 /\ Opcode0 = b["11101000"] /\ length imm321 = 32 /\ imm321 = (proj1_sig uvar32_0)),
Pcall_ofs_spec lst uvar32_0.
Inductive Pnop_spec: list bool -> Prop :=
|cons_Pnop:
forall lst
(CONS: exists Opcode0,
lst = Opcode0
 /\ length Opcode0 = 8 /\ Opcode0 = b["10010000"]),
Pnop_spec lst.
Inductive Pjmp_Ev_spec: list bool -> AddrE -> Prop :=
|cons_Pjmp_Ev:
forall lst AddrE
(CONS: exists Opcode0 mod1 reg_op1 rm1 AddrE1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ AddrE1
 /\ length Opcode0 = 8 /\ Opcode0 = b["11111111"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ reg_op1 = b["100"] /\ AddrE_spec (mod1 ++ reg_op1 ++ rm1 ++ AddrE1) AddrE),
Pjmp_Ev_spec lst AddrE.
Inductive Pjmp_l_rel_spec: list bool -> u32 -> Prop :=
|cons_Pjmp_l_rel:
forall lst uvar32_0
(CONS: exists Opcode0 imm321,
lst = Opcode0 ++ imm321
 /\ length Opcode0 = 8 /\ Opcode0 = b["11101001"] /\ length imm321 = 32 /\ imm321 = (proj1_sig uvar32_0)),
Pjmp_l_rel_spec lst uvar32_0.
Inductive Pandps_fm_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pandps_fm:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = Opcode0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length Opcode0 = 8 /\ Opcode0 = b["00001111"] /\ length Opcode1 = 8 /\ Opcode1 = b["01011000"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_0) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pandps_fm_spec lst AddrE uvar3_0.
Inductive Pxorps_GvEv_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pxorps_GvEv:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = Opcode0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length Opcode0 = 8 /\ Opcode0 = b["00001111"] /\ length Opcode1 = 8 /\ Opcode1 = b["01010111"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_0) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pxorps_GvEv_spec lst AddrE uvar3_0.
Inductive Pxorpd_GvEv_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pxorpd_GvEv:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3 AddrE3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3 ++ AddrE3
 /\ length Opcode0 = 8 /\ Opcode0 = b["01100110"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["01010111"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ reg_op3 = (proj1_sig uvar3_0) /\ AddrE_spec (mod3 ++ reg_op3 ++ rm3 ++ AddrE3) AddrE),
Pxorpd_GvEv_spec lst AddrE uvar3_0.
Inductive Pcomisd_ff_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pcomisd_ff:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3
 /\ length Opcode0 = 8 /\ Opcode0 = b["01100110"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["00101111"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ mod3 = b["11"] /\ reg_op3 = (proj1_sig uvar3_0) /\ rm3 = (proj1_sig uvar3_1)),
Pcomisd_ff_spec lst uvar3_0 uvar3_1.
Inductive Pdivss_ff_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pdivss_ff:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110011"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["01011110"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ mod3 = b["11"] /\ reg_op3 = (proj1_sig uvar3_0) /\ rm3 = (proj1_sig uvar3_1)),
Pdivss_ff_spec lst uvar3_0 uvar3_1.
Inductive Pdivsd_ff_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pdivsd_ff:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110010"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["01011110"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ mod3 = b["11"] /\ reg_op3 = (proj1_sig uvar3_0) /\ rm3 = (proj1_sig uvar3_1)),
Pdivsd_ff_spec lst uvar3_0 uvar3_1.
Inductive Pmuld_ff_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pmuld_ff:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110010"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["01011001"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ mod3 = b["11"] /\ reg_op3 = (proj1_sig uvar3_0) /\ rm3 = (proj1_sig uvar3_1)),
Pmuld_ff_spec lst uvar3_0 uvar3_1.
Inductive Psubd_ff_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Psubd_ff:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110010"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["01011100"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ mod3 = b["11"] /\ reg_op3 = (proj1_sig uvar3_0) /\ rm3 = (proj1_sig uvar3_1)),
Psubd_ff_spec lst uvar3_0 uvar3_1.
Inductive Paddd_ff_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Paddd_ff:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110010"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["01011000"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ mod3 = b["11"] /\ reg_op3 = (proj1_sig uvar3_0) /\ rm3 = (proj1_sig uvar3_1)),
Paddd_ff_spec lst uvar3_0 uvar3_1.
Inductive Psetcc_spec: list bool -> u4 -> u3 -> Prop :=
|cons_Psetcc:
forall lst uvar4_0 uvar3_1
(CONS: exists Opcode0 cprefix1 cccode1 mod2 reg_op2 rm2,
lst = Opcode0 ++ cprefix1 ++ cccode1 ++ mod2 ++ reg_op2 ++ rm2
 /\ length Opcode0 = 8 /\ Opcode0 = b["00001111"] /\ length cprefix1 = 4 /\ length cccode1 = 4 /\ cprefix1 = b["1001"] /\ cccode1 = (proj1_sig uvar4_0) /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ mod2 = b["11"] /\ reg_op2 = b["000"] /\ rm2 = (proj1_sig uvar3_1)),
Psetcc_spec lst uvar4_0 uvar3_1.
Inductive Pcmov_spec: list bool -> u4 -> u3 -> u3 -> Prop :=
|cons_Pcmov:
forall lst uvar4_0 uvar3_1 uvar3_2
(CONS: exists Opcode0 cprefix1 cccode1 mod2 reg_op2 rm2,
lst = Opcode0 ++ cprefix1 ++ cccode1 ++ mod2 ++ reg_op2 ++ rm2
 /\ length Opcode0 = 8 /\ Opcode0 = b["00001111"] /\ length cprefix1 = 4 /\ length cccode1 = 4 /\ cprefix1 = b["0100"] /\ cccode1 = (proj1_sig uvar4_0) /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ mod2 = b["11"] /\ reg_op2 = (proj1_sig uvar3_1) /\ rm2 = (proj1_sig uvar3_2)),
Pcmov_spec lst uvar4_0 uvar3_1 uvar3_2.
Inductive Ptestl_rr_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Ptestl_rr:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["10000101"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = (proj1_sig uvar3_0) /\ rm1 = (proj1_sig uvar3_1)),
Ptestl_rr_spec lst uvar3_0 uvar3_1.
Inductive Ptestl_ri_spec: list bool -> u3 -> u32 -> Prop :=
|cons_Ptestl_ri:
forall lst uvar3_0 uvar32_1
(CONS: exists Opcode0 mod1 reg_op1 rm1 imm322,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ imm322
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110111"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["000"] /\ rm1 = (proj1_sig uvar3_0) /\ length imm322 = 32 /\ imm322 = (proj1_sig uvar32_1)),
Ptestl_ri_spec lst uvar3_0 uvar32_1.
Inductive Pcmpl_ri_spec: list bool -> u3 -> u32 -> Prop :=
|cons_Pcmpl_ri:
forall lst uvar3_0 uvar32_1
(CONS: exists Opcode0 mod1 reg_op1 rm1 imm322,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ imm322
 /\ length Opcode0 = 8 /\ Opcode0 = b["10000001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["111"] /\ rm1 = (proj1_sig uvar3_0) /\ length imm322 = 32 /\ imm322 = (proj1_sig uvar32_1)),
Pcmpl_ri_spec lst uvar3_0 uvar32_1.
Inductive Pcmpl_rr_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pcmpl_rr:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["00111001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = (proj1_sig uvar3_0) /\ rm1 = (proj1_sig uvar3_1)),
Pcmpl_rr_spec lst uvar3_0 uvar3_1.
Inductive Prorl_ri_spec: list bool -> u3 -> u8 -> Prop :=
|cons_Prorl_ri:
forall lst uvar3_0 uvar8_1
(CONS: exists Opcode0 mod1 reg_op1 rm1 imm82,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ imm82
 /\ length Opcode0 = 8 /\ Opcode0 = b["11000001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ reg_op1 = b["001"] /\ mod1 = b["11"] /\ rm1 = (proj1_sig uvar3_0) /\ length imm82 = 8 /\ imm82 = (proj1_sig uvar8_1)),
Prorl_ri_spec lst uvar3_0 uvar8_1.
Inductive Prolw_ri_spec: list bool -> u3 -> u8 -> Prop :=
|cons_Prolw_ri:
forall lst uvar3_0 uvar8_1
(CONS: exists Opcode0 Opcode1 mod2 reg_op2 rm2 imm83,
lst = Opcode0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ imm83
 /\ length Opcode0 = 8 /\ Opcode0 = b["01100110"] /\ length Opcode1 = 8 /\ Opcode1 = b["11000001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ mod2 = b["11"] /\ reg_op2 = b["000"] /\ rm2 = (proj1_sig uvar3_0) /\ length imm83 = 8 /\ imm83 = (proj1_sig uvar8_1)),
Prolw_ri_spec lst uvar3_0 uvar8_1.
Inductive Pshld_ri_spec: list bool -> u3 -> u3 -> u8 -> Prop :=
|cons_Pshld_ri:
forall lst uvar3_0 uvar3_1 uvar8_2
(CONS: exists Opcode0 Opcode1 mod2 reg_op2 rm2 imm83,
lst = Opcode0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ imm83
 /\ length Opcode0 = 8 /\ Opcode0 = b["00001111"] /\ length Opcode1 = 8 /\ Opcode1 = b["10100100"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ mod2 = b["11"] /\ reg_op2 = (proj1_sig uvar3_0) /\ rm2 = (proj1_sig uvar3_1) /\ length imm83 = 8 /\ imm83 = (proj1_sig uvar8_2)),
Pshld_ri_spec lst uvar3_0 uvar3_1 uvar8_2.
Inductive Psarl_rcl_spec: list bool -> u3 -> Prop :=
|cons_Psarl_rcl:
forall lst uvar3_0
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["11010011"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["111"] /\ rm1 = (proj1_sig uvar3_0)),
Psarl_rcl_spec lst uvar3_0.
Inductive Psarl_ri_spec: list bool -> u3 -> u8 -> Prop :=
|cons_Psarl_ri:
forall lst uvar3_0 uvar8_1
(CONS: exists Opcode0 mod1 reg_op1 rm1 imm82,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ imm82
 /\ length Opcode0 = 8 /\ Opcode0 = b["11000001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["111"] /\ rm1 = (proj1_sig uvar3_0) /\ length imm82 = 8 /\ imm82 = (proj1_sig uvar8_1)),
Psarl_ri_spec lst uvar3_0 uvar8_1.
Inductive Pshrl_rcl_spec: list bool -> u3 -> Prop :=
|cons_Pshrl_rcl:
forall lst uvar3_0
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["11010011"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["101"] /\ rm1 = (proj1_sig uvar3_0)),
Pshrl_rcl_spec lst uvar3_0.
Inductive Pshrl_ri_spec: list bool -> u3 -> u8 -> Prop :=
|cons_Pshrl_ri:
forall lst uvar3_0 uvar8_1
(CONS: exists Opcode0 mod1 reg_op1 rm1 imm82,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ imm82
 /\ length Opcode0 = 8 /\ Opcode0 = b["11000001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["101"] /\ rm1 = (proj1_sig uvar3_0) /\ length imm82 = 8 /\ imm82 = (proj1_sig uvar8_1)),
Pshrl_ri_spec lst uvar3_0 uvar8_1.
Inductive Psall_rcl_spec: list bool -> u3 -> Prop :=
|cons_Psall_rcl:
forall lst uvar3_0
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["11010011"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["100"] /\ rm1 = (proj1_sig uvar3_0)),
Psall_rcl_spec lst uvar3_0.
Inductive Psall_ri_spec: list bool -> u3 -> u8 -> Prop :=
|cons_Psall_ri:
forall lst uvar3_0 uvar8_1
(CONS: exists Opcode0 mod1 reg_op1 rm1 imm82,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ imm82
 /\ length Opcode0 = 8 /\ Opcode0 = b["11000001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["100"] /\ rm1 = (proj1_sig uvar3_0) /\ length imm82 = 8 /\ imm82 = (proj1_sig uvar8_1)),
Psall_ri_spec lst uvar3_0 uvar8_1.
Inductive Pnotl_spec: list bool -> u3 -> Prop :=
|cons_Pnotl:
forall lst uvar3_0
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110111"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["010"] /\ rm1 = (proj1_sig uvar3_0)),
Pnotl_spec lst uvar3_0.
Inductive Pxorl_rr_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pxorl_rr:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["00110001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = (proj1_sig uvar3_0) /\ rm1 = (proj1_sig uvar3_1)),
Pxorl_rr_spec lst uvar3_0 uvar3_1.
Inductive Pxorl_ri_spec: list bool -> u3 -> u32 -> Prop :=
|cons_Pxorl_ri:
forall lst uvar3_0 uvar32_1
(CONS: exists Opcode0 mod1 reg_op1 rm1 imm322,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ imm322
 /\ length Opcode0 = 8 /\ Opcode0 = b["10000001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["110"] /\ rm1 = (proj1_sig uvar3_0) /\ length imm322 = 32 /\ imm322 = (proj1_sig uvar32_1)),
Pxorl_ri_spec lst uvar3_0 uvar32_1.
Inductive Porl_rr_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Porl_rr:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["00001001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = (proj1_sig uvar3_0) /\ rm1 = (proj1_sig uvar3_1)),
Porl_rr_spec lst uvar3_0 uvar3_1.
Inductive Porl_ri_spec: list bool -> u3 -> u32 -> Prop :=
|cons_Porl_ri:
forall lst uvar3_0 uvar32_1
(CONS: exists Opcode0 mod1 reg_op1 rm1 imm322,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ imm322
 /\ length Opcode0 = 8 /\ Opcode0 = b["10000001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["001"] /\ rm1 = (proj1_sig uvar3_0) /\ length imm322 = 32 /\ imm322 = (proj1_sig uvar32_1)),
Porl_ri_spec lst uvar3_0 uvar32_1.
Inductive Pandl_ri_spec: list bool -> u3 -> u32 -> Prop :=
|cons_Pandl_ri:
forall lst uvar3_0 uvar32_1
(CONS: exists Opcode0 mod1 reg_op1 rm1 imm322,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ imm322
 /\ length Opcode0 = 8 /\ Opcode0 = b["10000001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["100"] /\ rm1 = (proj1_sig uvar3_0) /\ length imm322 = 32 /\ imm322 = (proj1_sig uvar32_1)),
Pandl_ri_spec lst uvar3_0 uvar32_1.
Inductive Pandl_rr_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pandl_rr:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["00100001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = (proj1_sig uvar3_0) /\ rm1 = (proj1_sig uvar3_1)),
Pandl_rr_spec lst uvar3_0 uvar3_1.
Inductive Pidivl_r_spec: list bool -> u3 -> Prop :=
|cons_Pidivl_r:
forall lst uvar3_0
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110111"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["111"] /\ rm1 = (proj1_sig uvar3_0)),
Pidivl_r_spec lst uvar3_0.
Inductive Pdivl_r_spec: list bool -> u3 -> Prop :=
|cons_Pdivl_r:
forall lst uvar3_0
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110111"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["110"] /\ rm1 = (proj1_sig uvar3_0)),
Pdivl_r_spec lst uvar3_0.
Inductive Pcltd_spec: list bool -> Prop :=
|cons_Pcltd:
forall lst
(CONS: exists Opcode0,
lst = Opcode0
 /\ length Opcode0 = 8 /\ Opcode0 = b["10011001"]),
Pcltd_spec lst.
Inductive Pmull_r_spec: list bool -> u3 -> Prop :=
|cons_Pmull_r:
forall lst uvar3_0
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110111"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["100"] /\ rm1 = (proj1_sig uvar3_0)),
Pmull_r_spec lst uvar3_0.
Inductive Pimull_ri_spec: list bool -> u3 -> u3 -> u32 -> Prop :=
|cons_Pimull_ri:
forall lst uvar3_0 uvar3_1 uvar32_2
(CONS: exists Opcode0 mod1 reg_op1 rm1 imm322,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ imm322
 /\ length Opcode0 = 8 /\ Opcode0 = b["01101001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = (proj1_sig uvar3_0) /\ rm1 = (proj1_sig uvar3_1) /\ length imm322 = 32 /\ imm322 = (proj1_sig uvar32_2)),
Pimull_ri_spec lst uvar3_0 uvar3_1 uvar32_2.
Inductive Pimull_rr_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pimull_rr:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 mod2 reg_op2 rm2,
lst = Opcode0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2
 /\ length Opcode0 = 8 /\ Opcode0 = b["00001111"] /\ length Opcode1 = 8 /\ Opcode1 = b["10101111"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ mod2 = b["11"] /\ reg_op2 = (proj1_sig uvar3_0) /\ rm2 = (proj1_sig uvar3_1)),
Pimull_rr_spec lst uvar3_0 uvar3_1.
Inductive Psubl_rr_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Psubl_rr:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["00101011"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = (proj1_sig uvar3_0) /\ rm1 = (proj1_sig uvar3_1)),
Psubl_rr_spec lst uvar3_0 uvar3_1.
Inductive Paddl_ri_spec: list bool -> u3 -> u32 -> Prop :=
|cons_Paddl_ri:
forall lst uvar3_0 uvar32_1
(CONS: exists Opcode0 mod1 reg_op1 rm1 imm322,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ imm322
 /\ length Opcode0 = 8 /\ Opcode0 = b["10000001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["000"] /\ rm1 = (proj1_sig uvar3_0) /\ length imm322 = 32 /\ imm322 = (proj1_sig uvar32_1)),
Paddl_ri_spec lst uvar3_0 uvar32_1.
Inductive Pnegl_spec: list bool -> u3 -> Prop :=
|cons_Pnegl:
forall lst uvar3_0
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110111"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = b["011"] /\ rm1 = (proj1_sig uvar3_0)),
Pnegl_spec lst uvar3_0.
Inductive Pleal_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pleal:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 mod1 reg_op1 rm1 AddrE1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ AddrE1
 /\ length Opcode0 = 8 /\ Opcode0 = b["10001101"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ reg_op1 = (proj1_sig uvar3_0) /\ AddrE_spec (mod1 ++ reg_op1 ++ rm1 ++ AddrE1) AddrE),
Pleal_spec lst AddrE uvar3_0.
Inductive Pcvttss2si_rf_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pcvttss2si_rf:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110011"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["00101100"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ mod3 = b["11"] /\ reg_op3 = (proj1_sig uvar3_0) /\ rm3 = (proj1_sig uvar3_1)),
Pcvttss2si_rf_spec lst uvar3_0 uvar3_1.
Inductive Pcvtsi2sd_fr_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pcvtsi2sd_fr:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110010"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["00101010"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ mod3 = b["11"] /\ reg_op3 = (proj1_sig uvar3_0) /\ rm3 = (proj1_sig uvar3_1)),
Pcvtsi2sd_fr_spec lst uvar3_0 uvar3_1.
Inductive Pcvtsi2ss_fr_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pcvtsi2ss_fr:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110011"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["00101010"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ mod3 = b["11"] /\ reg_op3 = (proj1_sig uvar3_0) /\ rm3 = (proj1_sig uvar3_1)),
Pcvtsi2ss_fr_spec lst uvar3_0 uvar3_1.
Inductive Pcvttsd2si_rf_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pcvttsd2si_rf:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110010"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["00101100"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ mod3 = b["11"] /\ reg_op3 = (proj1_sig uvar3_0) /\ rm3 = (proj1_sig uvar3_1)),
Pcvttsd2si_rf_spec lst uvar3_0 uvar3_1.
Inductive Pcvtss2sd_ff_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pcvtss2sd_ff:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110011"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["01011010"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ mod3 = b["11"] /\ reg_op3 = (proj1_sig uvar3_0) /\ rm3 = (proj1_sig uvar3_1)),
Pcvtss2sd_ff_spec lst uvar3_0 uvar3_1.
Inductive Pcvtsd2ss_ff_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pcvtsd2ss_ff:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110010"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["01011010"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ mod3 = b["11"] /\ reg_op3 = (proj1_sig uvar3_0) /\ rm3 = (proj1_sig uvar3_1)),
Pcvtsd2ss_ff_spec lst uvar3_0 uvar3_1.
Inductive Pmovsw_GvEv_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovsw_GvEv:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = Opcode0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length Opcode0 = 8 /\ Opcode0 = b["00001111"] /\ length Opcode1 = 8 /\ Opcode1 = b["10111111"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_0) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pmovsw_GvEv_spec lst AddrE uvar3_0.
Inductive Pmovzw_GvEv_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovzw_GvEv:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = Opcode0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length Opcode0 = 8 /\ Opcode0 = b["00001111"] /\ length Opcode1 = 8 /\ Opcode1 = b["10110111"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_0) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pmovzw_GvEv_spec lst AddrE uvar3_0.
Inductive Pmovsb_GvEv_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovsb_GvEv:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = Opcode0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length Opcode0 = 8 /\ Opcode0 = b["00001111"] /\ length Opcode1 = 8 /\ Opcode1 = b["10111110"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_0) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pmovsb_GvEv_spec lst AddrE uvar3_0.
Inductive Pmovzb_rm_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovzb_rm:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = Opcode0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length Opcode0 = 8 /\ Opcode0 = b["00001111"] /\ length Opcode1 = 8 /\ Opcode1 = b["10110110"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_0) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pmovzb_rm_spec lst AddrE uvar3_0.
Inductive Pmovw_rm_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovw_rm:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = Opcode0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length Opcode0 = 8 /\ Opcode0 = b["01100110"] /\ length Opcode1 = 8 /\ Opcode1 = b["10001011"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_0) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pmovw_rm_spec lst AddrE uvar3_0.
Inductive Pmovw_mr_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovw_mr:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 Opcode1 mod2 reg_op2 rm2 AddrE2,
lst = Opcode0 ++ Opcode1 ++ mod2 ++ reg_op2 ++ rm2 ++ AddrE2
 /\ length Opcode0 = 8 /\ Opcode0 = b["01100110"] /\ length Opcode1 = 8 /\ Opcode1 = b["10001001"] /\ length mod2 = 2 /\ length reg_op2 = 3 /\ length rm2 = 3 /\ reg_op2 = (proj1_sig uvar3_0) /\ AddrE_spec (mod2 ++ reg_op2 ++ rm2 ++ AddrE2) AddrE),
Pmovw_mr_spec lst AddrE uvar3_0.
Inductive Pmovb_rm_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovb_rm:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 mod1 reg_op1 rm1 AddrE1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ AddrE1
 /\ length Opcode0 = 8 /\ Opcode0 = b["10001010"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ reg_op1 = (proj1_sig uvar3_0) /\ AddrE_spec (mod1 ++ reg_op1 ++ rm1 ++ AddrE1) AddrE),
Pmovb_rm_spec lst AddrE uvar3_0.
Inductive Pmovb_mr_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovb_mr:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 mod1 reg_op1 rm1 AddrE1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ AddrE1
 /\ length Opcode0 = 8 /\ Opcode0 = b["10001000"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ reg_op1 = (proj1_sig uvar3_0) /\ AddrE_spec (mod1 ++ reg_op1 ++ rm1 ++ AddrE1) AddrE),
Pmovb_mr_spec lst AddrE uvar3_0.
Inductive Pxchg_rr_spec: list bool -> u3 -> u3 -> Prop :=
|cons_Pxchg_rr:
forall lst uvar3_0 uvar3_1
(CONS: exists Opcode0 mod1 reg_op1 rm1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1
 /\ length Opcode0 = 8 /\ Opcode0 = b["10000111"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ mod1 = b["11"] /\ reg_op1 = (proj1_sig uvar3_0) /\ rm1 = (proj1_sig uvar3_1)),
Pxchg_rr_spec lst uvar3_0 uvar3_1.
Inductive Pflds_m_spec: list bool -> AddrE -> Prop :=
|cons_Pflds_m:
forall lst AddrE
(CONS: exists Opcode0 mod1 reg_op1 rm1 AddrE1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ AddrE1
 /\ length Opcode0 = 8 /\ Opcode0 = b["11011001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ reg_op1 = b["000"] /\ AddrE_spec (mod1 ++ reg_op1 ++ rm1 ++ AddrE1) AddrE),
Pflds_m_spec lst AddrE.
Inductive Pfstps_m_spec: list bool -> AddrE -> Prop :=
|cons_Pfstps_m:
forall lst AddrE
(CONS: exists Opcode0 mod1 reg_op1 rm1 AddrE1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ AddrE1
 /\ length Opcode0 = 8 /\ Opcode0 = b["11011001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ reg_op1 = b["011"] /\ AddrE_spec (mod1 ++ reg_op1 ++ rm1 ++ AddrE1) AddrE),
Pfstps_m_spec lst AddrE.
Inductive Pfstpl_m_spec: list bool -> AddrE -> Prop :=
|cons_Pfstpl_m:
forall lst AddrE
(CONS: exists Opcode0 mod1 reg_op1 rm1 AddrE1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ AddrE1
 /\ length Opcode0 = 8 /\ Opcode0 = b["11011101"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ reg_op1 = b["011"] /\ AddrE_spec (mod1 ++ reg_op1 ++ rm1 ++ AddrE1) AddrE),
Pfstpl_m_spec lst AddrE.
Inductive Pfldl_m_spec: list bool -> AddrE -> Prop :=
|cons_Pfldl_m:
forall lst AddrE
(CONS: exists Opcode0 mod1 reg_op1 rm1 AddrE1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ AddrE1
 /\ length Opcode0 = 8 /\ Opcode0 = b["11011101"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ reg_op1 = b["000"] /\ AddrE_spec (mod1 ++ reg_op1 ++ rm1 ++ AddrE1) AddrE),
Pfldl_m_spec lst AddrE.
Inductive Pmovss_fm_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovss_fm:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3 AddrE3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3 ++ AddrE3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110011"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["00010000"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ reg_op3 = (proj1_sig uvar3_0) /\ AddrE_spec (mod3 ++ reg_op3 ++ rm3 ++ AddrE3) AddrE),
Pmovss_fm_spec lst AddrE uvar3_0.
Inductive Pmovss_mf_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovss_mf:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3 AddrE3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3 ++ AddrE3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110011"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["00010001"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ reg_op3 = (proj1_sig uvar3_0) /\ AddrE_spec (mod3 ++ reg_op3 ++ rm3 ++ AddrE3) AddrE),
Pmovss_mf_spec lst AddrE uvar3_0.
Inductive Pmovsd_fm_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovsd_fm:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3 AddrE3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3 ++ AddrE3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110010"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["00010000"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ reg_op3 = (proj1_sig uvar3_0) /\ AddrE_spec (mod3 ++ reg_op3 ++ rm3 ++ AddrE3) AddrE),
Pmovsd_fm_spec lst AddrE uvar3_0.
Inductive Pmovsd_mf_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovsd_mf:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 Opcode1 Opcode2 mod3 reg_op3 rm3 AddrE3,
lst = Opcode0 ++ Opcode1 ++ Opcode2 ++ mod3 ++ reg_op3 ++ rm3 ++ AddrE3
 /\ length Opcode0 = 8 /\ Opcode0 = b["11110010"] /\ length Opcode1 = 8 /\ Opcode1 = b["00001111"] /\ length Opcode2 = 8 /\ Opcode2 = b["00010001"] /\ length mod3 = 2 /\ length reg_op3 = 3 /\ length rm3 = 3 /\ reg_op3 = (proj1_sig uvar3_0) /\ AddrE_spec (mod3 ++ reg_op3 ++ rm3 ++ AddrE3) AddrE),
Pmovsd_mf_spec lst AddrE uvar3_0.
Inductive Pmovl_rm_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovl_rm:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 mod1 reg_op1 rm1 AddrE1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ AddrE1
 /\ length Opcode0 = 8 /\ Opcode0 = b["10001011"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ reg_op1 = (proj1_sig uvar3_0) /\ AddrE_spec (mod1 ++ reg_op1 ++ rm1 ++ AddrE1) AddrE),
Pmovl_rm_spec lst AddrE uvar3_0.
Inductive Pmovl_mr_spec: list bool -> AddrE -> u3 -> Prop :=
|cons_Pmovl_mr:
forall lst AddrE uvar3_0
(CONS: exists Opcode0 mod1 reg_op1 rm1 AddrE1,
lst = Opcode0 ++ mod1 ++ reg_op1 ++ rm1 ++ AddrE1
 /\ length Opcode0 = 8 /\ Opcode0 = b["10001001"] /\ length mod1 = 2 /\ length reg_op1 = 3 /\ length rm1 = 3 /\ reg_op1 = (proj1_sig uvar3_0) /\ AddrE_spec (mod1 ++ reg_op1 ++ rm1 ++ AddrE1) AddrE),
Pmovl_mr_spec lst AddrE uvar3_0.
Inductive Pmovl_ri_spec: list bool -> u3 -> u32 -> Prop :=
|cons_Pmovl_ri:
forall lst uvar3_0 uvar32_1
(CONS: exists row0 page0 col0 imm321,
lst = row0 ++ page0 ++ col0 ++ imm321
 /\ length row0 = 4 /\ length page0 = 1 /\ length col0 = 3 /\ row0 = b["1011"] /\ page0 = b["1"] /\ col0 = (proj1_sig uvar3_0) /\ length imm321 = 32 /\ imm321 = (proj1_sig uvar32_1)),
Pmovl_ri_spec lst uvar3_0 uvar32_1.
Definition Instruction_spec lst  element : Prop :=
	match element with
| Ptestq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Ptestq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Ptestq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4 => Ptestq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4
| Pcmpq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Pcmpq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Pcmpq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Pcmpq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Pcmpq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4 => Pcmpq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4
| Prorq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar8_4 => Prorq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar8_4
| Psarq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar8_4 => Psarq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar8_4
| Psarq_rcl AddrE uvar1_0 uvar1_1 uvar1_2 => Psarq_rcl_spec lst AddrE uvar1_0 uvar1_1 uvar1_2
| Psalq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar8_4 => Psalq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar8_4
| Psalq_rcl AddrE uvar1_0 uvar1_1 uvar1_2 => Psalq_rcl_spec lst AddrE uvar1_0 uvar1_1 uvar1_2
| Pnotq AddrE uvar1_0 uvar1_1 uvar1_2 => Pnotq_spec lst AddrE uvar1_0 uvar1_1 uvar1_2
| Pxorq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Pxorq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Pxorq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Pxorq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Pxorq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4 => Pxorq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4
| Porq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Porq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Porq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Porq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Porq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4 => Porq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4
| Pandq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Pandq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Pandq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Pandq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Pandq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4 => Pandq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4
| Pdivq uvar1_0 uvar3_1 => Pdivq_spec lst uvar1_0 uvar3_1
| Pidivq uvar1_0 uvar3_1 => Pidivq_spec lst uvar1_0 uvar3_1
| Pmulq_r uvar1_0 uvar3_1 => Pmulq_r_spec lst uvar1_0 uvar3_1
| Pimulq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Pimulq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Pimulq_r uvar1_0 uvar3_1 => Pimulq_r_spec lst uvar1_0 uvar3_1
| Pimulq_ri uvar1_0 uvar1_1 uvar3_2 uvar3_3 uvar32_4 => Pimulq_ri_spec lst uvar1_0 uvar1_1 uvar3_2 uvar3_3 uvar32_4
| Psubq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Psubq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Psubq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Psubq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Psubq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4 => Psubq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4
| Paddq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Paddq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Paddq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Paddq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Paddq_ri AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4 => Paddq_ri_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar32_4
| Pnegq AddrE uvar1_0 uvar1_1 uvar1_2 => Pnegq_spec lst AddrE uvar1_0 uvar1_1 uvar1_2
| Pleaq AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Pleaq_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Pmovq_EvGv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Pmovq_EvGv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Pmovq_GvEv AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3 => Pmovq_GvEv_spec lst AddrE uvar1_0 uvar1_1 uvar1_2 uvar3_3
| Pmovq_ri uvar1_0 uvar3_1 uvar64_2 => Pmovq_ri_spec lst uvar1_0 uvar3_1 uvar64_2
| Psubl_ri uvar3_0 uvar32_1 => Psubl_ri_spec lst uvar3_0 uvar32_1
| Pbsqrtsd uvar3_0 uvar3_1 => Pbsqrtsd_spec lst uvar3_0 uvar3_1
| Psbbl_rr uvar3_0 uvar3_1 => Psbbl_rr_spec lst uvar3_0 uvar3_1
| Prep_movsl => Prep_movsl_spec lst
| Pmovsq_rm AddrE uvar3_0 => Pmovsq_rm_spec lst AddrE uvar3_0
| Pmovsq_mr AddrE uvar3_0 => Pmovsq_mr_spec lst AddrE uvar3_0
| Pminsd uvar3_0 uvar3_1 => Pminsd_spec lst uvar3_0 uvar3_1
| Pmaxsd uvar3_0 uvar3_1 => Pmaxsd_spec lst uvar3_0 uvar3_1
| Pbswap32 uvar3_0 => Pbswap32_spec lst uvar3_0
| Pbsrl uvar3_0 uvar3_1 => Pbsrl_spec lst uvar3_0 uvar3_1
| Pbsfl uvar3_0 uvar3_1 => Pbsfl_spec lst uvar3_0 uvar3_1
| Paddl_mi AddrE uvar32_1 => Paddl_mi_spec lst AddrE uvar32_1
| Paddl_rr uvar3_0 uvar3_1 => Paddl_rr_spec lst uvar3_0 uvar3_1
| Padcl_rr uvar3_0 uvar3_1 => Padcl_rr_spec lst uvar3_0 uvar3_1
| Padcl_ri uvar3_0 uvar8_1 => Padcl_ri_spec lst uvar3_0 uvar8_1
| Pjcc_rel uvar4_0 uvar32_1 => Pjcc_rel_spec lst uvar4_0 uvar32_1
| Pret_iw uvar16_0 => Pret_iw_spec lst uvar16_0
| Pret => Pret_spec lst
| Pcall_r uvar3_0 => Pcall_r_spec lst uvar3_0
| Pcall_ofs uvar32_0 => Pcall_ofs_spec lst uvar32_0
| Pnop => Pnop_spec lst
| Pjmp_Ev AddrE => Pjmp_Ev_spec lst AddrE
| Pjmp_l_rel uvar32_0 => Pjmp_l_rel_spec lst uvar32_0
| Pandps_fm AddrE uvar3_0 => Pandps_fm_spec lst AddrE uvar3_0
| Pxorps_GvEv AddrE uvar3_0 => Pxorps_GvEv_spec lst AddrE uvar3_0
| Pxorpd_GvEv AddrE uvar3_0 => Pxorpd_GvEv_spec lst AddrE uvar3_0
| Pcomisd_ff uvar3_0 uvar3_1 => Pcomisd_ff_spec lst uvar3_0 uvar3_1
| Pdivss_ff uvar3_0 uvar3_1 => Pdivss_ff_spec lst uvar3_0 uvar3_1
| Pdivsd_ff uvar3_0 uvar3_1 => Pdivsd_ff_spec lst uvar3_0 uvar3_1
| Pmuld_ff uvar3_0 uvar3_1 => Pmuld_ff_spec lst uvar3_0 uvar3_1
| Psubd_ff uvar3_0 uvar3_1 => Psubd_ff_spec lst uvar3_0 uvar3_1
| Paddd_ff uvar3_0 uvar3_1 => Paddd_ff_spec lst uvar3_0 uvar3_1
| Psetcc uvar4_0 uvar3_1 => Psetcc_spec lst uvar4_0 uvar3_1
| Pcmov uvar4_0 uvar3_1 uvar3_2 => Pcmov_spec lst uvar4_0 uvar3_1 uvar3_2
| Ptestl_rr uvar3_0 uvar3_1 => Ptestl_rr_spec lst uvar3_0 uvar3_1
| Ptestl_ri uvar3_0 uvar32_1 => Ptestl_ri_spec lst uvar3_0 uvar32_1
| Pcmpl_ri uvar3_0 uvar32_1 => Pcmpl_ri_spec lst uvar3_0 uvar32_1
| Pcmpl_rr uvar3_0 uvar3_1 => Pcmpl_rr_spec lst uvar3_0 uvar3_1
| Prorl_ri uvar3_0 uvar8_1 => Prorl_ri_spec lst uvar3_0 uvar8_1
| Prolw_ri uvar3_0 uvar8_1 => Prolw_ri_spec lst uvar3_0 uvar8_1
| Pshld_ri uvar3_0 uvar3_1 uvar8_2 => Pshld_ri_spec lst uvar3_0 uvar3_1 uvar8_2
| Psarl_rcl uvar3_0 => Psarl_rcl_spec lst uvar3_0
| Psarl_ri uvar3_0 uvar8_1 => Psarl_ri_spec lst uvar3_0 uvar8_1
| Pshrl_rcl uvar3_0 => Pshrl_rcl_spec lst uvar3_0
| Pshrl_ri uvar3_0 uvar8_1 => Pshrl_ri_spec lst uvar3_0 uvar8_1
| Psall_rcl uvar3_0 => Psall_rcl_spec lst uvar3_0
| Psall_ri uvar3_0 uvar8_1 => Psall_ri_spec lst uvar3_0 uvar8_1
| Pnotl uvar3_0 => Pnotl_spec lst uvar3_0
| Pxorl_rr uvar3_0 uvar3_1 => Pxorl_rr_spec lst uvar3_0 uvar3_1
| Pxorl_ri uvar3_0 uvar32_1 => Pxorl_ri_spec lst uvar3_0 uvar32_1
| Porl_rr uvar3_0 uvar3_1 => Porl_rr_spec lst uvar3_0 uvar3_1
| Porl_ri uvar3_0 uvar32_1 => Porl_ri_spec lst uvar3_0 uvar32_1
| Pandl_ri uvar3_0 uvar32_1 => Pandl_ri_spec lst uvar3_0 uvar32_1
| Pandl_rr uvar3_0 uvar3_1 => Pandl_rr_spec lst uvar3_0 uvar3_1
| Pidivl_r uvar3_0 => Pidivl_r_spec lst uvar3_0
| Pdivl_r uvar3_0 => Pdivl_r_spec lst uvar3_0
| Pcltd => Pcltd_spec lst
| Pmull_r uvar3_0 => Pmull_r_spec lst uvar3_0
| Pimull_ri uvar3_0 uvar3_1 uvar32_2 => Pimull_ri_spec lst uvar3_0 uvar3_1 uvar32_2
| Pimull_rr uvar3_0 uvar3_1 => Pimull_rr_spec lst uvar3_0 uvar3_1
| Psubl_rr uvar3_0 uvar3_1 => Psubl_rr_spec lst uvar3_0 uvar3_1
| Paddl_ri uvar3_0 uvar32_1 => Paddl_ri_spec lst uvar3_0 uvar32_1
| Pnegl uvar3_0 => Pnegl_spec lst uvar3_0
| Pleal AddrE uvar3_0 => Pleal_spec lst AddrE uvar3_0
| Pcvttss2si_rf uvar3_0 uvar3_1 => Pcvttss2si_rf_spec lst uvar3_0 uvar3_1
| Pcvtsi2sd_fr uvar3_0 uvar3_1 => Pcvtsi2sd_fr_spec lst uvar3_0 uvar3_1
| Pcvtsi2ss_fr uvar3_0 uvar3_1 => Pcvtsi2ss_fr_spec lst uvar3_0 uvar3_1
| Pcvttsd2si_rf uvar3_0 uvar3_1 => Pcvttsd2si_rf_spec lst uvar3_0 uvar3_1
| Pcvtss2sd_ff uvar3_0 uvar3_1 => Pcvtss2sd_ff_spec lst uvar3_0 uvar3_1
| Pcvtsd2ss_ff uvar3_0 uvar3_1 => Pcvtsd2ss_ff_spec lst uvar3_0 uvar3_1
| Pmovsw_GvEv AddrE uvar3_0 => Pmovsw_GvEv_spec lst AddrE uvar3_0
| Pmovzw_GvEv AddrE uvar3_0 => Pmovzw_GvEv_spec lst AddrE uvar3_0
| Pmovsb_GvEv AddrE uvar3_0 => Pmovsb_GvEv_spec lst AddrE uvar3_0
| Pmovzb_rm AddrE uvar3_0 => Pmovzb_rm_spec lst AddrE uvar3_0
| Pmovw_rm AddrE uvar3_0 => Pmovw_rm_spec lst AddrE uvar3_0
| Pmovw_mr AddrE uvar3_0 => Pmovw_mr_spec lst AddrE uvar3_0
| Pmovb_rm AddrE uvar3_0 => Pmovb_rm_spec lst AddrE uvar3_0
| Pmovb_mr AddrE uvar3_0 => Pmovb_mr_spec lst AddrE uvar3_0
| Pxchg_rr uvar3_0 uvar3_1 => Pxchg_rr_spec lst uvar3_0 uvar3_1
| Pflds_m AddrE => Pflds_m_spec lst AddrE
| Pfstps_m AddrE => Pfstps_m_spec lst AddrE
| Pfstpl_m AddrE => Pfstpl_m_spec lst AddrE
| Pfldl_m AddrE => Pfldl_m_spec lst AddrE
| Pmovss_fm AddrE uvar3_0 => Pmovss_fm_spec lst AddrE uvar3_0
| Pmovss_mf AddrE uvar3_0 => Pmovss_mf_spec lst AddrE uvar3_0
| Pmovsd_fm AddrE uvar3_0 => Pmovsd_fm_spec lst AddrE uvar3_0
| Pmovsd_mf AddrE uvar3_0 => Pmovsd_mf_spec lst AddrE uvar3_0
| Pmovl_rm AddrE uvar3_0 => Pmovl_rm_spec lst AddrE uvar3_0
| Pmovl_mr AddrE uvar3_0 => Pmovl_mr_spec lst AddrE uvar3_0
| Pmovl_ri uvar3_0 uvar32_1 => Pmovl_ri_spec lst uvar3_0 uvar32_1
end.


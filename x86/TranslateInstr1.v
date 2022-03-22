Require Import Coqlib Maps Integers Floats Values AST Errors.
Require Import Axioms Globalenvs.
Require Import Asm RelocProgram.
Require Import Hex compcert.encode.Bits Memdata Encode.
Require Import Reloctablesgen.
Require Import SymbolString.
(* Import Hex compcert.encode.Bits.Bits. *)
Require Import Coq.Logic.Eqdep_dec.
(* Require Import RelocBingen. *)
Require Import EncDecRet BPProperty.
Import Hex Bits.
Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.

(** *CAV21: Instruction ,CompCertELF: instruction*)

(** * Encoding of instructions and functions *)

Definition encode_ireg (r: ireg) : res bits :=
  match r with
  | RAX => OK (b["000"])
  | RCX => OK (b["001"])
  | RDX => OK (b["010"])
  | RBX => OK (b["011"])
  | RSP => OK (b["100"])
  | RBP => OK (b["101"])
  | RSI => OK (b["110"])
  | RDI => OK (b["111"])
  | _ => Error (msg "Encoding of register not supported")
  end.

Definition encode_freg (r: freg) : res bits :=
  match r with
  | XMM0 => OK (b["000"])
  | XMM1 => OK (b["001"])
  | XMM2 => OK (b["010"])
  | XMM3 => OK (b["011"])
  | XMM4 => OK (b["100"])
  | XMM5 => OK (b["101"])
  | XMM6 => OK (b["110"])
  | XMM7 => OK (b["111"])
  | _ => Error (msg "Encoding of freg not supported")
  end.

Definition encode_scale (s: Z) : res bits :=
  match s with
  | 1 => OK b["00"]
  | 2 => OK b["01"]
  | 4 => OK b["10"]
  | 8 => OK b["11"]
  | _ => Error (msg "Translation of scale failed")
  end.


Program Definition zero32 : u32 :=
  bytes_to_bits_opt (bytes_of_int 4 0).

Program Definition encode_ireg_u3 (r:ireg) : res u3 :=
  do b <- encode_ireg r;
  if assertLength b 3 then
    OK (exist _ b _)
  else Error (msg "impossible").

Definition decode_ireg (bs: u3) : res ireg :=
  let bs' := proj1_sig bs in
  let n := bits_to_Z bs' in
  if Z.eqb n 0 then OK(RAX)           (**r b["000"] *)
  else if Z.eqb n 1 then OK(RCX)      (**r b["001"] *)
  else if Z.eqb n 2 then OK(RDX)      (**r b["010"] *)
  else if Z.eqb n 3 then OK(RBX)      (**r b["011"] *)
  else if Z.eqb n 4 then OK(RSP)      (**r b["100"] *)
  else if Z.eqb n 5 then OK(RBP)      (**r b["101"] *)
  else if Z.eqb n 6 then OK(RSI)      (**r b["110"] *)
  else if Z.eqb n 7 then OK(RDI)      (**r b["111"] *)
  else Error(msg "reg not found")
.

Lemma ireg_encode_consistency :
  forall r encoded,
  encode_ireg_u3 r = OK(encoded) ->
  decode_ireg encoded = OK(r).
Proof.
  intros.
  destruct encoded.
  unfold encode_ireg_u3 in H.
  destruct r; simpl in H;
  inversion H;                (**r extract the encoded result b from H *)
  subst; try reflexivity.
Qed.

Lemma ireg_decode_consistency :
  forall r encoded,
  decode_ireg encoded = OK(r) ->
  encode_ireg_u3 r = OK(encoded).
Proof.
  intros.
  destruct encoded as [b Hlen].
  (** extract three bits from b *)
  destruct b as [| b0 b]; try discriminate; inversion Hlen. (**r the 1st one *)
  destruct b as [| b1 b]; try discriminate; inversion Hlen. (**r the 2nd one *)
  destruct b as [| b2 b]; try discriminate; inversion Hlen. (**r the 3rd one *)
  destruct b; try discriminate.                          (**r b is a empty list now, eliminate other possibility *)
  (** case analysis on [b0, b1, b2] *)
  destruct b0, b1, b2 eqn:Eb;
  unfold decode_ireg in H; simpl in H; (**r extract decoded result r from H *)
  inversion H; subst;                  (**r subst r *)
  unfold encode_ireg_u3; simpl;        (**r calculate encode_ireg_u3 *)
  unfold char_to_bool; simpl;
  replace eq_refl with Hlen;
  try reflexivity;                     (**r to solve OK(exsit _ _ Hlen) = OK(exsit _ _ Hlen) *)
  try apply proof_irr.                 (**r to solve e = eq_refl *)
Qed.

Program Definition encode_freg_u3 (r:freg) : res u3 :=
  do b <- encode_freg r;
  if assertLength b 3 then
    OK (exist _ b _)
  else Error (msg "impossible").

Definition decode_freg (bs: u3) : res freg :=
  let bs' := proj1_sig bs in
  let n := bits_to_Z bs' in
  if Z.eqb n 0 then OK(XMM0)           (**r b["000"] *)
  else if Z.eqb n 1 then OK(XMM1)      (**r b["001"] *)
  else if Z.eqb n 2 then OK(XMM2)      (**r b["010"] *)
  else if Z.eqb n 3 then OK(XMM3)      (**r b["011"] *)
  else if Z.eqb n 4 then OK(XMM4)      (**r b["100"] *)
  else if Z.eqb n 5 then OK(XMM5)      (**r b["101"] *)
  else if Z.eqb n 6 then OK(XMM6)      (**r b["110"] *)
  else if Z.eqb n 7 then OK(XMM7)      (**r b["111"] *)
  else Error(msg "reg not found")
.

Lemma freg_encode_consistency :
  forall r encoded,
  encode_freg_u3 r = OK(encoded) ->
  decode_freg encoded = OK(r).
Proof.
  intros.
  destruct encoded.
  unfold encode_freg_u3 in H.
  destruct r; simpl in H;
  inversion H;                (**r extract the encoded result b from H *)
  subst; try reflexivity.
Qed.

Lemma freg_decode_consistency :
  forall r encoded,
  decode_freg encoded = OK(r) ->
  encode_freg_u3 r = OK(encoded).
Proof.
  intros.
  destruct encoded as [b Hlen].
  (** extract three bits from b *)
  destruct b as [| b0 b]; try discriminate; inversion Hlen. (**r the 1st one *)
  destruct b as [| b1 b]; try discriminate; inversion Hlen. (**r the 2nd one *)
  destruct b as [| b2 b]; try discriminate; inversion Hlen. (**r the 3rd one *)
  destruct b; try discriminate.                          (**r b is a empty list now, eliminate other possibility *)
  (** case analysis on [b0, b1, b2] *)
  destruct b0, b1, b2 eqn:Eb;
  unfold decode_freg in H; simpl in H; (**r extract decoded result r from H *)
  inversion H; subst;                  (**r subst r *)
  unfold encode_freg_u3; simpl;        (**r calculate encode_freg_u3 *)
  unfold char_to_bool; simpl;
  replace eq_refl with Hlen;
  try reflexivity;                     (**r to solve OK(exsit _ _ Hlen) = OK(exsit _ _ Hlen) *)
  try apply proof_irr.                 (**r to solve e = eq_refl *)
Qed.

Program Definition encode_scale_u2 (ss: Z) :res u2 :=
  do s <- encode_scale ss;
  if assertLength s 2 then
    OK (exist _ s _)
  else Error (msg "impossible").

Definition decode_scale (bs: u2) : res Z :=
  let bs' := proj1_sig bs in
  let n := bits_to_Z bs' in
  if Z.eqb n 0 then OK(1%Z)           (**r b["000"] *)
  else if Z.eqb n 1 then OK(2%Z)      (**r b["001"] *)
  else if Z.eqb n 2 then OK(4%Z)      (**r b["010"] *)
  else if Z.eqb n 3 then OK(8%Z)      (**r b["011"] *)
  else Error(msg "reg not found")
.

Lemma scale_encode_consistency :
  forall ss encoded,
  encode_scale_u2 ss = OK(encoded) ->
  decode_scale encoded = OK(ss).
Proof.
  intros.
  destruct encoded.
  unfold encode_scale_u2 in H; monadInv H.

  destruct (assertLength x0 2); try discriminate.  (**r prove x = x0 *)
  inversion EQ0; subst.

  unfold encode_scale in EQ.
  destruct ss eqn:Ess; try discriminate.
  repeat (destruct p; try discriminate);           (**r generate subgoals for each scale 1/2/4/8 *)
  inversion EQ as [Heq]; subst; simpl;             (**r replace x with exact value *)
  unfold decode_scale; auto.                       (**r get result of function decode_scale *)
Qed.

Lemma scale_decode_consistency :
  forall r encoded,
  decode_scale encoded = OK(r) ->
  encode_scale_u2 r = OK(encoded).
Proof.
  intros.
  destruct encoded as [b Hlen].
  (** extract three bits from b *)
  destruct b as [| b0 b]; try discriminate; inversion Hlen. (**r the 1st one *)
  destruct b as [| b1 b]; try discriminate; inversion Hlen. (**r the 2nd one *)
  destruct b; try discriminate.                          (**r b is a empty list now, eliminate other possibility *)
  (** case analysis on [b0, b1] *)
  destruct b0, b1 eqn:Eb;
  unfold decode_scale in H; simpl in H; (**r extract decoded result r from H *)
  inversion H; subst;                  (**r subst r *)
  unfold encode_scale_u2; simpl;        (**r calculate encode_scale_u2 *)
  unfold char_to_bool; simpl;
  replace eq_refl with Hlen;
  try reflexivity;                     (**r to solve OK(exsit _ _ Hlen) = OK(exsit _ _ Hlen) *)
  try apply proof_irr.                 (**r to solve e = eq_refl *)
Qed.

Program Definition encode_ofs_u8 (ofs:Z) :res u8 :=
  let ofs8 := bytes_to_bits_opt (bytes_of_int 1 ofs) in
  if assertLength ofs8 8 then
    OK (exist _ ofs8 _)
  else Error (msg "impossible").

Definition decode_ofs_u8 (bs:u8) : res int :=
  let bs' := proj1_sig bs in
  let z := bits_to_Z bs' in
  OK (Int.repr z).

Program Definition encode_ofs_u16 (ofs:Z) :res u16 :=
  let ofs16 := bytes_to_bits_opt (bytes_of_int 4 ofs) in
  if assertLength ofs16 16 then
    OK (exist _ ofs16 _)
  else Error (msg "impossible").

Definition decode_ofs_u16 (bs:u16) : res int :=
  let bs' := proj1_sig bs in
  let z := bits_to_Z bs' in
  OK(Int.repr z).

Program Definition encode_ofs_u32 (ofs:Z) :res u32 :=
  let ofs32 := bytes_to_bits_opt (bytes_of_int 4 ofs) in
  if assertLength ofs32 32 then
    OK (exist _ ofs32 _)
  else Error (msg "impossible").

Definition decode_ofs_u32 (bs:u32) : res int :=
  let bs' := proj1_sig bs in
  let z := bits_to_Z bs' in
  OK (Int.repr z).

Program Definition encode_testcond_u4 (c:testcond) : u4 :=
  match c with
  | Cond_e   => b["0100"]   (**r 4 *)
  | Cond_ne  => b["0101"]   (**r 5 *)
  | Cond_b   => b["0010"]   (**r 2 *)
  | Cond_be  => b["0110"]   (**r 6 *)
  | Cond_ae  => b["0011"]   (**r 3 *)
  | Cond_a   => b["0111"]   (**r 7 *)
  | Cond_l   => b["1100"]   (**r C *)
  | Cond_le  => b["1110"]   (**r E *)
  | Cond_ge  => b["1101"]   (**r D *)
  | Cond_g   => b["1111"]   (**r F *)
  | Cond_p   => b["1010"]   (**r A *)
  | Cond_np  => b["1011"]   (**r B *)
  end.

Definition decode_testcond_u4 (bs:u4) : res testcond :=
  let bs' := proj1_sig bs in
  let n := bits_to_Z bs' in
  if Z.eqb n 4 then OK(Cond_e)            (**r 4 b["0100"] *)
  else if Z.eqb n 5  then OK(Cond_ne)     (**r 5 b["0101"] *)
  else if Z.eqb n 2  then OK(Cond_b)      (**r 2 b["0010"] *)
  else if Z.eqb n 6  then OK(Cond_be)     (**r 6 b["0110"] *)
  else if Z.eqb n 3  then OK(Cond_ae)     (**r 3 b["0011"] *)
  else if Z.eqb n 7  then OK(Cond_a)      (**r 7 b["0111"] *)
  else if Z.eqb n 12 then OK(Cond_l)      (**r C b["1100"] *)
  else if Z.eqb n 14 then OK(Cond_le)     (**r E b["1110"] *)
  else if Z.eqb n 13 then OK(Cond_ge)     (**r D b["1101"] *)
  else if Z.eqb n 15 then OK(Cond_g)      (**r F b["1111"] *)
  else if Z.eqb n 10 then OK(Cond_p)      (**r A b["1010"] *)
  else if Z.eqb n 11 then OK(Cond_np)     (**r B b["1011"] *)
  else Error(msg "reg not found")
.

Lemma testcond_encode_consistency : forall c bs,
  encode_testcond_u4 c = bs ->
  decode_testcond_u4 bs = OK(c).
Proof.
  (**r enumerate all possibility of c *)
  destruct c;
  simpl; unfold char_to_bool; simpl;
  intros; subst;
  unfold decode_testcond_u4; simpl;
  auto.
Qed.

Lemma testcond_decode_consistency : forall c bs,
  decode_testcond_u4 bs = OK(c) ->
  encode_testcond_u4 c = bs.
Proof.
  intros.
  destruct bs as [b Hlen].
  (** extract three bits from b *)
  destruct b as [| b0 b]; try discriminate; inversion Hlen. (**r the 1st one *)
  destruct b as [| b1 b]; try discriminate; inversion Hlen. (**r the 2nd one *)
  destruct b as [| b2 b]; try discriminate; inversion Hlen. (**r the 3rd one *)
  destruct b as [| b3 b]; try discriminate; inversion Hlen. (**r the 4th one *)
  destruct b; try discriminate.                             (**r b is a empty list now, eliminate other possibility *)
  (** case analysis on [b0, b1, b2] *)
  destruct b0, b1, b2, b3 eqn:Eb;
  unfold decode_testcond_u4 in H; simpl in H; (**r extract decoded result r from H *)
  inversion H; subst;                         (**r subst r *)
  unfold encode_testcond_u4; simpl;           (**r calculate encode_testcond_u4 *)
  cbv delta in *;
  unfold char_to_bool; simpl;
  replace eq_refl with Hlen;
  try reflexivity;                            (**r to solve OK(exsit _ _ Hlen) = OK(exsit _ _ Hlen) *)
  try apply proof_irr.                        (**r to solve e = eq_refl *)
Qed.

Definition Instr_reloc_offset (i:Instruction): res Z := Error (msg "unfinished").

Section WITH_RELOC_OFS_MAP.

Variable rtbl_ofs_map: reloc_ofs_map_type.


Definition get_reloc_addend (ofs:Z) : res Z :=
  match ZTree.get ofs rtbl_ofs_map with
  | None => Error [MSG "Cannot find the relocation entry at the offset "; POS (Z.to_pos ofs)]
  | Some e => OK (reloc_addend e)
  end.

Definition get_instr_reloc_addend (ofs:Z) (i:instruction) : res Z :=
  do iofs <- instr_reloc_offset i;
  get_reloc_addend (ofs + iofs).


Definition get_instr_reloc_addend' (ofs:Z): res Z :=
  get_reloc_addend ofs.


(* Translate ccelf addressing mode to cav21 addr mode *)
(* sofs: instruction ofs, res_iofs: relocated location in the instruction*)
(* TODO: 64bit mode, the addend is placed in the relocation entry *)
Definition translate_Addrmode_AddrE (sofs: Z) (res_iofs: res Z) (addr:addrmode): res AddrE :=
  match addr with
  | Addrmode obase oindex disp  =>
    match disp with
    | inr (id, ofs) =>
      match id with
      | xH =>
        do iofs <- res_iofs;
        do addend <- get_instr_reloc_addend' (iofs + sofs);
        if Z.eqb (Ptrofs.unsigned ofs) addend then
          (*32bit mode the addend placed in instruction *)
          do imm32 <- encode_ofs_u32 addend;
          match obase,oindex with
          | None,None =>
            OK (AddrE11 imm32)
          | Some base,None =>
            (* some bug only fix here not fixed in reverse *)
            do r <- encode_ireg_u3 base;
            if ireg_eq base RSP then
              OK (AddrE4 r imm32)
            else
              OK (AddrE6 r imm32)
          | None,Some (idx,ss) =>
            do index <- encode_ireg_u3 idx;
            do scale <- encode_scale_u2 ss;
            if ireg_eq idx RSP then
              (* OK (AddrE7 zero32) *)
              Error (msg "index can not be RSP")
            else
              OK (AddrE9 scale index imm32)
          | Some base,Some (idx,ss) =>
            do scale <- encode_scale_u2 ss;
            do index <- encode_ireg_u3 idx;
            do breg <- encode_ireg_u3 base;
            if ireg_eq idx RSP then
              Error (msg "index can not be RSP")
                    (* OK (AddrE4 breg zero32)            *)
            else
              OK (AddrE5 scale index breg imm32)
          end
        else Error (msg "addend is not equal to ofs")
      | _ => Error(msg "id must be 1")
      end
    | inl ofs =>
      do iofs <- res_iofs;
      match ZTree.get (iofs + sofs)%Z rtbl_ofs_map with
      | None =>
        do ofs32 <- encode_ofs_u32 ofs;
        match obase,oindex with
        | None,None =>
          OK (AddrE11 ofs32)
        | Some base,None =>
          do r <- encode_ireg_u3 base;
          if ireg_eq base RSP then
              OK (AddrE4 r ofs32)
          else
              OK (AddrE6 r ofs32)
        | None,Some (idx,ss) =>
          do r <- encode_ireg_u3 idx;
          do scale <- encode_scale_u2 ss;
          if ireg_eq idx RSP then
            (* OK (AddrE7 ofs32) *)
            Error (msg "index can not be RSP")
          else
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

(* FIXME: some bug fixed in above but not here *)
(* Translate CAV21 addr mode to ccelf addr mode *)
Definition translate_AddrE_Addrmode (sofs: Z) (res_iofs : res Z) (addr:AddrE) : res addrmode :=
  (* need to relocate? *)
  do iofs <- res_iofs;
  match ZTree.get (iofs + sofs)%Z rtbl_ofs_map with
  | None =>
    match addr with
    | AddrE11 disp =>
      OK (Addrmode None None (inl (bits_to_Z (proj1_sig disp))))
    | AddrE9 ss idx disp =>
      do index <- decode_ireg idx;
      if ireg_eq index RSP then
        Error (msg "index can not be RSP")
      else
        OK (Addrmode None (Some (index,(bits_to_Z (proj1_sig ss)))) (inl (bits_to_Z (proj1_sig disp))) )
    | AddrE6 base disp =>
      do b <- decode_ireg base;
      OK (Addrmode (Some b) None (inl (bits_to_Z (proj1_sig disp))) )
    (* | AddrE4 base disp => *)
    (*   do b <- decode_ireg (proj1_sig base); *)
    (*   OK (Addr) *)
    | AddrE5 ss idx base disp =>
      do index <- decode_ireg idx;
      do b <- decode_ireg base;
      if ireg_eq index RSP then
        Error (msg "index can not be RSP")
      else OK (Addrmode (Some b) (Some (index,(bits_to_Z (proj1_sig ss)))) (inl (bits_to_Z (proj1_sig disp))) )
    | _ => Error (msg "unsupported or impossible")
    end
  | Some _ =>
    do addend <- get_instr_reloc_addend' (* rtbl_ofs_map *) (iofs + sofs);
    match addr with
    | AddrE11 _ =>
      OK (Addrmode None None (inr (xH,Ptrofs.repr addend)))
    | AddrE9 ss idx disp =>
      do index <- decode_ireg idx;
      OK (Addrmode None (Some (index,(bits_to_Z (proj1_sig ss)))) (inr (xH,Ptrofs.repr addend)) )
    | AddrE6 base disp =>
      do b <- decode_ireg base;
      OK (Addrmode (Some b) None (inr (xH,Ptrofs.repr addend)))
    (* | AddrE4 base disp => *)
    (*   do b <- decode_ireg (proj1_sig base); *)
    (*   OK (Addr) *)
    | AddrE5 ss idx base disp =>
      do index <- decode_ireg idx;
      do b <- decode_ireg base;
      if ireg_eq index RSP then
        Error (msg "index can not be RSP")
      else OK (Addrmode (Some b) (Some (index,(bits_to_Z (proj1_sig ss)))) (inr (xH,Ptrofs.repr addend)) )
    | _ => Error (msg "unsupported or impossible")
    end
  end.

(* 64bit addrmode translation *)
(* TODO *)

(* consistency proof *)
Lemma translate_consistency1 : forall ofs iofs addr addrE,
    translate_Addrmode_AddrE ofs iofs addr = OK addrE ->
    translate_AddrE_Addrmode ofs iofs addrE = OK addr.
  intros. destruct addr.
  unfold translate_Addrmode_AddrE in H.
  unfold translate_AddrE_Addrmode.
  (* destruct base;destruct (ZTree.get);try destruct p;destruct const;try congruence. *)
  (* - monadInv H. *)
  (*   rewrite EQ. *)
  (*   cbn [bind].     *)
  (*   destruct (ZTree.get (x + ofs)%Z rtbl_ofs_map);try congruence. *)
  (*   monadInv EQ0. *)
  (*   destruct (ireg_eq i1 RSP);try congruence. *)
  (*   monadInv EQ5. *)
Admitted.



(*encode 64bit reg ,return *)
Definition encode_ireg64 (r:ireg) :(bits*bits):=
  match r with
  | RAX =>  (b["0"],b[ "000"])
  | RBX =>  (b["0"],b[ "011"])
  | RCX =>  (b["0"],b[ "001"])
  | RDX =>  (b["0"],b[ "010"])
  | RSI =>  (b["0"],b[ "110"])
  | RDI =>  (b["0"],b[ "111"])
  | RBP =>  (b["0"],b[ "101"])
  | RSP =>  (b["0"],b[ "100"])
  | R8 => (b["1"],b["000"])
  | R9 => (b["1"],b["001"])
  | R10 =>  (b["1"],b["010"])
  | R11 =>  (b["1"],b["011"])
  | R12 =>  (b["1"],b["100"])
  | R13 =>  (b["1"],b["101"])
  | R14 => (b["1"],b["110"])
  | R15 => (b["1"],b["111"])
end.

Program Definition encode_ireg_u4 (r:ireg) : res (u1*u3):=
  let (R,b) := encode_ireg64 r in
  if assertLength R 1 then
    if assertLength b 3 then
      OK (R,b)
    else Error(msg"impossible")
  else Error(msg"impossible").

(* FIXME *)
Program Definition encode_ofs_u64 (ofs:Z) : res u64 :=
  let ofs64 := bytes_to_bits_opt (bytes_of_int 8 ofs) in
  if assertLength ofs64 64 then
    OK (exist _ ofs64 _)
  else Error (msg "impossible").
    

(* ccelf instruction to cav21 instruction, unfinished!!! *)
Definition translate_instr (ofs: Z) (i:instruction) : res Instruction :=
  let res_iofs := instr_reloc_offset i in
  let translate_Addrmode_AddrE := translate_Addrmode_AddrE ofs res_iofs in
  match i with
  | Pmov_rr rd r1 =>
    do rdbits <- encode_ireg_u3 rd;
    do r1bits <- encode_ireg_u3 r1;
    OK (Pmovl_mr (AddrE0 rdbits) r1bits) 
  | Asm.Pmovl_rm rd addr =>
    do rdbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovl_rm a rdbits)
  | Asm.Pmovl_ri rd imm =>
    do rdbits <- encode_ireg_u3 rd;
    do imm32 <- encode_ofs_u32 (Int.intval imm);
    OK (Pmovl_ri rdbits imm32)
  | Asm.Pmovl_mr addr r =>
    do rbits <- encode_ireg_u3 r;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovl_mr a rbits)
  | Asm.Pmovsd_ff rd r1 =>
    do rdbits <- encode_freg_u3 rd;
    do r1bits <- encode_freg_u3 r1;
    OK (Pmovsd_fm (AddrE0 rdbits) r1bits)
  | Asm.Pmovsd_fm r addr =>
    do rbits <- encode_freg_u3 r;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovsd_fm a rbits)
  | Asm.Pmovsd_mf addr r =>
    do rbits <- encode_freg_u3 r;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovsd_mf a rbits)
  | Asm.Pmovss_fm r addr =>
    do rbits <- encode_freg_u3 r;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovss_fm a rbits)
  | Asm.Pmovss_mf addr r =>
    do rbits <- encode_freg_u3 r;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovss_mf a rbits)
  | Asm.Pfldl_m addr =>
    do a <- translate_Addrmode_AddrE addr;
    OK (Pfldl_m a)
  | Asm.Pfstpl_m addr =>
    do a <- translate_Addrmode_AddrE addr;
    OK (Pfstpl_m a)
  | Asm.Pflds_m addr =>
    do a <- translate_Addrmode_AddrE addr;
    OK (Pflds_m a)
  | Asm.Pfstps_m addr =>
    do a <- translate_Addrmode_AddrE addr;
    OK (Pfstps_m a)
  | Asm.Pmovb_mr addr r =>
    do a <- translate_Addrmode_AddrE addr;
    do rbits <- encode_ireg_u3 r;
    OK (Pmovb_mr a rbits)
  | Asm.Pmovw_mr addr r =>
    do a <- translate_Addrmode_AddrE addr;
    do rbits <- encode_ireg_u3 r;
    OK (Pmovw_mr a rbits)
  | Asm.Pmovzb_rr rd r =>
    do rdbits <- encode_ireg_u3 rd;
    do rbits <- encode_ireg_u3 r;
    OK (Pmovzb_rm (AddrE0 rdbits) rbits)
  | Asm.Pmovzb_rm r addr =>
    do rbits <- encode_ireg_u3 r;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovzb_rm a rbits)
  (*from there*)
  | Asm.Pmovzw_rm rd addr =>
    do rbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovzw_GvEv a rbits)
  | Asm.Pmovzw_rr rd rs =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 rs;
     OK (Pmovzw_GvEv (AddrE0 rdbits) rbits)
  | Asm.Pmovsb_rm rd addr =>
    do rbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovsb_GvEv a rbits)
  | Asm.Pmovsb_rr rd rs =>
    do rdbits <- encode_ireg_u3 rd;
    do rbits <- encode_ireg_u3 rs;
    OK (Pmovsb_GvEv (AddrE0 rdbits) rbits)
  | Asm.Pmovw_rm rd addr =>
    do rbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovw_rm a rbits)
  | Asm.Pmovb_rm rd addr =>
    do rdbits <- encode_ireg_u3 rd;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pmovb_rm a rdbits)
  | Asm.Pmovsw_rm rd addr =>
     do rdbits <- encode_ireg_u3 rd;
     do a <- translate_Addrmode_AddrE addr;
     OK (Pmovsw_GvEv a rdbits)
  | Asm.Pmovsw_rr rd rs =>
    do rdbits <- encode_ireg_u3 rd;
    do rbits <- encode_ireg_u3 rs;
    OK (Pmovsw_GvEv (AddrE0 rdbits) rbits)
  | Asm.Pnegl r =>
     do rbits <- encode_ireg_u3 r;
     OK (Pnegl rbits)
  | Asm.Pleal r addr =>
     do rbits <- encode_ireg_u3 r;
     do a <- translate_Addrmode_AddrE addr;
     OK (Pleal a rbits)
  | Asm.Pcvttss2si_rf rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pcvttss2si_rf rdbits rbits)
  | Asm.Pcvtsi2sd_fr rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pcvtsi2sd_fr rdbits rbits)
  | Asm.Pcvtsi2ss_fr rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pcvtsi2ss_fr rdbits rbits)
  | Asm.Pcvttsd2si_rf rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pcvttsd2si_rf rdbits rbits)
  | Asm.Pcvtss2sd_ff rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pcvtss2sd_ff rdbits rbits)
  | Asm.Pcvtsd2ss_ff rd r1=>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pcvtsd2ss_ff rdbits rbits)
  | Asm.Paddl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Paddl_ri rdbits imm32)
  | Asm.Psubl_rr rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Psubl_rr rdbits rbits)
  | Asm.Pimull_rr rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pimull_rr rdbits rbits)
  | Asm.Pimull_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Pimull_ri rdbits rdbits imm32)
  | Asm.Pmull_r r1 =>
     do rbits <- encode_ireg_u3 r1;
     OK (Pmull_r rbits)
  | Asm.Pcltd => OK (Pcltd)
  | Asm.Pdivl r1 =>
     do rbits <- encode_ireg_u3 r1;
     OK (Pdivl_r rbits)
  | Asm.Pidivl r1 =>
     do rbits <- encode_ireg_u3 r1;
     OK (Pidivl_r rbits)
  | Asm.Pandl_rr rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pandl_rr rdbits rbits)
  | Asm.Pandl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Pandl_ri rdbits imm32)
  | Asm.Porl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Porl_ri rdbits imm32)
  | Asm.Porl_rr rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Porl_rr rdbits rbits)
  | Asm.Pxorl_rr rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pxorl_rr rdbits rbits)
  | Asm.Pxorl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Pxorl_ri rdbits imm32)
  | Asm.Pnotl rd =>
     do rdbits <- encode_ireg_u3 rd;
     OK (Pnotl rdbits)
  | Asm.Psall_ri rd imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 (Int.intval imm);
     OK (Psall_ri rdbits imm8)
  | Asm.Psall_rcl rd =>
     do rdbits <- encode_ireg_u3 rd;
     OK (Psall_rcl rdbits)
  | Asm.Pshrl_ri rd imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 (Int.intval imm);
     OK (Pshrl_ri rdbits imm8)
  | Asm.Psarl_ri rd imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 (Int.intval imm);
     OK (Psarl_ri rdbits imm8)
  | Asm.Psarl_rcl rd =>
     do rdbits <- encode_ireg_u3 rd;
     OK (Psarl_rcl rdbits)
  | Asm.Pshld_ri rd r1 imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     do imm8 <- encode_ofs_u8 (Int.intval imm);
     OK (Pshld_ri rdbits rbits imm8)
  | Asm.Prolw_ri rd imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 (Int.intval imm);
     OK (Prolw_ri rdbits imm8)
  | Asm.Prorl_ri rd imm =>(*define a new function*)
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 (Int.intval imm);
     OK (Prorl_ri rdbits imm8)
  | Asm.Pcmpl_rr r1 r2 =>
     do rdbits <- encode_ireg_u3 r1;
     do rbits <- encode_ireg_u3 r2;
     OK (Pcmpl_rr rdbits rbits)
  | Asm.Pcmpl_ri r1 imm =>
     do rdbits <- encode_ireg_u3 r1;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Pcmpl_ri rdbits imm32)
  | Asm.Ptestl_ri r1 imm =>
     do rdbits <- encode_ireg_u3 r1;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Ptestl_ri rdbits imm32)
  | Asm.Ptestl_rr r1 r2 =>
     do rdbits <- encode_ireg_u3 r1;
     do rbits <- encode_ireg_u3 r2;
     OK (Ptestl_rr rdbits rbits)
  | Asm.Pcmov c rd r1 =>(*define a new function*)
     let cond := encode_testcond_u4 c in
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pcmov cond rdbits rbits)
  | Asm.Psetcc c rd =>
     let cond := encode_testcond_u4 c in 
     do rdbits <- encode_ireg_u3 rd;
     OK (Psetcc cond rdbits)
  | Asm.Paddd_ff rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Paddd_ff rdbits rbits)
  | Asm.Psubd_ff rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Psubd_ff rdbits rbits)
  | Asm.Pmuld_ff rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pmuld_ff rdbits rbits)
  | Asm.Pcomisd_ff r1 r2 =>
     do rdbits <- encode_freg_u3 r1;
     do rbits <- encode_freg_u3 r2;
     OK (Pcomisd_ff rdbits rbits)
  | Asm.Pxorps_f rd =>
     do rdbits <- encode_freg_u3 rd;
     OK (Pxorps_GvEv (AddrE0 rdbits) rdbits)
  | Asm.Pxorps_fm frd addr =>
     do rdbits <- encode_freg_u3 frd;
     do a <- translate_Addrmode_AddrE addr;
     OK (Pxorps_GvEv a rdbits)
  | Asm.Pandps_fm frd addr =>
     do rdbits <- encode_freg_u3 frd;
     do a <- translate_Addrmode_AddrE addr;
     OK (Pandps_fm a rdbits)
  | Asm.Pjmp_l_rel ofs =>(*admitttttttttttttttttttttted*)
     do imm <- encode_ofs_u32 ofs;
     OK (Pjmp_l_rel imm)
  | Asm.Pjmp_r r sg =>(*admitttttttttttttttttttttted*)
     do rdbits <- encode_ireg_u3 r;
     (*how to use sg*)
     OK (Pjmp_Ev (AddrE0 rdbits))
  | Asm.Pjmp_m addr =>
     do a <- translate_Addrmode_AddrE addr;
     OK (Pjmp_Ev a)
  | Asm.Pnop | Asm.Plabel _ =>
     OK (Pnop)
  | Asm.Pcall_r r sg => (*how to use sg*)
     do rdbits <- encode_ireg_u3 r;
     OK (Pcall_r rdbits)
  | Asm.Pcall_s id sg =>
    match id with
    | xH =>
      do iofs <- res_iofs;
      do addend <- get_instr_reloc_addend' (iofs + ofs);
      (* FIXME: different in 64bit mode? *)
      (* CSLED: need 64bit call instruction *)
      do imm32 <- encode_ofs_u32 addend;
      OK (Pcall_ofs imm32)
    | _ =>
      Error [MSG "id must be 1: Pcall_s"]
    end
  | Asm.Pret => OK(Pret)
  | Asm.Pret_iw imm => (*define encode_ofs_u16*)
     do imm16 <- encode_ofs_u16 (Int.intval imm);
     OK (Pret_iw imm16)
  | Asm.Pjcc_rel c ofs =>
     let cond := encode_testcond_u4 c in
     do imm <- encode_ofs_u32 ofs;
     OK (Pjcc_rel cond imm)
  | Asm.Padcl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm8 <- encode_ofs_u8 (Int.intval imm);
     OK (Padcl_ri rdbits imm8)
  | Asm.Padcl_rr rd r2 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r2;
     OK (Padcl_rr rdbits rbits)
  | Asm.Paddl_rr rd r2 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r2;
     OK (Paddl_rr rdbits rbits)
  | Asm.Paddl_mi addr imm =>
     do a <- translate_Addrmode_AddrE addr;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Paddl_mi a imm32)
  | Asm.Pbsfl rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pbsfl rdbits rbits)
  | Asm.Pbsrl rd r1 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r1;
     OK (Pbsrl rdbits rbits)
  | Asm.Pbswap32 rd =>
     do rdbits <- encode_ireg_u3 rd;
     OK (Pbswap32 rdbits)
  | Asm.Pmaxsd rd r2 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r2;
     OK (Pmaxsd rdbits rbits)
  | Asm.Pminsd rd r2 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r2;
     OK (Pminsd rdbits rbits)
  | Asm.Pmovsq_mr addr rs =>
     do a <- translate_Addrmode_AddrE addr;
     do rbits <- encode_freg_u3 rs;
     OK (Pmovsq_mr a rbits)
  | Asm.Pmovsq_rm rd addr =>
     do rdbits <- encode_freg_u3 rd;
     do a <- translate_Addrmode_AddrE addr;
     OK (Pmovsq_mr a rdbits)
  | Asm.Prep_movsl => OK(Prep_movsl)
  | Asm.Psbbl_rr  rd r2 =>
     do rdbits <- encode_ireg_u3 rd;
     do rbits <- encode_ireg_u3 r2;
     OK (Psbbl_rr rdbits rbits)
  | Asm.Psqrtsd rd r1 =>
     do rdbits <- encode_freg_u3 rd;
     do rbits <- encode_freg_u3 r1;
     OK (Pbsqrtsd rdbits rbits)
  | Asm.Psubl_ri rd imm =>
     do rdbits <- encode_ireg_u3 rd;
     do imm32 <- encode_ofs_u32 (Int.intval imm);
     OK (Psubl_ri rdbits imm32)
  | Asm.Pmov_mr_a addr rs =>
    do a <- translate_Addrmode_AddrE addr;
    do rbits <- encode_ireg_u3 rs;
    OK (Pmovl_rm a rbits)
  | Asm.Pmov_rm_a rs addr =>
    do a <- translate_Addrmode_AddrE addr;
    do rbits <- encode_ireg_u3 rs;
    OK (Pmovl_rm a rbits)
  | Asm.Pmovsd_mf_a addr rs =>
    do a <- translate_Addrmode_AddrE addr;
    do rbits <- encode_freg_u3 rs;
    OK (Pmovsd_mf a rbits)
  | Asm.Pmovsd_fm_a rs addr =>
    do a <- translate_Addrmode_AddrE addr;
    do rbits <- encode_freg_u3 rs;
    OK (Pmovsd_fm a rbits)  
  | Asm.Pxorl_r r =>
    do rbits <- encode_ireg_u3 r;
    OK (Pxorl_rr rbits rbits)
  | Asm.Pxorpd_f r =>
    do rbits <- encode_freg_u3 r;
    OK (Pxorpd_GvEv (AddrE0 rbits) rbits)
  | Asm.Pdivd_ff rd rs =>
    do rdbits <- encode_freg_u3 rd;
    do rbits <- encode_freg_u3 rs;
    OK (Pdivsd_ff rdbits rbits)
  | Asm.Pdivs_ff rd rs =>
    do rdbits <- encode_freg_u3 rd;
    do rbits <- encode_freg_u3 rs;
    OK (Pdivss_ff rdbits rbits)
  | Asm.Pxorpd_fm rd addr =>
    do rdbits <- encode_freg_u3 rd;
    do a <- translate_Addrmode_AddrE addr;
    OK (Pxorpd_GvEv a rdbits) 
  (* (* 64bit *) *)
  (* | Asm.Pmovq_ri rd imm => *)
  (*   do Rrdbits <- encode_ireg_u4 rd; *)
  (*   let (R,rdbits) := Rrdbits in *)
  (*   do imm64 <- encode_ofs_u64 (Int64.intval imm); *)
  (*   OK (Pmovq_ri R rdbits imm64)        *)
  (* | Asm.Pmovq_rm rd addr => *)
    
  | _ => Error [MSG "Not exists "; MSG (instr_to_string i)]
              
  end.

End WITH_RELOC_OFS_MAP.

Require Import Smallstep.
Require Import Machregs.
Require Import Asm.
Require Import Integers.
Require Import Floats.
Require Import List.
Require Import ZArith.
Require Import Memtype.
Require Import Memory.
Require Import Archi.
Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Values.
Require Import Conventions1.
Require Import SSAsm AsmFacts AsmRegs.

(** * Operational Semantics with instr_size *)
Section INSTRSIZE.
Variable instr_size : instruction -> Z.

Fixpoint code_size (c:code) : Z :=
  match c with
  |nil => 0
  |i::c' => code_size c' + instr_size i
  end.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - instr_size i) il
  end.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
    let nextpos := pos + instr_size instr in
      if is_label lbl instr then Some nextpos else label_pos lbl nextpos c'
  end.

Section WITHGE.
  Variable ge : Genv.t Asm.fundef unit.

Definition nextinstr (rs: regset) (sz:ptrofs) :=
  rs#PC <- (Val.offset_ptr rs#PC sz).

Definition nextinstr_nf (rs: regset) (sz:ptrofs) : regset :=
  nextinstr (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs) sz.

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs =>
        match Genv.find_funct_ptr ge b with
        | Some _ => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
        | None => Stuck
        end
      | _ => Stuck
    end
  end.

(** Auxiliaries for memory accesses. *)

Definition exec_load (chunk: memory_chunk) (m: mem)
                     (a: addrmode) (rs: regset) (rd: preg) (sz:ptrofs):=
  match Mem.loadv chunk m (eval_addrmode ge a rs) with
  | Some v => Next (nextinstr_nf (rs#rd <- v) sz) m
  | None => Stuck
  end.

Definition exec_store (chunk: memory_chunk) (m: mem)
                      (a: addrmode) (rs: regset) (r1: preg)
                      (destroyed: list preg) (sz:ptrofs) :=
  match Mem.storev chunk m (eval_addrmode ge a rs) (rs r1) with
  | Some m' => Next (nextinstr_nf (undef_regs destroyed rs) sz) m'
  | None => Stuck
  end.

Definition exec_instr_asm (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  let sz := Ptrofs.repr (instr_size i) in
  match i with
  (** Moves *)
  | Pmov_rr rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1)) sz) m
  | Pmovl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vint n)) sz) m
  | Pmovq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vlong n)) sz) m
  | Pmov_rs rd id =>
      Next (nextinstr_nf (rs#rd <- (Genv.symbol_address ge id Ptrofs.zero)) sz) m
  | Pmovl_rm rd a =>
      exec_load Mint32 m a rs rd sz
  | Pmovq_rm rd a =>
      exec_load Mint64 m a rs rd sz
  | Pmovl_mr a r1 =>
      exec_store Mint32 m a rs r1 nil sz
  | Pmovq_mr a r1 =>
      exec_store Mint64 m a rs r1 nil sz
  | Pmovsd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1)) sz) m
  | Pmovsd_fi rd n =>
      Next (nextinstr (rs#rd <- (Vfloat n)) sz) m
  | Pmovsd_fm rd a =>
      exec_load Mfloat64 m a rs rd sz
  | Pmovsd_mf a r1 =>
      exec_store Mfloat64 m a rs r1 nil sz
  | Pmovss_fi rd n =>
      Next (nextinstr (rs#rd <- (Vsingle n)) sz) m
  | Pmovss_fm rd a =>
      exec_load Mfloat32 m a rs rd sz
  | Pmovss_mf a r1 =>
      exec_store Mfloat32 m a rs r1 nil sz
  | Pfldl_m a =>
      exec_load Mfloat64 m a rs ST0 sz
  | Pfstpl_m a =>
      exec_store Mfloat64 m a rs ST0 (ST0 :: nil) sz
  | Pflds_m a =>
      exec_load Mfloat32 m a rs ST0 sz
  | Pfstps_m a =>
      exec_store Mfloat32 m a rs ST0 (ST0 :: nil) sz
  (** Moves with conversion *)
  | Pmovb_mr a r1 =>
      exec_store Mint8unsigned m a rs r1 nil sz
  | Pmovw_mr a r1 =>
      exec_store Mint16unsigned m a rs r1 nil sz
  | Pmovzb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1)) sz) m
  | Pmovzb_rm rd a =>
      exec_load Mint8unsigned m a rs rd sz
  | Pmovsb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1)) sz) m
  | Pmovsb_rm rd a =>
      exec_load Mint8signed m a rs rd sz
  | Pmovzw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1)) sz) m
  | Pmovzw_rm rd a =>
      exec_load Mint16unsigned m a rs rd sz
  | Pmovsw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1)) sz) m
  | Pmovsw_rm rd a =>
      exec_load Mint16signed m a rs rd sz
  | Pmovzl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofintu rs#r1)) sz) m
  | Pmovsl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofint rs#r1)) sz) m
  | Pmovls_rr rd =>
      Next (nextinstr (rs#rd <- (Val.loword rs#rd)) sz) m
  | Pcvtsd2ss_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1)) sz) m
  | Pcvtss2sd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.floatofsingle rs#r1)) sz) m
  | Pcvttsd2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intoffloat rs#r1))) sz) m
  | Pcvtsi2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatofint rs#r1))) sz) m
  | Pcvttss2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intofsingle rs#r1))) sz) m
  | Pcvtsi2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofint rs#r1))) sz) m
  | Pcvttsd2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longoffloat rs#r1))) sz) m
  | Pcvtsl2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatoflong rs#r1))) sz) m
  | Pcvttss2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longofsingle rs#r1))) sz) m
  | Pcvtsl2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleoflong rs#r1))) sz) m
  (** Integer arithmetic *)
  | Pleal rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode32 ge a rs)) sz) m
  | Pleaq rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode64 ge a rs)) sz) m
  | Pnegl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.neg rs#rd)) sz) m
  | Pnegq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.negl rs#rd)) sz) m
  | Paddl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.add rs#rd (Vint n))) sz) m
  | Paddq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.addl rs#rd (Vlong n))) sz) m
  | Psubl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1)) sz) m
  | Psubq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.subl rs#rd rs#r1)) sz) m
  | Pimull_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd rs#r1)) sz) m
  | Pimulq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd rs#r1)) sz) m
  | Pimull_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd (Vint n))) sz) m
  | Pimulq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd (Vlong n))) sz) m
  | Pimull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhs rs#RAX rs#r1)) sz) m
  | Pimulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhs rs#RAX rs#r1)) sz) m
  | Pmull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhu rs#RAX rs#r1)) sz) m
  | Pmulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhu rs#RAX rs#r1)) sz) m
  | Pcltd =>
      Next (nextinstr_nf (rs#RDX <- (Val.shr rs#RAX (Vint (Int.repr 31)))) sz) m
  | Pcqto =>
      Next (nextinstr_nf (rs#RDX <- (Val.shrl rs#RAX (Vint (Int.repr 63)))) sz) m
  | Pdivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r)) sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pdivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r)) sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r)) sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r)) sz) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pandl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd rs#r1)) sz) m
  | Pandq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd rs#r1)) sz) m
  | Pandl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd (Vint n))) sz) m
  | Pandq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd (Vlong n))) sz) m
  | Porl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd rs#r1)) sz) m
  | Porq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd rs#r1)) sz) m
  | Porl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd (Vint n))) sz) m
  | Porq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd (Vlong n))) sz) m
  | Pxorl_r rd =>
      Next (nextinstr_nf (rs#rd <- Vzero) sz) m
  | Pxorq_r rd =>
      Next (nextinstr_nf (rs#rd <- (Vlong Int64.zero)) sz) m
  | Pxorl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd rs#r1)) sz) m
  | Pxorq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd rs#r1)) sz) m
  | Pxorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd (Vint n))) sz) m
  | Pxorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd (Vlong n))) sz) m
  | Pnotl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notint rs#rd)) sz) m
  | Pnotq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notl rs#rd)) sz) m
  | Psall_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd rs#RCX)) sz) m
  | Psalq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd rs#RCX)) sz) m
  | Psall_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd (Vint n))) sz) m
  | Psalq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd (Vint n))) sz) m
  | Pshrl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd rs#RCX)) sz) m
  | Pshrq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd rs#RCX)) sz) m
  | Pshrl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd (Vint n))) sz) m
  | Pshrq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd (Vint n))) sz) m
  | Psarl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd rs#RCX)) sz) m
  | Psarq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd rs#RCX)) sz) m
  | Psarl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd (Vint n))) sz) m
  | Psarq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd (Vint n))) sz) m
  | Pshld_ri rd r1 n =>
      Next (nextinstr_nf
              (rs#rd <- (Val.or (Val.shl rs#rd (Vint n))
                                (Val.shru rs#r1 (Vint (Int.sub Int.iwordsize n))))) sz) m
  | Prorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.ror rs#rd (Vint n))) sz) m
  | Prorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.rorl rs#rd (Vint n))) sz) m
  | Pcmpl_rr r1 r2 =>
      Next (nextinstr (compare_ints (rs r1) (rs r2) rs m) sz) m
  | Pcmpq_rr r1 r2 =>
      Next (nextinstr (compare_longs (rs r1) (rs r2) rs m) sz) m
  | Pcmpl_ri r1 n =>
      Next (nextinstr (compare_ints (rs r1) (Vint n) rs m) sz) m
  | Pcmpq_ri r1 n =>
      Next (nextinstr (compare_longs (rs r1) (Vlong n) rs m) sz) m
  | Ptestl_rr r1 r2 =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (rs r2)) Vzero rs m) sz) m
  | Ptestq_rr r1 r2 =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (rs r2)) (Vlong Int64.zero) rs m) sz) m
  | Ptestl_ri r1 n =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (Vint n)) Vzero rs m) sz) m
  | Ptestq_ri r1 n =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (Vlong n)) (Vlong Int64.zero) rs m) sz) m
  | Pcmov c rd r1 =>
      let v :=
        match eval_testcond c rs with
        | Some b => if b then rs#r1 else rs#rd
        | None   => Vundef
      end in
      Next (nextinstr (rs#rd <- v) sz) m
  | Psetcc c rd =>
      Next (nextinstr (rs#rd <- (Val.of_optbool (eval_testcond c rs))) sz) m
  (** Arithmetic operations over double-precision floats *)
  | Paddd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addf rs#rd rs#r1)) sz) m
  | Psubd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subf rs#rd rs#r1)) sz) m
  | Pmuld_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulf rs#rd rs#r1)) sz) m
  | Pdivd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divf rs#rd rs#r1)) sz) m
  | Pnegd rd =>
      Next (nextinstr (rs#rd <- (Val.negf rs#rd)) sz) m
  | Pabsd rd =>
      Next (nextinstr (rs#rd <- (Val.absf rs#rd)) sz) m
  | Pcomisd_ff r1 r2 =>
      Next (nextinstr (compare_floats (rs r1) (rs r2) rs) sz) m
  | Pxorpd_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vfloat Float.zero)) sz) m
  (** Arithmetic operations over single-precision floats *)
  | Padds_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addfs rs#rd rs#r1)) sz) m
  | Psubs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subfs rs#rd rs#r1)) sz) m
  | Pmuls_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulfs rs#rd rs#r1)) sz) m
  | Pdivs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divfs rs#rd rs#r1)) sz) m
  | Pnegs rd =>
      Next (nextinstr (rs#rd <- (Val.negfs rs#rd)) sz) m
  | Pabss rd =>
      Next (nextinstr (rs#rd <- (Val.absfs rs#rd)) sz) m
  | Pcomiss_ff r1 r2 =>
      Next (nextinstr (compare_floats32 (rs r1) (rs r2) rs) sz) m
  | Pxorps_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vsingle Float32.zero)) sz) m
  (** Branches and calls *)
  | Pjmp_l lbl =>
      goto_label f lbl rs m
  | Pjmp_s id sg =>
    let addr := Genv.symbol_address ge id Ptrofs.zero in
    match Genv.find_funct ge addr with
    | Some _ =>
      Next (rs#PC <- addr) m
    | _ => Stuck
    end
  | Pjmp_r r sg =>
    let addr := (rs r) in
    match Genv.find_funct ge addr with
    | Some _ =>
      Next (rs#PC <- addr) m
    | _ => Stuck
    end
  | Pjcc cond lbl =>
      match eval_testcond cond rs with
      | Some true => goto_label f lbl rs m
      | Some false => Next (nextinstr rs sz) m
      | None => Stuck
      end
  | Pjcc2 cond1 cond2 lbl =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => goto_label f lbl rs m
      | Some _, Some _ => Next (nextinstr rs sz) m
      | _, _ => Stuck
      end
  | Pjmptbl r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs #RAX <- Vundef #RDX <- Vundef) m
          end
      | _ => Stuck
      end
  | Pcall_s id sg =>
    let addr := Genv.symbol_address ge id Ptrofs.zero in
    match Genv.find_funct ge addr with
    | Some _ =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- addr) m
    | _ => Stuck
    end
  | Pcall_r r sg =>
    let addr := (rs r) in
    match Genv.find_funct ge addr with
    | Some _ =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- addr) m
    | _ => Stuck
    end
  | Pret =>
    if check_ra_after_call ge (rs#RA) then Next (rs#PC <- (rs#RA) #RA <- Vundef) m else Stuck
  (** Saving and restoring registers *)
  | Pmov_rm_a rd a =>
      exec_load (if Archi.ptr64 then Many64 else Many32) m a rs rd sz
  | Pmov_mr_a a r1 =>
      exec_store (if Archi.ptr64 then Many64 else Many32) m a rs r1 nil sz
  | Pmovsd_fm_a rd a =>
      exec_load Many64 m a rs rd sz
  | Pmovsd_mf_a a r1 =>
      exec_store Many64 m a rs r1 nil sz
  (** Pseudo-instructions *)
  | Plabel lbl =>
      Next (nextinstr rs sz) m
  | Pallocframe fsz ofs_ra ofs_link =>
    if zle 0 fsz then
    match rs # PC with
    |Vptr (Global id) _
     =>
     let (m0,path) := Mem.alloc_frame m id in
     let (m1, stk) := Mem.alloc m0 0 fsz in
     match Mem.record_frame (Mem.push_stage m1) (Memory.mk_frame fsz) with
     |None => Stuck
     |Some m2 =>
      let sp := Vptr stk Ptrofs.zero in
      match Mem.storev Mptr m2 (Val.offset_ptr sp ofs_ra) rs#RA with
      | None => Stuck
      | Some m3 =>
        match Mem.storev Mptr m3 (Val.offset_ptr sp ofs_link) rs#RSP with
        | None => Stuck
        | Some m4 => Next (nextinstr (rs #RAX <- (rs#RSP) #RSP <- sp) sz) m4
        end
      end
     end
    |_ => Stuck
    end else Stuck
  | Pfreeframe fsz ofs_ra ofs_link =>
    if zle 0 fsz then
      match loadvv Mptr m (Val.offset_ptr rs#RSP ofs_ra) with
      | None => Stuck
      | Some ra =>
          match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_link) with
          | None => Stuck
          | Some sp =>
              match rs#RSP with
              | Vptr stk ofs =>
                  if check_topframe fsz (Mem.astack (Mem.support m)) then
                  if Val.eq sp (parent_sp_stree (Mem.stack (Mem.support m))) then
                  if Val.eq (Vptr stk ofs) (top_sp_stree (Mem.stack (Mem.support m))) then
                  match Mem.free m stk 0 fsz with
                  | None => Stuck
                  | Some m' =>
                    match Mem.return_frame m' with
                    | None => Stuck
                    | Some m'' =>
                      match Mem.pop_stage m'' with
                        | None => Stuck
                        | Some m''' =>
                        Next (nextinstr (rs#RSP <- sp #RA <- ra) sz) m'''
                      end
                    end
                  end else Stuck else Stuck else Stuck
              | _ => Stuck
              end
          end
      end else Stuck
  | Pbuiltin ef args res =>
      Stuck                             (**r treated specially below *)
  (** The following instructions and directives are not generated
      directly by [Asmgen], so we do not model them. *)
  | Padcl_ri _ _
  | Padcl_rr _ _
  | Paddl_mi _ _
  | Paddl_rr _ _
  | Pbsfl _ _
  | Pbsfq _ _
  | Pbsrl _ _
  | Pbsrq _ _
  | Pbswap64 _
  | Pbswap32 _
  | Pbswap16 _
  | Pcfi_adjust _
  | Pfmadd132 _ _ _
  | Pfmadd213 _ _ _
  | Pfmadd231 _ _ _
  | Pfmsub132 _ _ _
  | Pfmsub213 _ _ _
  | Pfmsub231 _ _ _
  | Pfnmadd132 _ _ _
  | Pfnmadd213 _ _ _
  | Pfnmadd231 _ _ _
  | Pfnmsub132 _ _ _
  | Pfnmsub213 _ _ _
  | Pfnmsub231 _ _ _
  | Pmaxsd _ _
  | Pminsd _ _
  | Pmovb_rm _ _
  | Pmovq_rf _ _
  | Pmovsq_rm _ _
  | Pmovsq_mr _ _
  | Pmovsb
  | Pmovsw
  | Pmovw_rm _ _
  | Pnop
  | Prep_movsl
  | Psbbl_rr _ _
  | Psqrtsd _ _
  | Psubl_ri _ _
  | Psubq_ri _ _ => Stuck
  end.

(* maybe useful to prove SSAsm -> RealAsm_1 *)
  Definition exec_instr f i rs (m: mem) :=
    let isz := Ptrofs.repr (instr_size i) in
    match i with
    | Pallocframe sz ofs_ra ofs_link =>
      let aligned_sz := align sz 8 in
      let psp := (Val.offset_ptr (rs#RSP) (Ptrofs.repr (size_chunk Mptr))) in (* parent stack pointer *)
      let sp := Val.offset_ptr (rs#RSP) (Ptrofs.neg (Ptrofs.sub (Ptrofs.repr aligned_sz) (Ptrofs.repr (size_chunk Mptr)))) in
      match Mem.storev Mptr m (Val.offset_ptr sp ofs_link) psp with
        |None => Stuck
        |Some m1 =>
      Next (nextinstr (rs #RAX <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr))) #RSP <- sp) isz) m1
      end
    | Pfreeframe sz ofs_ra ofs_link =>
      let sp := Val.offset_ptr (rs RSP) (Ptrofs.sub (Ptrofs.repr (align sz 8)) (Ptrofs.repr (size_chunk Mptr))) in
      Next (nextinstr (rs#RSP <- sp) isz) m
    | Pcall_s i sg =>
      let sp := Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))) in
      match Mem.storev Mptr m sp (Val.offset_ptr rs#PC isz) with
        |None => Stuck
        |Some m1 =>
        Next (rs#RA <- (Val.offset_ptr rs#PC isz)
                #PC <- (Genv.symbol_address ge i Ptrofs.zero)
                #RSP <- sp) m1
      end
    |Pcall_r r sg =>
      let sp := Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))) in
      match Mem.storev Mptr m sp (Val.offset_ptr rs#PC isz) with
        |None => Stuck
        |Some m1 =>
        Next (rs#RA <- (Val.offset_ptr rs#PC isz)
                #PC <- (rs r)
                #RSP <- sp) m1
      end
    | Pret =>
      match loadvv Mptr m rs#RSP with
      | None => Stuck
      | Some ra =>
        let sp := Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr)) in
        Next (rs #RSP <- sp
                 #PC <- ra
                 #RA <- Vundef) m
      end
    | _ => exec_instr_asm f i rs m
    end.

  Inductive step  : state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
        exec_instr f i rs m = Next rs' m' ->
        step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
        eval_builtin_args ge rs (rs RSP) m args vargs ->
        external_call ef ge vargs m t vres m' ->
        rs' = nextinstr_nf
                (set_res res vres
                         (undef_regs (map preg_of (destroyed_by_builtin ef)) rs))
                         (Ptrofs.repr (instr_size (Pbuiltin ef args res))) ->
        step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments
        (rs # RSP <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr)))) m (ef_sig ef) args ->
        forall (SP_TYPE: Val.has_type (rs RSP) Tptr)
          ra (LOADRA: Mem.loadv Mptr m (rs RSP) = Some ra)
          (SP_NOT_VUNDEF: rs RSP <> Vundef)
          (RA_NOT_VUNDEF: ra <> Vundef),
      external_call ef ge args m t res m' ->
      rs' = (set_pair (loc_external_result (ef_sig ef))
                      res (undef_caller_save_regs rs))
              #PC <- ra
              #RA <- Vundef
              #RSP <- (Val.offset_ptr (rs RSP) (Ptrofs.repr (size_chunk Mptr)))
      ->
      step (State rs m) t (State rs' m').

End WITHGE.

Inductive initial_state (p: Asm.program): state -> Prop :=
  | initial_state_intro: forall m0 m1 m2 stk bmain,
      Genv.init_mem p = Some m0 ->
      Mem.alloc m0 0 (max_stacksize + (align (size_chunk Mptr)8)) = (m1, stk) ->
      Mem.storev Mptr m1 (Vptr stk (Ptrofs.repr (max_stacksize + align (size_chunk Mptr) 8 - size_chunk Mptr))) Vnullptr = Some m2 ->
      let ge := Genv.globalenv p in
      Genv.find_symbol ge p.(prog_main) = Some bmain ->
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Vptr bmain Ptrofs.zero)
        # RA <- Vnullptr
        # RSP <- (Val.offset_ptr
                   (Vptr stkblock (Ptrofs.repr (max_stacksize + align (size_chunk Mptr) 8)))
                   (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr)))) in
      initial_state p (State rs0 m2).

Definition semantics prog :=
  Semantics step (initial_state prog) final_state (Genv.globalenv prog).

Section WITHGETGE.

    Variable (ge tge: Genv.t Asm.fundef unit).
    Hypothesis (SADDR_EQ: forall id ofs, Genv.symbol_address tge id ofs = Genv.symbol_address ge id ofs).
    Hypothesis (FPTR_EQ: forall b, Genv.find_funct_ptr ge b = None <-> Genv.find_funct_ptr tge b = None).

    Lemma fptr_some_eq:
      forall b f, Genv.find_funct_ptr ge b = Some f ->
             exists f', Genv.find_funct_ptr tge b = Some f'.
    Proof.
      intros.
      destruct (Genv.find_funct_ptr tge b) eqn:EQ; eauto.
      rewrite <- FPTR_EQ in EQ. congruence.
    Qed.

    Lemma funct_some_eq:
      forall b f, Genv.find_funct ge b = Some f ->
             exists f', Genv.find_funct tge b = Some f'.
    Proof.
      unfold Genv.find_funct.
      intros. destruct b; auto; try congruence.
      destr_in H; eauto.
      subst.
      eapply fptr_some_eq; eauto.
    Qed.

    Lemma funct_none_eq: forall b, Genv.find_funct ge b = None <-> Genv.find_funct tge b = None.
    Proof.
      intros. unfold Genv.find_funct.
      destruct b; split; eauto.
      destr; eauto.
      subst. intros. rewrite <- FPTR_EQ. auto.
      destr; eauto.
      subst. intros. rewrite FPTR_EQ. auto.
    Qed.

 (*   Lemma goto_ofs_eq: forall sz ofs rs m,
        goto_ofs ge sz ofs rs m = goto_ofs tge sz ofs rs m.
    Proof.
      intros. unfold goto_ofs. destr; auto.
      destr. 
      exploit fptr_some_eq; eauto.
      intros (f1 & FT). rewrite FT. auto.
      rewrite FPTR_EQ in Heqo. rewrite Heqo. auto.
    Qed.
*)
    Ltac unfold_loadstore :=
      match goal with
      | [ |- context[ exec_load _ _ _ _ _  _] ] =>
        unfold exec_load
      | [ |- context[ exec_store _ _ _ _  _ _ _] ] =>
        unfold exec_store
      end.

    Ltac rewrite_eval_addrmode :=
      match goal with
      | [ |- context[ eval_addrmode _ _ _ ] ] =>
        erewrite eval_addrmode_same; eauto
      end.

    Lemma exec_valid_instr_same : forall (i:instruction) f f' i rs m,
        instr_valid i ->
        exec_instr ge f i rs m = exec_instr  tge f' i rs m.
    Proof.
      intros i f f' i0 rs m VI.
      destruct i0; cbn; auto;
        try (unfold_loadstore; rewrite_eval_addrmode);
        try (red in VI; cbn in VI; contradiction).
      - congruence.
      - erewrite eval_addrmode32_same; eauto.
      - erewrite eval_addrmode64_same; eauto.
      - erewrite SADDR_EQ. unfold Genv.find_funct.
        destruct (Genv.symbol_address ge symb Ptrofs.zero); auto.
        destruct (Ptrofs.eq_dec i0 Ptrofs.zero); auto.
        destr; destr.
        apply FPTR_EQ in Heqo0. congruence.
        apply FPTR_EQ in Heqo. congruence.
      - unfold Genv.find_funct.
        destruct (rs r); auto.
        destruct (Ptrofs.eq_dec i0 Ptrofs.zero); auto.
        destr; destr.
        apply FPTR_EQ in Heqo0. congruence.
        apply FPTR_EQ in Heqo. congruence.
      - erewrite SADDR_EQ. auto.
    Qed.

(*    Lemma label_pos_1_eq: forall lbl z c,
      Asm.label_pos lbl z c = label_pos instr_size_1 lbl z c.
    Proof.
      intros.
      unfold instr_size_1. simpl. reflexivity.
    Qed. *)

    Lemma goto_label_eq : forall (i:instruction) f f' l rs m,
        (forall lbl ofs, label_pos lbl ofs (fn_code f) = label_pos lbl ofs (fn_code f')) ->
        goto_label ge f l rs m = goto_label tge f' l rs m.
    Proof.
      intros.
      unfold goto_label. destr.
      - rewrite <- H. rewrite Heqo.
        destr; auto.
        destr.
        exploit fptr_some_eq; eauto.
        intros (f1 & FT). rewrite FT. auto.
        rewrite FPTR_EQ in Heqo0. rewrite Heqo0. auto.
      - rewrite <- H. setoid_rewrite Heqo. auto.
    Qed.

    Lemma exec_instr_same : forall (i:instruction) f f' i rs m,
        (forall lbl ofs, label_pos lbl ofs (fn_code f) = label_pos lbl ofs (fn_code f')) ->
        exec_instr ge f i rs m = exec_instr tge f' i rs m.
    Proof.
      intros i f f' i0 rs m LP.
      destruct (instr_valid_dec i0).
      eapply exec_valid_instr_same; eauto.
      unfold instr_valid in n.
      destruct i0; try tauto.
      - cbn. eapply goto_label_eq; eauto.
      - cbn. destr; auto. destr; auto.
        eapply goto_label_eq; eauto.
      - cbn. destr; auto. destr; auto.
        destr; auto. destr; auto.
        eapply goto_label_eq; eauto.
      - cbn. destr; auto. cbn. destr; auto.
        eapply goto_label_eq; eauto.
    Qed.

End WITHGETGE.

Section RECEPTIVEDET.

  Theorem real_asm_single_events p:
    single_events (semantics p).
  Proof.
    red. simpl. intros s t s' STEP.
    inv STEP; simpl. lia.
    eapply external_call_trace_length; eauto.
    eapply external_call_trace_length; eauto.
  Qed.

  Theorem real_asm_receptive p:
    receptive (semantics p).
  Proof.
    split.
    - simpl. intros s t1 s1 t2 STEP MT.
      inv STEP.
      inv MT. eexists. eapply exec_step_internal; eauto.
      edestruct external_call_receptive as (vres2 & m2 & EC2); eauto.
      eexists. eapply exec_step_builtin; eauto.
      edestruct external_call_receptive as (vres2 & m2 & EC2); eauto.
      eexists. eapply exec_step_external; eauto.
    - eapply real_asm_single_events; eauto.
  Qed.

  Theorem real_asm_determinate p :
    determinate (semantics p).
  Proof.
    split.
    - simpl; intros s t1 s1 t2 s2 STEP1 STEP2.
      inv STEP1.
      + inv STEP2; rewrite_hyps. split. constructor.  congruence.
        simpl in H2. inv H2.
      + inv STEP2; rewrite_hyps. inv H11.
        exploit eval_builtin_args_determ. apply H2. apply H9. intro; subst.
        exploit external_call_determ. apply H3. apply H10. intros (A & B); split; auto. intro C.
        destruct B; auto. congruence.
      + inv STEP2; rewrite_hyps.
        exploit extcall_arguments_determ. apply H1. apply H7. intro; subst.
        exploit external_call_determ. apply H2. apply H8. intros (A & B); split; auto. intro C.
        destruct B; auto. congruence.
    - apply real_asm_single_events.
    - simpl. intros s1 s2 IS1 IS2; inv IS1; inv IS2. rewrite_hyps.
      inv H0. rewrite_hyps. unfold rs0, rs1, ge, ge0 in *. rewrite_hyps. congruence.
    - simpl. intros s r FS.
      red. intros t s' STEP.
      inv FS. inv STEP; rewrite_hyps.
    - simpl. intros s r1 r2 FS1 FS2.
      inv FS1; inv FS2. congruence.
  Qed.

End RECEPTIVEDET.

Section WFASM.

  Fixpoint in_builtin_arg (b: builtin_arg preg) (r: preg) :=
    match b with
    | BA x => if preg_eq r x then True else False
    | BA_splitlong ba1 ba2 => in_builtin_arg ba1 r \/ in_builtin_arg ba2 r
    | BA_addptr ba1 ba2 => in_builtin_arg ba1 r \/ in_builtin_arg ba2 r
    | _ => False
    end.

  Inductive is_alloc : instruction -> Prop :=
    is_alloc_intro sz ora olink:
      is_alloc (Pallocframe sz ora olink).

  Definition make_palloc f  : instruction :=
    let sz := fn_stacksize f in
    (Pallocframe sz (Ptrofs.sub (Ptrofs.repr (align sz 8)) (Ptrofs.repr (size_chunk Mptr))) (fn_ofs_link f)).

  Lemma make_palloc_is_alloc:
    forall f,
      is_alloc (make_palloc f).
  Proof. constructor. Qed.

  Inductive is_free : instruction -> Prop :=
    is_free_intro sz ora olink:
      is_free (Pfreeframe sz ora olink).

  Lemma is_free_dec:
    forall i,
      {is_free i} + {~ is_free i}.
  Proof.
    destruct i; try now (right; intro A; inv A).
    left. econstructor; eauto.
  Defined.
  Inductive is_jmp: instruction -> Prop :=
  | is_jmps_intro: forall i sg, is_jmp (Pjmp_s i sg)
  | is_jmpr_intro: forall ir sg, is_jmp (Pjmp_r ir sg).


  Inductive intermediate_instruction : instruction -> Prop :=
  | ii_alloc i: is_alloc i -> intermediate_instruction i
  | ii_jmp i: i = Pret \/ is_jmp i -> intermediate_instruction i.

  Record wf_asm_function (f: function): Prop :=
    {

      wf_asm_alloc_only_at_beginning:
        forall o sz ora olink,
          find_instr o (fn_code f) = Some (Pallocframe sz ora olink) ->
          o = 0;

      wf_asm_alloc_at_beginning:
        find_instr 0 (fn_code f) = Some (make_palloc f);

      wf_asm_after_freeframe:
        forall i o,
          find_instr (Ptrofs.unsigned o) (fn_code f) = Some i ->
          is_free i ->
          exists i' ,
            find_instr (Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (instr_size i)))) (fn_code f) = Some i' /\
            (i' = Pret \/ is_jmp i' );

      wf_asm_ret_jmp_comes_after_freeframe:
        forall i o,
          find_instr (Ptrofs.unsigned o) (fn_code f) = Some i ->
          i = Pret \/ is_jmp i ->
          exists o' ifree,
            find_instr (Ptrofs.unsigned o') (fn_code f) = Some ifree /\
            is_free ifree /\
            Ptrofs.unsigned o' + instr_size ifree = Ptrofs.unsigned o;

      wf_asm_code_bounded:
        0 <= code_size (fn_code f) <= Ptrofs.max_unsigned;

      wf_asm_builtin_not_PC:
        forall o ef args res,
          find_instr o (fn_code f) = Some (Pbuiltin ef args res) ->
          ~ in_builtin_res res PC /\
          ~ in_builtin_res res RSP
          /\ Forall (fun arg : builtin_arg preg => ~ in_builtin_arg arg RA) args;

      wf_asm_jmp_no_rsp:
        forall o (r: ireg) sg,
          find_instr o (fn_code f) = Some (Pjmp_r r sg) ->
          r <> RSP;

      wf_asm_call_no_rsp:
        forall o (r: ireg) sg,
          find_instr o (fn_code f) = Some (Pcall_r r sg) ->
          r <> RSP;

      wf_asm_free_spec:
        forall o sz ora olink,
          find_instr o (fn_code f) = Some (Pfreeframe sz ora olink) ->
          sz = fn_stacksize f /\ ora = Ptrofs.sub (Ptrofs.repr (align sz 8)) (Ptrofs.repr (size_chunk Mptr));

      wf_allocframe_repr:
        forall o sz ora olink,
          find_instr o (fn_code f) = Some (Pallocframe sz ora olink) ->
          align sz 8 - size_chunk Mptr =
          Ptrofs.unsigned (Ptrofs.sub (Ptrofs.repr (align sz 8)) (Ptrofs.repr (size_chunk Mptr)));

      wf_freeframe_repr:
        forall o sz ora olink,
          find_instr o (fn_code f) = Some (Pfreeframe sz ora olink) ->
          Ptrofs.repr (align sz 8 - size_chunk Mptr) = Ptrofs.sub (Ptrofs.repr (align sz 8)) (Ptrofs.repr (size_chunk Mptr));
    }.

  Definition is_make_palloc a f :=  a = make_palloc f /\
                                    align (fn_stacksize f) 8 - size_chunk Mptr =
                                    Ptrofs.unsigned (Ptrofs.sub (Ptrofs.repr (align (fn_stacksize f) 8)) (Ptrofs.repr (size_chunk Mptr))).
(*
  Lemma pair_eq: forall {A B}
                   (Adec: forall (a b: A), {a = b} + {a <> b})
                   (Bdec: forall (a b: B), {a = b} + {a <> b}),
      forall (a b: A * B), {a = b} + {a <> b}.
  Proof.
    intros.
    destruct a, b.
    destruct (Adec a a0), (Bdec b b0); subst;
      first [ now (right; inversion 1; congruence)
            | left; reflexivity ].
  Defined.
*)
  Definition pallocframe_dec s s' o o' l l':
    {Pallocframe s o l= Pallocframe s' o' l'} + {Pallocframe s o l <> Pallocframe s' o' l'}.
  Proof.
    destruct (zeq s s'); subst. 2: (now right; inversion 1).
    destruct (Ptrofs.eq_dec o o'); subst. 2: (now right; inversion 1).
    destruct (Ptrofs.eq_dec l l'); subst. 2: (now right; inversion 1).
    left; reflexivity.
  Defined.

  Lemma and_dec: forall {A B: Prop},
      { A } + { ~ A } ->
      { B } + { ~ B } ->
      { A /\ B } + { ~ (A /\ B) }.
  Proof.
    intros. destruct H, H0; [left|right|right|right]; intuition.
  Qed.

  Definition is_make_palloc_dec a f : { is_make_palloc a f } + { ~ is_make_palloc a f }.
  Proof.
    unfold is_make_palloc, make_palloc.
    destruct a; try (now right; inversion 1).
    apply and_dec.
    apply pallocframe_dec.
    apply zeq.
  Defined.

  Definition check_ret_or_jmp roj :=
    match roj with
    | Pret |Pjmp_r _ _ | Pjmp_s _ _=> true
    | _ => false
    end.

  Definition valid_ret_or_jmp roj :=
    match roj with
    | Pjmp_r r _ =>  negb (preg_eq r RSP)
    | _ => true
    end.

  Definition check_free f sz ora :=
      sz = fn_stacksize f /\ ora = Ptrofs.sub (Ptrofs.repr (align sz 8)) (Ptrofs.repr (size_chunk Mptr)) /\
      Ptrofs.repr (align sz 8 - size_chunk Mptr) = Ptrofs.sub (Ptrofs.repr (align sz 8)) (Ptrofs.repr (size_chunk Mptr)).

  Definition check_free_dec f sz ora : { check_free f sz ora } + { ~ check_free f sz ora }.
  Proof.
    unfold check_free.
    apply and_dec. 2: apply and_dec.
    apply zeq. apply Ptrofs.eq_dec. apply Ptrofs.eq_dec.
  Defined.

  Definition check_builtin args res :=
    ~ in_builtin_res res PC /\
    ~ in_builtin_res res RSP
    /\ Forall (fun arg : builtin_arg preg => ~ in_builtin_arg arg RA) args.

  Lemma not_in_builtin_res_dec res r:
    {~ in_builtin_res res r} + {~ ~ in_builtin_res res r}.
  Proof.
    induction res; simpl.
    destruct (preg_eq x r); subst; intuition. left; inversion 1.
    destruct IHres1, IHres2; try (right; now intuition). left. intuition congruence.
  Qed.


  Lemma not_in_builtin_arg_dec arg r:
    {~ in_builtin_arg arg r} + {~ ~ in_builtin_arg arg r}.
  Proof.
    induction arg; simpl; try (try destr; left; now inversion 1).
    destruct IHarg1, IHarg2; try (right; now intuition). left. intuition congruence.
    destruct IHarg1, IHarg2; try (right; now intuition). left. intuition congruence.
  Qed.

  Definition check_builtin_dec args res: {check_builtin args res} + { ~ check_builtin args res}.
  Proof.
    unfold check_builtin.
    repeat apply and_dec.
    apply not_in_builtin_res_dec.
    apply not_in_builtin_res_dec.
    apply Forall_dec. intros.
    apply not_in_builtin_arg_dec.
  Defined.

  Hypothesis instr_size_repr : forall i, 0 <= instr_size i <= Ptrofs.max_unsigned.
  Hypothesis instr_size_positive : forall i, 0 < instr_size i.

  Lemma code_size_non_neg: forall c, 0 <= code_size c.
  Proof.
    intros. induction c; simpl. lia. generalize (instr_size_positive a); lia.
  Qed.

  Lemma find_instr_bound:
    forall c o i,
      find_instr o c = Some i ->
      o + instr_size i <= code_size c.
  Proof.
    induction c; simpl; intros; eauto. congruence.
    destr_in H. inv H. generalize (code_size_non_neg c) (instr_size_positive i). lia.
    apply IHc in H. lia.
  Qed.

  Lemma find_instr_pos_positive:
        forall c o i,
          find_instr o c = Some i ->
          0 <= o.
   Proof.
     induction c; intros; simpl; inv H. destr_in H1. lia.
     eapply IHc in H1. generalize (instr_size_positive a). lia.
   Qed.
(*
  Lemma instr_size_repr : 0 <= 1 <= Ptrofs.max_unsigned.
  Proof.
    vm_compute. split; congruence.
  Qed.*)

  Lemma code_bounded_repr':
    forall c
      (RNG: 0 <= code_size c <= Ptrofs.max_unsigned)
      i o
      (FI: find_instr o c = Some i)
      sz
      (LE: 0 <= sz <= instr_size i),
      Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr o) (Ptrofs.repr sz)) = o + sz.
  Proof.
    intros.
    unfold Ptrofs.add.
    rewrite (Ptrofs.unsigned_repr sz). 2: generalize (instr_size_repr i); lia.
    generalize (find_instr_bound _ _ _ FI) (find_instr_pos_positive _ _ _ FI). intros.
    rewrite (Ptrofs.unsigned_repr o) by lia.
    apply Ptrofs.unsigned_repr; lia.
  Qed.

  Lemma code_bounded_repr:
    forall c
      (RNG: 0 <= code_size c <= Ptrofs.max_unsigned)
      i o
      (FI: find_instr (Ptrofs.unsigned o) c = Some i)
      sz
      (LE: 0 <= sz <= instr_size i),
      Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr sz)) = Ptrofs.unsigned o + sz.
  Proof.
    intros.
    erewrite <- code_bounded_repr'; eauto.
    unfold Ptrofs.add.
    rewrite Ptrofs.repr_unsigned. reflexivity.
  Qed.

  Lemma wf_asm_pc_repr' : forall f : function,
       wf_asm_function f ->
       forall (i : instruction) (o : ptrofs),
       find_instr (Ptrofs.unsigned o) (fn_code f) = Some i ->
       forall sz : Z, 0 <= sz <= instr_size i ->
       Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr sz)) = Ptrofs.unsigned o + sz.
  Proof.
    intros; eapply code_bounded_repr; eauto.
    apply wf_asm_code_bounded; eauto.
  Qed.

  Fixpoint check_asm_body (f: function) (next_roj: bool) (r: code) : bool :=
    match r with
    | nil => negb next_roj
    | i :: r =>
      let roj := proj_sumbool (is_free_dec i) in
      check_asm_body f roj r &&
      if next_roj then check_ret_or_jmp i && valid_ret_or_jmp i
      else
        negb (check_ret_or_jmp i) &&
        match i with
        | Pfreeframe sz ora olink =>     (* after a free, ret or jmp *)
          check_free_dec f sz ora
        | Pallocframe _ _ _ => false (* no alloc in body *)
        | Pcall_r r sg => negb (preg_eq r RSP)
        | Pbuiltin _ args res => check_builtin_dec args res
        | _ => true
      end
    end.

  Definition wf_asm_function_check (f: function) : bool :=
    match fn_code f with
    | nil => false
    | a::r => is_make_palloc_dec a f && check_asm_body f false r
    end && zle (code_size (fn_code f)) Ptrofs.max_unsigned.

  Lemma check_asm_body_no_alloc:
    forall f c b i,
      check_asm_body f b c = true ->
      In i c ->
      ~ is_alloc i.
  Proof.
    induction c; simpl; intros. easy.
    intro IA. inv IA.
    assert (exists b, check_asm_body f b c = true).
    {
      eexists. refine (proj1 _); apply andb_true_iff; eauto.
    }
    destruct H1.
    destruct H0. subst. simpl in *.
    apply andb_true_iff in H. destruct H. destr_in H0.
    eapply IHc in H0; eauto. apply H0; constructor.
  Qed.

  Lemma find_instr_app:
    forall a o b,
      0 <= o ->
      find_instr (o + code_size a) (a ++ b) = find_instr o b.
  Proof.
    induction a; simpl; intros; eauto.
    f_equal. lia.
    rewrite pred_dec_false.
    rewrite <- (IHa o b). f_equal. lia. lia.
    generalize (code_size_non_neg a0). generalize (instr_size_positive a). lia.
  Qed.

  Lemma find_instr_app':
    forall a o b,
      code_size a <= o ->
      find_instr o (a ++ b) = find_instr (o - code_size a) b.
  Proof.
    intros.
    rewrite <- (find_instr_app a _ b). f_equal. lia. lia.
  Qed.

  Lemma find_instr_split:
    forall c o i,
      find_instr o c = Some i ->
      exists a b, c = a ++ i :: b /\ o = code_size a.
  Proof.
    induction c; simpl; intros; eauto. congruence.
    destr_in H. inv H. eexists nil, c; simpl. split; auto.
    edestruct IHc as (aa & b & EQ & SZ). apply H. subst.
    exists (a::aa), b; simpl; split; auto.
    generalize (instr_size_positive a). lia.
  Qed.

  Lemma find_instr_app_pres: forall f1 f2 ofs i,
      find_instr ofs f1 = Some i ->
      find_instr ofs (f1 ++ f2) = Some i.
  Proof.
    induction f1 as [|i1 f1].
    - cbn. intros; congruence.
    - cbn. intros f2 i FI.
      destr. eauto.
  Qed.

  Lemma code_size_app:
    forall c1 c2,
      code_size (c1 ++ c2) = code_size c1 + code_size c2.
  Proof.
    induction c1; simpl; intros; eauto. rewrite IHc1. lia.
  Qed.

  Lemma check_asm_body_after_free:
    forall f a i b roj,
      check_asm_body f roj (a ++ i :: b) = true ->
      is_free i ->
      check_asm_body f true b = true.
  Proof.
    induction a; simpl; intros; eauto.
    apply andb_true_iff in H. destruct H as (H & _).
    inv H0. simpl in *. auto.
    apply andb_true_iff in H. destruct H as (H & B).
    destruct (is_free_dec a); simpl in *. inv i0.
    eapply IHa; eauto.
    eapply IHa; eauto.
  Qed.


  Lemma check_asm_body_call:
    forall f c b r sg,
      check_asm_body f b c = true ->
      In (Pcall_r r sg) c ->
      r <> RSP.
  Proof.
    induction c; simpl; intros. easy.
    assert (exists b, check_asm_body f b c = true).
    {
      eexists. refine (proj1 _); apply andb_true_iff; eauto.
    }
    apply andb_true_iff in H. destruct H. destruct H1. destruct H0; eauto. subst. simpl in *.
    destr_in H2; simpl in *.
    unfold proj_sumbool in H2; destr_in H2. simpl in H2. congruence.
  Qed.

  Lemma check_asm_body_free:
    forall f c b sz ora olink,
      check_asm_body f b c = true ->
      In (Pfreeframe sz ora olink) c ->
      check_free f sz ora.
  Proof.
    induction c; simpl; intros. easy.
    assert (exists b, check_asm_body f b c = true).
    {
      eexists. refine (proj1 _); apply andb_true_iff; eauto.
    }
    apply andb_true_iff in H. destruct H. destruct H1. destruct H0; eauto. subst. simpl in *.
    destr_in H2; simpl in *.
    unfold proj_sumbool in H2; destr_in H2.
  Qed.

  Lemma check_asm_body_before_roj:
    forall f a i b roj,
      check_asm_body f roj (a ++ i :: b) = true ->
      i = Pret \/ is_jmp i ->
      (a = nil /\ roj = true) \/ exists a0 i0, a = a0 ++ i0 :: nil /\ is_free i0.
  Proof.
    induction a; simpl; intros; eauto.
    - apply andb_true_iff in H. destruct H as (A & B).
      destruct H0 as [ROJ|ROJ]; inv ROJ; simpl in *. destr_in B.
      destruct roj. auto. congruence. destr_in B.
    - apply andb_true_iff in H. destruct H as (A & B).
      destruct (is_free_dec a); simpl in *. inv i0.
      + simpl in *. destr_in B. right.
        destruct a0. clear IHa. simpl in *.
        eexists nil, _. split. simpl. eauto. constructor.
        edestruct IHa as [ROJ|(a1 & i1 & EQ & IFR)]; eauto.
        destruct ROJ; congruence. rewrite EQ.
        eexists (_ :: a1), i1; split. simpl. reflexivity. auto.
      + edestruct IHa as [ROJ|(a1 & i1 & EQ & IFR)]; eauto.
        destruct ROJ; congruence. subst. right.
        eexists (_ :: a1), i1; split. simpl. reflexivity. auto.
  Qed.

  Lemma check_asm_body_builtin:
    forall f c b ef args res,
      check_asm_body f b c = true ->
      In (Pbuiltin ef args res) c ->
      check_builtin args res.
  Proof.
    induction c; simpl; intros. easy.
    assert (exists b, check_asm_body f b c = true).
    {
      eexists. refine (proj1 _); apply andb_true_iff; eauto.
    }
    destruct H1.
    destruct H0. subst. simpl in *.
    apply andb_true_iff in H. destruct H. destr_in H0.
    unfold proj_sumbool in H0; destr_in H0.
    eapply IHc in H0; eauto.
  Qed.

  Lemma check_asm_body_jmp:
    forall f c b r sg,
      check_asm_body f b c = true ->
      In (Pjmp_r  r sg) c ->
      r <> RSP.
  Proof.
    induction c; simpl; intros. easy.
    assert (exists b, check_asm_body f b c = true).
    {
      eexists. refine (proj1 _); apply andb_true_iff; eauto.
    }
    apply andb_true_iff in H. destruct H. destruct H1. destruct H0; eauto. subst. simpl in *.
    destr_in H2; simpl in *.
    unfold proj_sumbool in H2; destr_in H2. simpl in H2. congruence.
  Qed.

  Lemma find_instr_in:
    forall c pos i,
      find_instr pos c = Some i -> In i c.
  Proof.
    induction c; simpl. intros; discriminate.
    intros until i. case (zeq pos 0); intros.
    left; congruence. right; eauto.
  Qed.

  Lemma wf_asm_function_check_correct f:
    wf_asm_function_check f = true ->
    wf_asm_function f.
  Proof.
    unfold wf_asm_function_check. destr. simpl. congruence.
    rewrite ! andb_true_iff. intros ((A & B) & C).
    unfold proj_sumbool in A, C. destr_in A; destr_in C.
    clear A C. rename Heqc into CODE. rename l into SIZE.
    constructor.
    - rewrite CODE. simpl. intros. destr_in H.
      apply find_instr_in in H.
      eapply check_asm_body_no_alloc in H; eauto. contradict H. constructor.
    - rewrite CODE; simpl. clear - i0. destruct i0 as (A & B). subst. reflexivity.
    - destruct i0 as (i0 & _). subst. rewrite CODE. simpl.
      intros. destr_in H. inv H. inv H0.
      simpl in SIZE.
      rewrite pred_dec_false.
      replace (Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (instr_size i))) - instr_size (make_palloc f))
        with (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr (Ptrofs.unsigned o - instr_size (make_palloc f))) (Ptrofs.repr (instr_size i)))).
      revert H.
      generalize (Ptrofs.unsigned o - instr_size (make_palloc f)).
      intros. 
      edestruct find_instr_split as (a & b & EQ & SZ). apply H. subst.
      rewrite find_instr_app'.
      simpl. rewrite pred_dec_false.
      eapply check_asm_body_after_free in B; eauto.
      destruct b; simpl in B. congruence. simpl. rewrite pred_dec_true. eexists; split; eauto.
      apply andb_true_iff in B. destruct B as (B & CHK).
      unfold check_ret_or_jmp in CHK. apply andb_true_iff in CHK. destruct CHK as (CHK & _). destr_in CHK; try (right; constructor).
      unfold Ptrofs.add.
      rewrite (Ptrofs.unsigned_repr (code_size a)).
      rewrite (Ptrofs.unsigned_repr _ (instr_size_repr i)).
      rewrite Ptrofs.unsigned_repr. lia.
      simpl in SIZE. rewrite code_size_app in SIZE. simpl in SIZE.
      generalize (code_size_non_neg a) (instr_size_positive i) (instr_size_positive i0) (code_size_non_neg b)
                 (instr_size_positive (make_palloc f)). lia.
      simpl in SIZE. rewrite code_size_app in SIZE. simpl in SIZE.
      generalize (code_size_non_neg a) (instr_size_positive i) (instr_size_positive i0) (code_size_non_neg b)
                 (instr_size_positive (make_palloc f)). lia.
      unfold Ptrofs.add.
      rewrite (Ptrofs.unsigned_repr (code_size a)).
      rewrite (Ptrofs.unsigned_repr _ (instr_size_repr i)).
      rewrite Ptrofs.unsigned_repr. generalize (instr_size_positive i); lia.
      simpl in SIZE. rewrite code_size_app in SIZE. simpl in SIZE.
      generalize (code_size_non_neg a) (instr_size_positive i) (code_size_non_neg b)
                 (instr_size_positive (make_palloc f)). lia.
      simpl in SIZE. rewrite code_size_app in SIZE. simpl in SIZE.
      generalize (code_size_non_neg a) (instr_size_positive i) (code_size_non_neg b)
                 (instr_size_positive (make_palloc f)). lia.
      unfold Ptrofs.add.
      rewrite (Ptrofs.unsigned_repr (code_size a)).
      rewrite (Ptrofs.unsigned_repr _ (instr_size_repr i)).
      rewrite Ptrofs.unsigned_repr. generalize (instr_size_positive i); lia.
      simpl in SIZE. rewrite code_size_app in SIZE. simpl in SIZE.
      generalize (code_size_non_neg a) (instr_size_positive i) (code_size_non_neg b)
                 (instr_size_positive (make_palloc f)). lia.
      simpl in SIZE. rewrite code_size_app in SIZE. simpl in SIZE.
      generalize (code_size_non_neg a) (instr_size_positive i) (code_size_non_neg b)
                 (instr_size_positive (make_palloc f)). lia.
      unfold Ptrofs.add.
      rewrite (Ptrofs.unsigned_repr _ (instr_size_repr i)).
      rewrite (Ptrofs.unsigned_repr (Ptrofs.unsigned o - _)).
      rewrite ! Ptrofs.unsigned_repr. lia.
      generalize (find_instr_bound _ _ _ H) (find_instr_pos_positive _ _ _ H).
      generalize (instr_size_positive i)
                 (instr_size_positive (make_palloc f)). lia.
      generalize (find_instr_bound _ _ _ H) (find_instr_pos_positive _ _ _ H).
      generalize (instr_size_positive i)
                 (instr_size_positive (make_palloc f)). lia.
      generalize (find_instr_bound _ _ _ H) (find_instr_pos_positive _ _ _ H).
      generalize (instr_size_positive i)
                 (instr_size_positive (make_palloc f)). lia.
      unfold Ptrofs.add.
      rewrite (Ptrofs.unsigned_repr _ (instr_size_repr i)).
      rewrite Ptrofs.unsigned_repr.
      generalize (Ptrofs.unsigned_range o) (instr_size_positive i); lia.
      generalize (find_instr_bound _ _ _ H) (find_instr_pos_positive _ _ _ H).
      generalize (instr_size_positive i)
                 (instr_size_positive (make_palloc f)). lia.
    - destruct i0 as (i0 & _). subst. rewrite CODE. simpl.
      intros i o FI ROJ.
      destr_in FI. inv FI. destruct ROJ as [ROJ|ROJ]; inv ROJ.
      edestruct find_instr_split as (a & b & EQ & SZ). apply FI. subst.
      destruct (check_asm_body_before_roj _ _ _ _ _ B ROJ) as [(NIL & ROJFALSE)|(a0 & i0 & EQ & IFR)]. congruence.
      subst.
      exists (Ptrofs.sub o (Ptrofs.repr (instr_size i0))), i0.
      rewrite pred_dec_false.
      replace (Ptrofs.unsigned (Ptrofs.sub o (Ptrofs.repr (instr_size i0))) - instr_size (make_palloc f)) 
        with (0 + code_size a0). rewrite app_ass.
      rewrite find_instr_app. simpl. split; auto. split. auto.
      unfold Ptrofs.sub. 
      rewrite (Ptrofs.unsigned_repr _ (instr_size_repr i0)).
      rewrite Ptrofs.unsigned_repr. lia.
      generalize (find_instr_bound _ _ _ FI) (find_instr_pos_positive _ _ _ FI). intros.
      simpl in *. rewrite ! code_size_app in *. simpl in *.
      generalize (code_size_non_neg a0) (instr_size_positive i) (instr_size_positive i0) (code_size_non_neg b)
                 (instr_size_positive (make_palloc f)). lia.
      lia.
      unfold Ptrofs.sub. 
      rewrite (Ptrofs.unsigned_repr _ (instr_size_repr i0)).
      rewrite Ptrofs.unsigned_repr.
      simpl in *. rewrite ! code_size_app in *. simpl in *. lia.
      generalize (find_instr_bound _ _ _ FI) (find_instr_pos_positive _ _ _ FI). intros.
      simpl in *. rewrite ! code_size_app in *. simpl in *.
      generalize (code_size_non_neg a0) (instr_size_positive i) (instr_size_positive i0) (code_size_non_neg b)
                 (instr_size_positive (make_palloc f)). lia.
      unfold Ptrofs.sub. 
      rewrite (Ptrofs.unsigned_repr _ (instr_size_repr i0)).
      rewrite Ptrofs.unsigned_repr.
      simpl in *. rewrite ! code_size_app in *. simpl in *.
      generalize (find_instr_bound _ _ _ FI) (find_instr_pos_positive _ _ _ FI). intros. 
      simpl in *. rewrite ! code_size_app in *. simpl in *.
      generalize (code_size_non_neg a0) (instr_size_positive i) (instr_size_positive i0) (code_size_non_neg b)
                 (instr_size_positive (make_palloc f)). lia.
      generalize (find_instr_bound _ _ _ FI) (find_instr_pos_positive _ _ _ FI). intros. 
      simpl in *. rewrite ! code_size_app in *. simpl in *.
      generalize (code_size_non_neg a0) (instr_size_positive i) (instr_size_positive i0) (code_size_non_neg b)
                 (instr_size_positive (make_palloc f)). lia.
    - rewrite CODE; split; auto.
      generalize (code_size_non_neg (i::c)). lia.
    - destruct i0 as (i0 & _). subst. rewrite CODE. simpl.
      intros o ef args res FI.
      destr_in FI. inv FI.
      apply find_instr_in in FI.
      eapply check_asm_body_builtin in FI; eauto.
    - destruct i0 as (i0 & _). subst. rewrite CODE. simpl.
      intros o r sg FI.
      destr_in FI. inv FI.
      apply find_instr_in in FI.
      eapply check_asm_body_jmp in FI; eauto.
    - destruct i0 as (i0 & _). subst. rewrite CODE. simpl.
      intros o r sg FI.
      destr_in FI. inv FI.
      apply find_instr_in in FI.
      eapply check_asm_body_call in FI; eauto.
    - destruct i0 as (i0 & _). subst. rewrite CODE. simpl.
      intros o sz ora olink FI.
      destr_in FI. inv FI.
      apply find_instr_in in FI.
      edestruct check_asm_body_free as (A & BB & C); subst; eauto.
    - destruct i0 as (i0 & PA). subst. rewrite CODE. simpl.
      intros o sz ora olink FI.
      destr_in FI. inv FI; auto.
      apply find_instr_in in FI.
      eapply check_asm_body_no_alloc in FI; eauto. contradict FI; constructor.
    - destruct i0 as (i0 & _). subst. rewrite CODE. simpl.
      intros o sz ora olink FI.
      destr_in FI. inv FI.
      apply find_instr_in in FI.
      edestruct check_asm_body_free as (A & BB & C); subst; eauto.
  Qed.

  Lemma wf_asm_pc_repr:
    forall f (WF: wf_asm_function f) i o,
      find_instr (Ptrofs.unsigned o) (fn_code f) = Some i ->
      Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (instr_size i))) = Ptrofs.unsigned o + instr_size i.
  Proof.
    intros; eapply wf_asm_pc_repr'; eauto. generalize (instr_size_positive i); lia.
  Qed.

  Lemma wf_asm_wf_allocframe:
    forall f (WF: wf_asm_function f) o sz ora olink
      (FI: find_instr o (fn_code f) = Some (Pallocframe sz ora olink)),
      make_palloc f = Pallocframe sz ora olink.
  Proof.
    intros.
    exploit wf_asm_alloc_only_at_beginning; eauto. intro; subst.
    erewrite wf_asm_alloc_at_beginning in FI; eauto. inv FI; auto.
  Qed.

End WFASM.

End INSTRSIZE.
(* RealAsm senmantic version 1: instr_size == 1*)

Definition instr_size_1 : instruction -> Z := fun i => 1.


Definition rs_state s :=
  let '(State rs _) := s in rs.
Definition m_state s :=
  let '(State _ m) := s in m.

  Section INVARIANT.

    Variable prog: Asm.program.
    Let ge := Genv.globalenv prog.

    Definition bstack := stkblock.

    Definition rsp_ptr (s: state) : Prop :=
      exists o, rs_state s RSP = Vptr bstack o /\ (align_chunk Mptr | Ptrofs.unsigned o).

    Definition bstack_perm (s: state) : Prop :=
      forall o k p,
        Mem.perm (m_state s) bstack o k p ->
        Mem.perm (m_state s) bstack o k Writable.

    Definition stack_top_state (s: state) : Prop :=
      exists tl st, Mem.stack(Mem.support (m_state s))= Node None (1%positive::nil) tl st.

    Inductive real_asm_inv : state -> Prop :=
    | real_asm_inv_intro:
        forall s
          (RSPPTR: rsp_ptr s)
          (BSTACKPERM: bstack_perm s)
          (STOP: stack_top_state s),
          real_asm_inv s.

    Lemma storev_perm :
      forall m chunk addr v m', Mem.storev chunk m addr v = Some m' ->
                           (forall b o k p, Mem.perm m' b o k p <-> Mem.perm m b o k p).
      Proof.
        intros. unfold Mem.storev in H. destr_in H. split.
        eapply Mem.perm_store_2; eauto. eapply Mem.perm_store_1; eauto.
      Qed.

    Lemma real_initial_inv:
      forall is,
        initial_state prog is -> real_asm_inv is.
    Proof.
      intros. inv H.
      apply Genv.init_mem_stack in H0 as STK.
      constructor.
      - red. simpl. unfold rs0; simpl_regs. eexists. split. reflexivity.
        apply div_ptr_add.
        apply div_unsigned_repr.
        apply Z.divide_add_r. apply align_Mptr_stack_limit. apply align_Mptr_align8.
        apply align_Mptr_modulus. unfold Ptrofs.neg. apply div_unsigned_repr.
        apply Zdivide_opp_r.
        apply div_unsigned_repr.
        apply align_size_chunk_divides.
        apply align_Mptr_modulus.
        apply align_Mptr_modulus.
        apply align_Mptr_modulus.
      - exploit Mem.alloc_result; eauto. intro. subst.
        unfold Mem.nextblock in H1. unfold Mem.fresh_block in H1.
        rewrite STK in H1. destr_in H1. simpl in Heqp. inv Heqp.
        red. unfold bstack. unfold stkblock. intros o k p.
        repeat erewrite (storev_perm _ _ _ _ _ H2). eauto.
        intro. exploit Mem.perm_alloc_3; eauto.
        intro. exploit Mem.perm_alloc_2; eauto. simpl. intro. eapply Mem.perm_implies; eauto.
        apply perm_F_any.
      - red. simpl. apply Mem.stack_alloc in H1. rewrite STK in H1.
        exists nil, None. simpl in H1. erewrite <- Mem.support_storev; eauto.
Qed.

(*    Lemma nextinstr_1_eq :
      forall rs,
        nextinstr rs Ptrofs.one = Asm.nextinstr rs.
    Proof.
      intros. reflexivity.
    Qed. *)

    Lemma exec_instr_invar_same:
      forall f i rs1 m1,
        stk_unrelated_instr i = true ->
        exec_instr instr_size_1 ge f i rs1 m1 = SSAsm.exec_instr ge f i rs1 m1.
    Proof.
      intros f i rs1 m1 SI.
      destruct i; simpl in SI; simpl; unfold instr_size_1; simpl; try reflexivity; congruence.
    Qed.

    Lemma exec_instr_invar_same':
      forall f i rs1 m1,
        stk_unrelated_instr i = true ->
        Asm.exec_instr ge f i rs1 m1 = SSAsm.exec_instr ge f i rs1 m1.
    Proof.
      intros f i rs1 m1 SI.
      destruct i; simpl in SI; simpl; try congruence.
    Qed.

    Lemma exec_instr_invar_inv:
      forall f i rs1 m1 rs2 m2,
        asm_instr_unchange_rsp i ->
        stk_unrelated_instr i = true ->
        exec_instr (instr_size_1) ge f i rs1 m1 = Next rs2 m2 ->
        real_asm_inv (State rs1 m1) ->
        real_asm_inv (State rs2 m2).
    Proof.
      intros f i rs1 m1 rs2 m2 NORSP INVAR EI RAI; inv RAI.
      erewrite exec_instr_invar_same in EI; eauto.
      erewrite <- exec_instr_invar_same' in EI; eauto.
      exploit NORSP; eauto. intro EQ.
      generalize (asm_prog_unchange_sup i INVAR _ _ _ _ _ _ EI). intros (A & B).
      constructor.
      + red in RSPPTR; red. simpl in *; rewrite <- EQ. eauto.
      + red in BSTACKPERM; red. simpl in *. setoid_rewrite <- B. eauto.
      + red in STOP; red; simpl in *. rewrite <- A; eauto.
    Qed.

    Lemma align_Mptr_sub:
      forall o,
        (align_chunk Mptr | Ptrofs.unsigned o) ->
        (align_chunk Mptr | Ptrofs.unsigned (Ptrofs.add o (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))))).
    Proof.
      intros.
      apply div_ptr_add; auto.
      apply div_unsigned_repr.
      apply Z.divide_opp_r.
      apply div_unsigned_repr.
      apply align_size_chunk_divides.
      apply align_Mptr_modulus.
      apply align_Mptr_modulus.
      apply align_Mptr_modulus.
    Qed.

    Lemma align_Mptr_add:
      forall o,
        (align_chunk Mptr | Ptrofs.unsigned o) ->
        (align_chunk Mptr | Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (size_chunk Mptr)))).
    Proof.
      intros.
      apply div_ptr_add; auto.
      apply div_unsigned_repr.
      apply align_size_chunk_divides.
      apply align_Mptr_modulus.
      apply align_Mptr_modulus.
    Qed.

    Lemma align_Mptr_add_gen:
      forall o d,
        (align_chunk Mptr | Ptrofs.unsigned o) ->
        (align_chunk Mptr | Ptrofs.unsigned d) ->
        (align_chunk Mptr | Ptrofs.unsigned (Ptrofs.add o d)).
    Proof.
      intros.
      apply div_ptr_add; auto.
      apply align_Mptr_modulus.
    Qed.

    Definition asm_prog_no_rsp (ge: Genv.t Asm.fundef unit):=
      forall b f,
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        asm_code_no_rsp (fn_code f).

  Definition wf_asm_prog (ge: Genv.t Asm.fundef unit):=
      forall b f,
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        wf_asm_function instr_size_1 f.

(*Lemma nextinstr_nf_pc: forall rs sz, nextinstr_nf rs sz PC = Val.offset_ptr (rs PC) sz.
Proof.
  unfold nextinstr_nf. simpl.
  intros. f_equalrewrite Asmgenproof0.nextinstr_pc. f_equal.
Qed. *)

Lemma nextinstr_rsp:
  forall rs sz,
    nextinstr rs sz RSP= rs RSP.
Proof.
  unfold nextinstr.
  intros; rewrite Pregmap.gso; congruence.
Qed.

Lemma nextinstr_nf_rsp:
  forall rs sz,
    nextinstr_nf rs sz RSP = rs RSP.
Proof.
  unfold nextinstr_nf.
  intros. rewrite nextinstr_rsp.
  rewrite Asmgenproof0.undef_regs_other; auto.
  simpl; intuition subst; congruence.
Qed.

    Lemma real_asm_inv_inv:
      forall (prog_no_rsp: asm_prog_no_rsp ge) (WF: wf_asm_prog ge) s1 t s2,
        (step instr_size_1) ge s1 t s2 ->
        real_asm_inv s1 ->
        real_asm_inv s2.
    Proof.
      intros prog_no_rsp WF s1 t s2 STEP INV; inv STEP.
      - destruct (stk_unrelated_instr i) eqn:INVAR.
        eapply exec_instr_invar_inv; eauto.
        eapply prog_no_rsp; eauto. eapply Asmgenproof0.find_instr_in; eauto.
        destruct i; simpl in INVAR; try congruence.
        + (* call_s *)
          simpl in H2. destr_in H2. inv H2. inv INV; constructor; simpl.
          * red. simpl. simpl_regs. destruct RSPPTR as (o & EQ & AL); simpl in *; rewrite EQ.
            simpl. eexists; split; eauto. apply align_Mptr_sub; auto.
          * red in BSTACKPERM; red; simpl in *.
            intros o k p. erewrite storev_perm; eauto. intro. erewrite storev_perm; eauto.
          * red in STOP; red; simpl in *. erewrite <- Mem.support_storev; eauto.
        + (* call_r *)
          simpl in H2. destr_in H2. inv H2. inv INV; constructor; simpl.
          * red. simpl. simpl_regs. destruct RSPPTR as (o & EQ & AL); simpl in *; rewrite EQ.
            simpl. eexists; split; eauto. apply align_Mptr_sub; auto.
          * red in BSTACKPERM; red; simpl in *.
            intros o k p. erewrite storev_perm; eauto. intro. erewrite storev_perm; eauto.
          * red in STOP; red; simpl in *. erewrite <- Mem.support_storev; eauto.
        + (* ret *)
          simpl in H2; repeat destr_in H2; inv INV; constructor; simpl.
          * red. simpl. simpl_regs. destruct RSPPTR as (o & EQ & AL); simpl in *; rewrite EQ.
            simpl. eexists; split; eauto. apply align_Mptr_add; auto.
          * red in BSTACKPERM; red; simpl in *.
            intros o k p. eauto.
          * red in STOP; red; simpl in *. eauto.
        + (* allocframe *)
          simpl in H2; repeat destr_in H2; inv INV; constructor; simpl.
          * red. simpl.
            (* simpl_regs. *)

            unfold nextinstr. rewrite Pregmap.gso. rewrite Pregmap.gss.
            destruct RSPPTR as (o & EQ & AL); simpl in *; rewrite EQ.
            simpl. eexists; split; eauto. apply align_Mptr_add_gen; auto.
            unfold Ptrofs.neg. apply div_unsigned_repr; auto. apply Z.divide_opp_r.
            unfold Ptrofs.sub. apply div_unsigned_repr; auto.
            apply Z.divide_sub_r.
            apply div_unsigned_repr; auto.
            transitivity 8. unfold Mptr. destr; simpl. exists 1; lia. exists 2; lia. apply align_divides. lia.
            apply align_Mptr_modulus.
            apply div_unsigned_repr; auto.
            apply align_size_chunk_divides.
            apply align_Mptr_modulus.
            apply align_Mptr_modulus.
            apply align_Mptr_modulus. congruence.
          * red in BSTACKPERM; red; simpl in *.
            intros o k p. erewrite storev_perm; eauto. intro. erewrite storev_perm; eauto.
          * red in STOP; red; simpl in *. erewrite <- Mem.support_storev; eauto.
        + (* freeframe *)
          simpl in H2; repeat destr_in H2; inv INV; constructor; simpl.
          * red. simpl.
            unfold nextinstr. rewrite Pregmap.gso. rewrite Pregmap.gss.
            (* simpl_regs. *)
            destruct RSPPTR as (o & EQ & AL); simpl in *; rewrite EQ.
            simpl. eexists; split; eauto. apply align_Mptr_add_gen; auto.
            unfold Ptrofs.sub. apply div_unsigned_repr; auto.
            apply Z.divide_sub_r.
            apply div_unsigned_repr; auto.
            transitivity 8. unfold Mptr. destr; simpl. exists 1; lia. exists 2; lia. apply align_divides. lia.
            apply align_Mptr_modulus.
            apply div_unsigned_repr; auto.
            apply align_size_chunk_divides.
            apply align_Mptr_modulus.
            apply align_Mptr_modulus. congruence.
          * red in BSTACKPERM; red; eauto.
          * red in STOP; red; eauto.
      - inv INV; constructor.
        + red in RSPPTR; red; simpl in *. unfold nextinstr_nf.
          (* repeat simpl_regs. *) rewrite nextinstr_rsp.
          rewrite Asmgenproof0.undef_regs_other.
          2: simpl; intuition subst; congruence.
          exploit wf_asm_builtin_not_PC; eauto.
          intros (NPC & NRSP & NRA).
          rewrite set_res_other; auto.
          rewrite Asmgenproof0.undef_regs_other.
          eauto. setoid_rewrite in_map_iff. intros r' (x & PREG & IN). subst.
          intro EQ. symmetry in EQ. apply preg_of_not_rsp in EQ. congruence.
        + red in BSTACKPERM; red. simpl in *. intros o k p.
          repeat erewrite (external_perm_stack _ _ _ _ _ _ _ _ _ _ _ H3); eauto.
           simpl. auto. red in STOP; simpl in STOP. unfold bstack. unfold stkblock.
           simpl. destruct STOP as (tl & st & STOP). rewrite STOP. split. auto. left. auto.
           simpl. auto. red in STOP; simpl in STOP. unfold bstack. unfold stkblock.
           simpl. destruct STOP as (tl & st & STOP). rewrite STOP. split. auto. left. auto.
        + red in STOP; red; simpl in *. destruct STOP as (tl & st & STOP).
          exploit external_call_stack; eauto. destr. intros.
          rewrite STOP in H4. simpl in H4. destruct st. eauto. eauto.
          intros. rewrite H4. eauto.
      - inv INV; constructor.
        + Opaque destroyed_at_call.
          red in RSPPTR; red; simpl in *. repeat simpl_regs.
          destruct RSPPTR as (o & EQ & AL); simpl in *. rewrite EQ.
          simpl. eexists; split; eauto. apply align_Mptr_add; auto.
        + red in BSTACKPERM; red. simpl in *. intros o k p.
          repeat erewrite (external_perm_stack _ _ _ _ _ _ _ _ _ _ _ H2); eauto.
           simpl. auto. red in STOP; simpl in STOP. unfold bstack. unfold stkblock.
           simpl. destruct STOP as (tl & st & STOP). rewrite STOP. split. auto. left. auto.
           simpl. auto. red in STOP; simpl in STOP. unfold bstack. unfold stkblock.
           simpl. destruct STOP as (tl & st & STOP). rewrite STOP. split. auto. left. auto.
        + red in STOP; red; simpl in *. destruct STOP as (tl & st & STOP).
          exploit external_call_stack; eauto. destr. intros.
          rewrite STOP in H3. simpl in H3. destruct st. eauto. eauto.
          intros. rewrite H3. eauto.
    Qed.

End INVARIANT.


(** Liveness analysis for region variables *)

Require Import Coqlib.
Require Import Maps.
Require Import Lattice.
Require Import Kildall.
Require Import Ordered.
Require FSetAVL.
Require Import Rusttypes Rustlight.
Require Import RustIR RustIRcfg.

(** Sets of regions *)

Module RegionSet := FSetAVL.Make(OrderedPositive).

(* A region [r] is live at a point [p] if there exists a path from [p]
  to some statement that uses a place whose type contains the region
  [r], and [r] is not redefined (e.g., by reassinging the variable
  whose type contains [r]). *)

Notation reg_live := RegionSet.add.
Notation reg_dead := RegionSet.remove.

Fixpoint reg_list_live (l: list origin) (rs: RegionSet.t) : RegionSet.t :=
  match l with
  | nil => rs
  | r :: l' =>
      (reg_list_live l' (reg_live r rs))
  end.

Fixpoint reg_list_dead (l: list origin) (rs: RegionSet.t) : RegionSet.t :=
  match l with
  | nil => rs
  | r :: l' =>
      (reg_list_dead l' (reg_dead r rs))
  end.

Definition reg_place_live (p: place) (rs: RegionSet.t) : RegionSet.t :=
  reg_list_live (origins_of_type (typeof_place p)) rs.

Fixpoint reg_pexpr_live (pe: pexpr) (rs: RegionSet.t) : RegionSet.t :=
  match pe with 
  | Eplace p _ 
  | Ecktag p _ 
  | Eref _ _ p _ => reg_place_live p rs
  | Eunop _ pe _ => reg_pexpr_live pe rs
  | Ebinop _ pe1 pe2 _ =>
      reg_pexpr_live pe2 (reg_pexpr_live pe1 rs)
  | _ => rs
  end.

Definition reg_expr_live (e: expr) (rs: RegionSet.t) : RegionSet.t :=
  match e with
  | Emoveplace p _ => reg_place_live p rs
  | Epure pe => reg_pexpr_live pe rs
  end.

Fixpoint reg_exprlis_live (l: list expr) (rs: RegionSet.t) : RegionSet.t :=
  match l with
  | nil => rs
  | e :: l' =>
      reg_exprlis_live l' (reg_expr_live e rs)
  end.

Definition reg_place_dead (p: place) (rs: RegionSet.t) : RegionSet.t :=
  match p with
  (* conservative kill: we only kill the regions whose place is a local *)
  | Plocal id ty => reg_list_dead (origins_of_type ty) rs
  | _ => rs
  end.

(* Transfer function *)
     
Definition transfer (f: function) (cfg: rustcfg) (pc: node) (after: RegionSet.t) : RegionSet.t :=
  match cfg ! pc with
  | None => RegionSet.empty
  | Some (Inop _) => after
  | Some (Icond e _ _) => reg_expr_live e after
  | Some Iend => after
  | Some (Isel sel _) =>
          match select_stmt f.(fn_body) sel with
          | None => RegionSet.empty
          | Some s =>
              match s with
              | Sassign p e
              | Sassign_variant p _ _ e
              | Sbox p e =>
                  reg_expr_live e (reg_place_dead p after)
              | Scall p _ l =>
                  reg_exprlis_live l (reg_place_dead p after)
              | Sdrop p =>
                  reg_place_live p after
              | Sreturn p =>
                  reg_place_live p after
              | _ => after
              end 
          end
  end.

Module RegionSetLat := LFSet(RegionSet).
Module DS := Backward_Dataflow_Solver(RegionSetLat)(NodeSetBackward).

Definition analyze (f: function) (cfg: rustcfg) : option (PMap.t RegionSet.t) :=
  DS.fixpoint cfg successors_instr (transfer f cfg).

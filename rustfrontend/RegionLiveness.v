
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

Fixpoint root_type_of_place (p: place) : type :=
  match p with
  | Plocal _ ty => ty
  | Pderef p' _ 
  | Pfield p' _ _
  | Pdowncast p' _ _ => root_type_of_place p'
  end.

Definition reg_place_live (p: place) (rs: RegionSet.t) : RegionSet.t :=
  reg_list_live (origins_of_type (root_type_of_place p)) rs.

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

(* Assigning a place may use some regions (if it is not a local) or
kill its regions (it is a local) *)
Definition reg_assign_place (p: place) (rs: RegionSet.t) : RegionSet.t :=
  match p with
  (* conservative kill: we only kill the regions whose place is a local *)
  | Plocal id ty => 
      reg_list_dead (origins_of_type ty) rs
  | _ => reg_list_live (origins_of_type (root_type_of_place p)) rs
  end.

(* Transfer function *)
     
Definition transfer (f: function) (cfg: rustcfg) (generic_regions: RegionSet.t) (pc: node) (after: RegionSet.t) : RegionSet.t :=
  match cfg ! pc with
  | None => generic_regions
  | Some (Inop _) => after
  | Some (Icond e _ _) => reg_expr_live e after
  | Some Iend => generic_regions
  | Some (Isel sel _) =>
          match select_stmt f.(fn_body) sel with
          | None => generic_regions
          | Some s =>
              match s with
              | Sassign p e
              | Sassign_variant p _ _ e
              | Sbox p e =>
                  reg_expr_live e (reg_assign_place p after)
              | Scall p _ l =>
                  reg_exprlis_live l (reg_assign_place p after)
              | Sdrop p =>
                  (*FIXME: We do not consider drop check for now, so there is no need to consider the regions in p live before this drop statement? Because (1) drop cannot access the region and (2) execution of drop depends on init-analysis *)
                  (* reg_place_live p after *)
                  after
              | Sreturn p =>
                  reg_place_live p generic_regions
              | _ => after
              end 
          end
  end.

Module RegionSetLat := LFSet(RegionSet).
Module DS := Backward_Dataflow_Solver(RegionSetLat)(NodeSetBackward).

Fixpoint live_generic_regions (l: list origin) : RegionSet.t := 
  match l with
  | nil => RegionSet.empty
  | r :: l' =>
      RegionSet.add r (live_generic_regions l')
  end.

Definition analyze (f: function) (cfg: rustcfg) : option (PMap.t RegionSet.t) :=
  (* All the generic regions are live at all points *)  
  let generic_regions := live_generic_regions f.(fn_generic_origins) in
  DS.fixpoint cfg successors_instr (transfer f cfg generic_regions).

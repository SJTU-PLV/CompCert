open Camlcoq
open BinNums
open Rustlight

(* let litNum = ref 0 *)

let dropglue_tbl = (Hashtbl.create 10 : (positive, bool) Hashtbl.t)

let union_tbl = (Hashtbl.create 20 : (positive, bool) Hashtbl.t)

let rec place_suffix = function
  | Plocal (id, _) ->
      extern_atom id
  | Pfield (p, fid, _) ->
      Printf.sprintf "%s__field__%s" (place_suffix p) (extern_atom fid)
  | Pderef (p, _) ->
      Printf.sprintf "deref__%s" (place_suffix p)
  | Pdowncast (p, fid, _) ->
      Printf.sprintf "%s__downcast__%s" (place_suffix p) (extern_atom fid)

let create_dropflag_ident (p: place) : positive =
  let name = Printf.sprintf "__dropflag_%s" (place_suffix p) in
  intern_string name

let create_dropglue_ident (a: positive) : positive =
  (* use the name of a in the end of drop in place *)
  let str = extern_atom a in
  let name = Printf.sprintf "__drop_in_place_%s" str in
  let id = intern_string name in
    Hashtbl.add dropglue_tbl id true;
  id

let is_dropglue_ident (id: positive) : bool =
  try
    Hashtbl.find dropglue_tbl id
  with Not_found -> false

  (* generate union id, tag field id and union field id (in struct) *)
let create_union_idents (a: positive) : (positive * positive) * positive =
  let str = extern_atom a in
  let union_name = Printf.sprintf "__union_of_%s" str in
  let tag_field = Printf.sprintf "__tag_of_%s" str in
  let body_field = Printf.sprintf "__body_of_%s" str in
  let union_id = intern_string union_name in
  let tag_id = intern_string tag_field in
  let body_id = intern_string body_field in
    Hashtbl.add union_tbl union_id true;
    Hashtbl.add union_tbl tag_id true;
    Hashtbl.add union_tbl body_id true;
  ((union_id, tag_id), body_id)

let malloc_id =
  intern_string "malloc"

let free_id =
  intern_string "free"

let param_id =
intern_string "dropglue_param"
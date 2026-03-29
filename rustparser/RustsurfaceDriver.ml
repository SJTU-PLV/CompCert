module I = RustsurfaceParser.MenhirInterpreter
module E = MenhirLib.ErrorReports
module L = MenhirLib.LexerUtil

let env checkpoint =
  match checkpoint with
  | I.HandlingError env ->
      env
  | _ ->
      assert false

(* [state checkpoint] extracts the number of the current state out of a
   checkpoint. *)

let state checkpoint : int =
  match I.top (env checkpoint) with
  | Some (I.Element (s, _, _, _)) ->
      I.number s
  | None ->
      (* Hmm... The parser is in its initial state. The incremental API
         currently lacks a way of finding out the number of the initial
         state. It is usually 0, so we return 0. This is unsatisfactory
         and should be fixed in the future. *)
      0

(* [show text (pos1, pos2)] displays a range of the input text [text]
   delimited by the positions [pos1] and [pos2]. *)

let show text positions =
  E.extract text positions
  |> E.sanitize
  |> E.compress
  |> E.shorten 20 (* max width 43 *)

(* [get text checkpoint i] extracts and shows the range of the input text that
   corresponds to the [i]-th stack cell. The top stack cell is numbered zero. *)

let get text checkpoint i =
  match I.get i (env checkpoint) with
  | Some (I.Element (_, _, pos1, pos2)) ->
      show text (pos1, pos2)
  | None ->
      (* The index is out of range. This should not happen if [$i]
         keywords are correctly inside the syntax error message
         database. The integer [i] should always be a valid offset
         into the known suffix of the stack. *)
      "???"

(* [succeed v] is invoked when the parser has succeeded and produced a
   semantic value [v]. In our setting, this cannot happen, since the
   table-based parser is invoked only when we know that there is a
   syntax error in the input file. *)

let succeed v = v

(* [fail text buffer checkpoint] is invoked when parser has encountered a
   syntax error. *)

let fail text buffer (checkpoint : _ I.checkpoint) =
  (* Indicate where in the input file the error occurred. *)
  let location = L.range (E.last buffer) in
  (* Show the tokens just before and just after the error. *)
  let indication = Format.sprintf "Syntax error %s.\n" (E.show (show text) buffer) in
  let message =
    try
      let message = RustsurfaceParserM.message (state checkpoint) in
      E.expand (get text checkpoint) message
    with Not_found ->
      "Please check the syntax near the highlighted tokens.\n"
  in
  (* Show these three components. *)
  Format.eprintf "%s%s%s%!" location indication message;
  exit 1

let report positions message =
  let location = L.range positions in
  Format.eprintf "%s%s\n%!" location message;
  exit 1

let parse filename =
  let text, lexbuf = L.read filename in
  (* Wrap the lexer and lexbuf together into a supplier, that is, a
     function of type [unit -> token * position * position]. *)
  let supplier = I.lexer_lexbuf_to_supplier RustsurfaceLexer.read lexbuf in
  (* Equip the supplier with a two-place buffer that records the positions
     of the last two tokens. This is useful when a syntax error occurs, as
     these are the token just before and just after the error. *)
  let buffer, supplier = E.wrap_supplier supplier in
  (* Fetch the parser's initial checkpoint. *)
  let open Lexing in
  let checkpoint = RustsurfaceParser.Incremental.prog_eof lexbuf.lex_curr_p in
  (* Run the parser. *)
  (* We do not handle [Lexer.Error] because we know that we will not
     encounter a lexical error during this second parsing run. *)
  try
    I.loop_handle succeed (fail text buffer) supplier checkpoint
  with
  | Rustsurface.Parse_error (pos1, pos2, message) ->
      report (pos1, pos2) message

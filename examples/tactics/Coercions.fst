module Coercions

open FStar.Tactics

(* let a : Type = true *)

(* let tm : term = `(2 + 1) *)

(* let basic : int = *)
(*   match tm with *)
(*   | Tv_App l _ -> 1 *)
(*   | _ -> 2 *)

(* let one () : option term = *)
(*   match tm with *)
(*   | Tv_App _ (x, _) -> Some x *)
(*   | _ -> None *)

(* let one' () : option term_view = *)
(*   match tm with *)
(*   | Tv_App _ (x, _) -> Some (inspect_ln x) *)
(*   | _ -> None *)

(* [> Currently, `l` has an unknown type, why? <] *)
(* let two_elab () : option term = *)
(*   match inspect_ln tm with *)
(*   | Tv_App a0 a1 -> *)
(*     begin match a0, a1 with *)
(*     | l, _ -> *)
(*         begin match inspect_ln l with *)
(*         | Tv_App _ (x, _) -> Some x *)
(*         | _ -> None *)
(*         end *)
(*     | uu -> (match uu with _ -> None) *)
(*     end *)
(*   | _ -> None *)

(* let two () : option term = *)
(*   match tm with *)
(*   | Tv_App l _ -> begin match l with *)
(*                   | Tv_App _ (x, _) -> Some x *)
(*                   | _ -> None *)
(*                   end *)
(*   | _ -> None *)

(* let _ = assert True by *)
(*         (print ("tm = "        ^ term_to_string tm); *)
(*          print ("one  = "      ^ (match one  ()      with | Some x -> term_to_string x | None -> "NONE?")); *)
(*          print ("one' = "      ^ (match one' ()      with | Some x -> term_to_string x | None -> "NONE?")); *)
(*          print ("two_elab  = " ^ (match two_elab ()  with | Some x -> term_to_string x | None -> "NONE?")); *)
(*          print ("two  = "      ^ (match two  ()      with | Some x -> term_to_string x | None -> "NONE?")); *)
(*          ()) *)

(* Nested patterns! *)
let test (tm:term) : option term =
  match tm with
  | Tv_App (Tv_App _ (x, _)) _ -> Some x
  | _ -> None

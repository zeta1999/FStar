module Antiquote

open FStar.Tactics

let _ = assert_by_tactic True
            (fun () -> let tm = (`(1 + `@(1))) in
                       let z = 16 in
                       let x = `16 in
                       let tm2 = `(1 + `@(z)) in
                       let tm3 = `(1 + `#((fun t -> t) x)) in
                       let tm4 = `(1 + `#((fun t -> t) x)) in
                       debug ("tm = " ^ term_to_string tm);
                       debug ("tm2 = " ^ term_to_string tm2);
                       debug ("tm3 = " ^ term_to_string tm3);
                       debug ("tm4 = " ^ term_to_string tm4);
                       let ty = tc tm in
                       debug ("ty = " ^ term_to_string ty);
                       let ty2 = tc tm2 in
                       debug ("ty2 = " ^ term_to_string ty2);
                       let ty3 = tc tm3 in
                       debug ("ty3 = " ^ term_to_string ty3);
                       let ty4 = tc tm4 in
                       debug ("ty4 = " ^ term_to_string ty4);
                       ())

(* Dynamic antiquotes *)
let _ = assert_by_tactic True
            (fun () -> let y = True in
                       let tm = `(False ==> `@y) in
                       debug ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())

let _ = assert_by_tactic True
            (fun () -> let y = bool in
                       let tm = `(int * (`@y)) in
                       debug ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())

let _ = assert_by_tactic True
            (fun () -> let y = 5 in
                       let tm = `((+) (`@y) 25) in
                       debug ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())


let _ = assert_by_tactic True
            (fun () -> let y = 5 in
                       let tm = `(fun z -> z + (`@y)) in
                       debug ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())

let _ = assert_by_tactic True
            (fun () -> let y = 5 in
                       let tm = `(if (`@y) = 22 then (`@y) - 1 else 1 - (`@y)) in
                       debug ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())

let _ = assert_by_tactic True
            (fun () -> let y = 5 in
                       let tm = `(match (`@y) with | 4 -> 1 + (`@y) | _ -> 99) in
                       debug ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())
(* // Dynamic *)



(* Static antiquotes *)
let _ = assert_by_tactic True
            (fun () -> let y = `True in
                       let tm = `(False ==> `#y) in
                       debug ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())

let _ = assert_by_tactic True
            (fun () -> let y = `bool in
                       let tm = `(int * (`#y)) in
                       debug ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())

let _ = assert_by_tactic True
            (fun () -> let y = `5 in
                       let tm = `((+) (`#y) 25) in
                       debug ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())


let _ = assert_by_tactic True
            (fun () -> let y = `5 in
                       let tm = `(fun z -> z + (`#y)) in
                       debug ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())

let _ = assert_by_tactic True
            (fun () -> let y = `5 in
                       let tm = `(if (`#y) = 22 then (`#y) - 1 else 1 - (`#y)) in
                       debug ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())

let _ = assert_by_tactic True
            (fun () -> let y = `5 in
                       let tm = `(match (`#y) with | 4 -> 1 + (`#y) | _ -> 99) in
                       debug ("tm = " ^ term_to_string tm);
                       let _ = tc tm in ())
(* // Static *)

// These two can extract, basically to mk_e_app (plus, [1; t])
let f (t : term) = `(1 + (`#t))
let f1 (t : term) = `(1 + (`#( (fun t -> t) t )))

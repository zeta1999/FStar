module Tes
open MiniParse.Spec.TEnum
open MiniParse.Tac.Impl

module T = FStar.Tactics

type test = | C1 | C2 | C3 | C4 

let f (x1: test) : Tot (bounded_u16 4) =
match x1 with
| C4 -> mk_u16 3 <: bounded_u16 4
| C3 -> mk_u16 2 <: bounded_u16 4
| C2 -> mk_u16 1 <: bounded_u16 4
| C1 -> mk_u16 0 <: bounded_u16 4
| _ -> mk_u16 3 <: bounded_u16 4

let f_inv (x2: bounded_u16 4) : Tot test =
  mk_if_t (bounded_u16_eq 4 x2 (mk_u16 0))
    (fun _ -> C1)
    (fun _ ->
      mk_if_t (bounded_u16_eq 4 x2 (mk_u16 1))
        (fun _ -> C2)
        (fun _ ->
           mk_if_t (bounded_u16_eq 4 x2 (mk_u16 2))
             (fun _ -> C3)
             (fun _ -> C4)
        )
    )

// #reset-options "--z3rlimit 1 --z3rlimit_factor 64 --z3seed 00"
#set-options "--hint_info"
#set-options "--tactics_info"
#set-options "--log_queries"

let f_smt : (test -> Tot (bounded_u16 4)) = _ by (T.exact (gen_synth_bounded' (`test)))

let f_tac : (test -> Tot (bounded_u16 4)) = _ by (T.with_policy T.Goal (fun _ -> T.exact_guard (gen_synth_bounded' (`test)); according_to T.Goal tconclude))

let g_smt : (bounded_u16 4 -> Tot test) =
  _ by (
    T.exact (invert_function' (`test) (`(bounded_u16 4)) (`(bounded_u16_eq 4)) (unfold_term (`f_tac)))
  )

let g_tac : (bounded_u16 4 -> Tot test) =
  _ by (
    T.with_policy T.Goal (fun () ->
      T.exact_guard
        (invert_function' (`test) (`(bounded_u16 4)) (`(bounded_u16_eq 4)) (unfold_term (`f_tac)));
      according_to T.Goal tconclude
    ))

#set-options "--debug Tes --debug_level Tac"

let u : parser_spec test =
  T.synth_by_tactic (fun () -> gen_enum_parser T.Goal (`test))

(*
let g () : Tot (squash (synth_inverse f f_inv)) = _ by (synth_inverse_forall_bounded_u16_solve ())

let h () : Tot unit =
  let f : (test -> Tot (bounded_u16 4)) = in
  let g : (bounded_u16 4 -> Tot test) = _ by (T.exact (invert_function' (`test) (`(bounded_u16 4)) (`(bounded_u16_eq 4)) (T.norm_term [delta; zeta] (quote f)))) in
  ()

(*

let pBenchMiniParseSize4Factor64Seed00SMT = T.synth_by_tactic (fun () -> gen_enum_parser T.Drop (`test))
let qBenchMiniParseSize4Factor64Seed00SMT = T.synth_by_tactic (fun () -> gen_parser_impl T.SMT)

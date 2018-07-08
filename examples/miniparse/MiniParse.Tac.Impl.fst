module MiniParse.Tac.Impl
include MiniParse.Tac.Base
include MiniParse.Impl.Combinators
include MiniParse.Impl.Int
include MiniParse.Impl.List
include MiniParse.Spec.TEnum

module T = FStar.Tactics
module L = FStar.List.Tot
module TS = MiniParse.Tac.Spec
module U32 = FStar.UInt32

inline_for_extraction
let mk_u32 (n: nat { n < 4294967296 } ) : Tot U32.t = U32.uint_to_t n

(* Generate the parser implementation from the parser specification *)

let rec gen_parser32' (env: T.env) (k: T.term) (t: T.term) (p: T.term) : T.Tac T.term =
  let (hd, tl) = app_head_tail p in
  if hd `T.term_eq` (`(parse_ret)) then T.mk_app (`(parse32_ret)) tl else
  if hd `T.term_eq` (`(parse_u8)) then (`(parse32_u8)) else
  if hd `T.term_eq` (`(and_then)) then match tl with
  | [(k, _); (t, _); (p, _); (k', _); (t', _); (p', _)] ->
    begin match T.inspect p' with
    | T.Tv_Abs bx body ->
      let p32 = gen_parser32' env k t p in
      let env' = T.push_binder env bx in
      let body' = gen_parser32' env' k' t' body in
      let p32' = T.pack (T.Tv_Abs bx body') in
      T.mk_app (`parse32_and_then) [
        (k, T.Q_Implicit);
        (t, T.Q_Implicit);
        (p, T.Q_Implicit);
        (p32, T.Q_Explicit);
        (k', T.Q_Implicit);
        (t', T.Q_Implicit);
        (p', T.Q_Explicit);
        (p32', T.Q_Explicit);
      ]
    | _ -> tfail "rhs part of and_then must be a lambda"
    end
  | _ -> tfail "Not enough arguments to and_then"
  else
  if hd `T.term_eq` (`(nondep_then)) then match tl with
  | [(k1, _); (t1, _); (p1, _); (k2, _); (t2, _); (p2, _)] ->
    let p1' = gen_parser32' env k1 t1 p1 in
    let p2' = gen_parser32' env k2 t2 p2 in
    T.mk_app (`(parse32_nondep_then)) [
      (k1, T.Q_Implicit);
      (t1, T.Q_Implicit);
      (p1, T.Q_Implicit);
      (p1', T.Q_Explicit);
      (k2, T.Q_Implicit);
      (t2, T.Q_Implicit);
      (p2, T.Q_Implicit);
      (p2', T.Q_Explicit);
    ]
  | _ -> tfail "Not enough arguments to nondep_then"
  else
  if hd `T.term_eq` (`(parse_synth))
  then match tl with
  | [(t1, _); t2; qp1; qf2; qg1] ->
    let (p1, _) = qp1 in
    let (f2, _) = qf2 in
    let bx = T.fresh_binder t1 in
    let x = T.pack (T.Tv_Var (T.bv_of_binder bx)) in
    let f2' = T.pack (T.Tv_Abs bx (T.mk_app f2 [x, T.Q_Explicit])) in
    let p1' = gen_parser32' env k t1 p1 in
    T.mk_app (`(parse32_synth)) [
      (t1, T.Q_Implicit);
      t2;
      (p1, T.Q_Implicit);
      (p1', T.Q_Explicit);
      qf2;
      (f2', T.Q_Explicit);
      qg1;
      ((`()), T.Q_Explicit);
    ]
  | _ -> tfail "Not enough arguments to synth"
  else
  if hd `T.term_eq` (`(parse_synth_weak))
  then match tl with
  | [(k, _); (t1, _); t2; qp1; qf2] ->
    let (p1, _) = qp1 in
    let (f2, _) = qf2 in
    let bx = T.fresh_binder t1 in
    let x = T.pack (T.Tv_Var (T.bv_of_binder bx)) in
    let f2' = T.pack (T.Tv_Abs bx (T.mk_app f2 [x, T.Q_Explicit])) in
    let p1' = gen_parser32' env k t1 p1 in
    T.mk_app (`(parse32_synth_weak)) [
      (k, T.Q_Implicit);
      (t1, T.Q_Implicit);
      t2;
      (p1, T.Q_Implicit);
      (p1', T.Q_Explicit);
      qf2;
      (f2', T.Q_Explicit);
    ]
  | _ -> tfail "Not enough arguments to synth_weak"
  else
  if hd `T.term_eq` (`parse_bounded_u8)
  then match tl with
  | [(b, _)] ->
    T.mk_app (`parse32_bounded_u8) [(b, T.Q_Explicit)]
  | _ -> tfail "not enough arguments to parse_bounded_u8"
  else
  if hd `T.term_eq` (`parse_filter)
  then match tl with
  | [(k, _); (t, _); (p, _); (f, _)] ->
    let bx = T.fresh_binder t in
    let x = T.pack (T.Tv_Var (T.bv_of_binder bx)) in
    let f' = T.pack (T.Tv_Abs bx (T.mk_app f [x, T.Q_Explicit])) in
    let p' = gen_parser32' env k t p in
    T.mk_app (`parse32_filter) [
      (k, T.Q_Implicit);
      (t, T.Q_Implicit);
      (p, T.Q_Implicit);
      (p', T.Q_Explicit);
      (f, T.Q_Explicit);
      (f', T.Q_Explicit);
    ]
  | _ -> tfail "Not enough arguments to parse_filter"
  else
  if hd `T.term_eq` (`(TS.package_parser))
  then match tl with
  | [qt; (pk, _)] ->
    let (hd', tl') = app_head_tail pk in
    if hd' `T.term_eq` (`(TS.mk_package))
    then match tl' with
    | [_; (p, _); _] ->
      gen_parser32' env k t p
    | _ -> tfail "Not enough arguments to mk_package"
    else begin match T.inspect hd with
    | T.Tv_FVar v ->
      let t' = T.norm_term_env env [iota] (T.mk_app (unfold_term hd') tl') in
      gen_parser32' env k t (T.mk_app hd [qt; (t', T.Q_Explicit)])
    | _ -> tfail "Unknown parser package"
    end
  | _ ->
    tfail "Not enough arguments to package_parser"
  else
  if hd `T.term_eq` (`parse_nlist)
  then match tl with
  | [(n, _); (t, _); (p, _)] ->
    let tv = T.inspect (T.norm_term_env env [delta; iota; zeta; primops] n) in
    begin match tv with
    | T.Tv_Const (T.C_Int _) ->
      let n' = T.mk_app (`(mk_u32)) [T.pack tv, T.Q_Explicit] in
      let p' = gen_parser32' env k t p in
      T.mk_app (`parse32_nlist) [
        (n, T.Q_Explicit);
        (n', T.Q_Explicit);
        (t, T.Q_Implicit);
        (p, T.Q_Implicit);
        (p', T.Q_Explicit);
      ]
    | _ -> tfail "parse_nlist: not an integer constant"
    end
  | _ -> tfail "Not enough arguments to parse_nlist"
  else
  if hd `T.term_eq` (`weaken)
  then match tl with
  | [(k', _); (t', _); (p', _)] ->
    let p32' = gen_parser32' env k' t' p' in
    T.mk_app (`parse32_weaken) [
      (k', T.Q_Implicit);
      (t', T.Q_Implicit);
      (p', T.Q_Implicit);
      (p32', T.Q_Explicit);
    ]
  | _ -> tfail "not enough arguments to weaken"
  else
  match T.inspect hd with
  | T.Tv_FVar v ->
    let t' = T.norm_term_env env [iota] (T.mk_app (unfold_term hd) tl) in
    gen_parser32' env k t t'
  | _ ->
    begin match T.inspect p with
    | T.Tv_Match cond [T.Pat_Constant T.C_True, tt; _, tf] ->
      (* ifthenelse: the second branch can be a wildcard or false *)
      let ctrue_t = T.mk_app (`cond_true) [cond, T.Q_Explicit] in
      let ctrue_b = T.fresh_binder_named "ctrue" ctrue_t in
      let ctrue_body = gen_parser32' env k t tt in
      let ctrue_p = T.pack (T.Tv_Abs ctrue_b tt) in
      let ctrue_p32 = T.pack (T.Tv_Abs ctrue_b ctrue_body) in
      let cfalse_t = T.mk_app (`cond_false) [cond, T.Q_Explicit] in
      let cfalse_b = T.fresh_binder_named "cfalse" cfalse_t in
      let cfalse_body = gen_parser32' env k t tf in
      let cfalse_p = T.pack (T.Tv_Abs cfalse_b tf) in
      let cfalse_p32 = T.pack (T.Tv_Abs cfalse_b cfalse_body) in
      T.mk_app (`parse32_ifthenelse) [
        (k, T.Q_Implicit);
        (t, T.Q_Implicit);
        (cond, T.Q_Explicit);
        (ctrue_p, T.Q_Explicit);
        (ctrue_p32, T.Q_Explicit);
        (cfalse_p, T.Q_Explicit);
        (cfalse_p32, T.Q_Explicit);
      ]
    | _ -> tfail "Unknown parser combinator"
    end

let p = parse_u8 `nondep_then` parse_ret 42

let gen_parser32_with_policy pol : T.Tac unit =
  T.set_guard_policy pol;
  let (hd, tl) = app_head_tail (T.cur_goal ()) in
  if hd `T.term_eq` (`parser32)
  then match tl with
  | [(k, _); (t, _); (p, _)] ->
    let env = T.cur_env () in
    let p32 = gen_parser32' env k t p in
    T.exact_guard p32;
    begin match pol with
    | T.SMT -> ()
    | _ ->
      tconclude_with [
        synth_inverse_forall_bounded_u8_solve;
        synth_inverse_forall_tenum_solve;
      ]
    end;
    T.print "gen_parser32 spits:";
    T.print (T.term_to_string p32)
  | _ -> tfail "Not enough arguments to gen_parser32"
  else tfail "Not a parser32 goal"

let gen_parser32 () : T.Tac unit = gen_parser32_with_policy T.Goal

let q : parser32 p = T.synth_by_tactic gen_parser32

let p' = p `nondep_then` parse_u8

// let p' = (parse_u8 `nondep_then` parse_ret 42) `nondep_then` parse_u8

#push-options "--print_implicits"

let q' : parser32 p' = T.synth_by_tactic gen_parser32

let r : parser int =
  parse_synth
    (parse_ret 42)
    (fun x -> x + 1)
    (fun x -> x - 1)

let r' : parser32 r = T.synth_by_tactic gen_parser32

let j : parser TS.t = TS.package_parser TS.p

let j32 : parser32 j = T.synth_by_tactic gen_parser32

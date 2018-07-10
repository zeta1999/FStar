module MiniParseExample
open MiniParse.Tac.Impl

module T = FStar.Tactics

#set-options "--no_smt"

let p = T.synth_by_tactic (fun () -> gen_enum_parser (`test))

let q = T.synth_by_tactic gen_parser32

#reset-options

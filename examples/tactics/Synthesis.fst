module Synthesis

open FStar.Tactics

#set-options "--__tactics_nbe"

let b = assert True by (fun () -> exact (`()); dump "B")

let a : unit = synth (fun () -> exact (`()); dump "A")

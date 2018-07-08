module MiniParseExample.Aux

module U8 = FStar.UInt8

module I16 = FStar.Int16
module Cast = FStar.Int.Cast

inline_for_extraction
let f (x: U8.t) (_: squash (~ ((x `U8.lt` 128uy) == true))) (y: U8.t) : Tot I16.t =
  Cast.uint8_to_int16 (x `U8.rem` 128uy) `I16.add` (Cast.uint8_to_int16 y `I16.mul` 128s)

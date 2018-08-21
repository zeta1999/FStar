module FStar.Monotonic.ManualHeap

open FStar.Preorder
open FStar.Classical

type st (a:Type) =
  | Unused : st a
  | Used   : a -> st a
  | Freed  : st a

private noeq type heap_rec = {
  next_addr: (x: nat);
  memory   : (x: nat) -> Tot (option (a:Type0 & rel:(option (preorder a)) & st a))
}

let heap = h:heap_rec{(forall (n:nat). n >= h.next_addr ==> None? (h.memory n))}

let equal h1 h2 =
  let _ = () in
  h1.next_addr = h2.next_addr /\
  FStar.FunctionalExtensionality.feq h1.memory h2.memory

let equal_extensional h1 h2 = ()

let emp = {
  next_addr = 0;
  memory    = (fun (r:nat) -> None)
}

private noeq type mref' (a:Type0) (rel:preorder a) :Type0 = {
  addr: nat;
  init: a;
}

let mref a rel = mref' a rel

let addr_of #a #rel r = r.addr

let compare_addrs #a #b #rel1 #rel2 r1 r2 = r1.addr = r2.addr

let contains #a #rel h r =
  let _ = () in
  Some? (h.memory r.addr) /\
  (let Some (| a1, pre_opt, v |) = h.memory r.addr in
   a == a1 /\ Some? pre_opt /\ Some?.v pre_opt == rel /\ Used? v)

let addr_unused_in n h = None? (h.memory n)

let addr_freed_in n h =
  match h.memory n with
  | Some (| _, _, Freed |) -> True
  | _ -> False

let not_addr_unused_in_nullptr h = ()

let unused_in #a #rel r h = addr_unused_in (addr_of r) h

let freed_in #a #rel r h =
  addr_freed_in (addr_of r) h

let sel_tot #a #rel h r =
  let Some (| _, _, Used x |) = h.memory r.addr in
  x

let sel #a #rel h r =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (h `contains` r) then
    sel_tot #a h r
  else r.init

let upd_tot' (#a: Type0) (#rel: preorder a) (h: heap) (r: mref a rel) (x: a) =
  { h with memory = (fun r' -> if r.addr = r'
                            then Some (| a, Some rel, Used x |)
                            else h.memory r') }

let upd_tot #a #rel h r x = upd_tot' h r x

let upd #a #rel h r x =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (h `contains` r)
  then upd_tot' h r x
  else
    if r.addr >= h.next_addr
    then
      { next_addr = r.addr + 1;
        memory    = (fun r' -> if r' = r.addr
                                 then Some (| a, Some rel, Used x |)
                                 else h.memory r') }
    else
      { h with memory = (fun r' -> if r' = r.addr
                                then Some (| a, Some rel, Used x |)
                                else h.memory r') }

let alloc #a rel h x =
  let r = { addr = h.next_addr; init = x } in
  r, { next_addr = r.addr + 1;
       memory    = (fun r' -> if r' = r.addr
                                then Some (| a, Some rel, Used x |)
                                else h.memory r') }

let free #a #rel h r =
  { h with memory = (fun r' -> if r' = r.addr then Some (| a, Some rel, Freed |) else h.memory r') }

(*
 * update of a well-typed mreference
 *)
private let lemma_upd_contains_test
  (#a:Type) (#rel:preorder a) (h0:heap) (r:mref a rel) (x:a)
  :Lemma (h0 `contains` r ==>
          (let h1 = upd h0 r x in
           (forall (b:Type) (rel:preorder b) (r':mref b rel). (h0 `contains` r' /\ addr_of r' = addr_of r) ==> sel h1 r' == x /\
           (forall (b:Type) (rel:preorder b) (r':mref b rel). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r')             /\
           (forall (b:Type) (rel:preorder b) (r':mref b rel). h0 `contains` r' <==> h1 `contains` r')                         /\
           (forall (b:Type) (rel:preorder b) (r':mref b rel). r' `unused_in` h0  <==> r' `unused_in` h1))))
  = ()

(*
 * update of a mreference that is mapped but not necessarily well-typed
 * we cannot prove that h0 `contains` r' ==> h1 `contains` r'
 * because consider that in h0 (r:mref a) contains (| b, y:b |),
 * and that (r':mref b) s.t. r'.addr = r.addr
 * in h0, r' is well-typed, but in h1 it's not
 *)
private let lemma_upd_contains_not_necessarily_well_typed_test
  (#a:Type) (#rel:preorder a) (h0:heap) (r:mref a rel) (x:a)
  :Lemma ((~ (r `unused_in` h0)) ==>
          (let h1 = upd h0 r x in
           h1 `contains` r /\
           (forall (b:Type) (#rel:preorder b) (r':mref b rel). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r')           /\
           (forall (b:Type) (#rel:preorder b) (r':mref b rel). (r'.addr <> r.addr /\ h0 `contains` r') ==> h1 `contains` r') /\
           (forall (b:Type) (#rel:preorder b) (r':mref b rel). r' `unused_in` h0 <==> r' `unused_in` h1)))
  = ()

(*
 * update of an unused mreference
 *)
private let lemma_upd_unused_test
  (#a:Type) (#rel:preorder a) (h0:heap) (r:mref a rel) (x:a)
  :Lemma (r `unused_in` h0 ==>
          (let h1 = upd h0 r x in
           h1 `contains` r /\
           (forall (b:Type) (rel:preorder b) (r':mref b rel). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
           (forall (b:Type) (rel:preorder b) (r':mref b rel). h0 `contains` r' ==> h1 `contains` r')             /\
           (forall (b:Type) (rel:preorder b) (r':mref b rel). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1))))
  = ()

(*
 * alloc and alloc_mm behaves just like upd of an unmapped mreference
 *)
private let lemma_alloc_test (#a:Type) (rel:preorder a) (h0:heap) (x:a)
  :Lemma (let (r, h1) = alloc rel h0 x in
          r `unused_in` h0 /\
          h1 `contains` r  /\
          (forall (b:Type) (rel:preorder b) (r':mref b rel). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
          (forall (b:Type) (rel:preorder b) (r':mref b rel). h0 `contains` r' ==> h1 `contains` r')             /\
          (forall (b:Type) (rel:preorder b) (r':mref b rel). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1)) /\
          True
          )
  = ()

private let lemma_free_mm_test (#a:Type) (rel:preorder a) (h0:heap) (r:mref a rel{h0 `contains` r})
  :Lemma (let h1 = free h0 r in
          r `freed_in` h1 /\
          (forall (b:Type) (rel:preorder b) (r':mref b rel). addr_of r' <> addr_of r ==>
                                  ((sel h0 r' == sel h1 r'                 /\
                                   (h0 `contains` r' <==> h1 `contains` r') /\
                                   (r' `unused_in` h0 <==> r' `unused_in` h1)))))
  = ()

private let lemma_alloc_fresh_test (#a:Type) (rel:preorder a) (h0:heap) (x:a)
  :Lemma (let r, h1 = alloc rel h0 x in
          fresh r h0 h1 /\ modifies Set.empty h0 h1)
  = ()

let lemma_ref_unused_iff_addr_unused #a #rel h r = ()
let lemma_ref_freed_iff_addr_freed #a #rel h r = ()
let lemma_contains_implies_used #a #rel h r = ()
let lemma_distinct_addrs_distinct_types #a #b #rel1 #rel2 h r1 r2 = ()
let lemma_distinct_addrs_distinct_preorders u = ()
let lemma_distinct_addrs_unused #a #b #rel1 #rel2 h r1 r2 = ()
let lemma_alloc #a rel h0 x =
  let r, h1 = alloc rel h0 x in
  let h1' = upd h0 r x in
  assert (equal h1 h1')
let lemma_free_sel #a #b #rel1 #rel2 h0 r1 r2 = ()
let lemma_free_contains #a #b #rel1 #rel2 h0 r1 r2 = ()
let lemma_free_unused #a #b #rel1 #rel2 h0 r1 r2 = ()
let lemma_free_not_contained #a #rel h r = ()
let lemma_free_addr_unused_in #a #rel h r n = ()
let lemma_sel_same_addr #a #rel h r1 r2 = ()
let lemma_sel_upd1 #a #rel h r1 x r2 = ()
let lemma_sel_upd2 #a #b #rel1 #rel2 h r1 r2 x = ()
let lemma_mref_injectivity = ()
let lemma_in_dom_emp #a #rel r = ()
let lemma_upd_contains #a #rel h r x = ()
let lemma_well_typed_upd_contains #a #b #rel1 #rel2 h r1 x r2 = ()
let lemma_unused_upd_contains #a #b #rel1 #rel2 h r1 x r2 = ()
let lemma_unused_upd_freed_in #a #b #rel1 #rel2 h r1 x r2 = ()
let lemma_upd_contains_different_addr #a #b #rel1 #rel2 h r1 x r2 = ()
let lemma_upd_unused #a #b #rel1 #rel2 h r1 x r2 = ()
let lemma_upd_freed  #a #b #rel1 #rel2 h r1 x r2 = ()
let lemma_contains_upd_modifies #a #rel h r x = ()
let lemma_unused_upd_modifies #a #rel h r x = ()

let lemma_sel_equals_sel_tot_for_contained_refs #a #rel h r = ()
let lemma_upd_equals_upd_tot_for_contained_refs #a #rel h r x = ()
let lemma_modifies_and_equal_dom_sel_diff_addr #a #rel s h0 h1 r = ()

let lemma_heap_equality_upd_same_addr #a #rel h r1 r2 x =
  assert (equal (upd h r1 x) (upd h r2 x))

let lemma_heap_equality_cancel_same_mref_upd #a #rel h r x y =
  let h0 = upd (upd h r x) r y in
  let h1 = upd h r y in
  assert (equal h0 h1)

let lemma_heap_equality_upd_with_sel #a #rel h r =
  let h' = upd h r (sel h r) in
  let Some (| _, _, _ |) = h.memory r.addr in
  assert (equal h h')

let lemma_heap_equality_commute_distinct_upds #a #b #rel_a #rel_b h r1 r2 x y =
  let h0 = upd (upd h r1 x) r2 y in
  let h1 = upd (upd h r2 y) r1 x in
  assert (equal h0 h1)

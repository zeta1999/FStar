
open Prims

let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)


let withenv = (fun c _50_40 -> (match (_50_40) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun _50_1 -> (match (_50_1) with
| (FStar_Util.Inl (_50_44), _50_47) -> begin
false
end
| _50_50 -> begin
true
end)) args))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let escape_null_name = (fun a -> if (a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = "_") then begin
(Prims.strcat a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText a.FStar_Absyn_Syntax.realname.FStar_Ident.idText)
end else begin
a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end)


let mk_typ_projector_name : FStar_Ident.lident  ->  FStar_Absyn_Syntax.btvdef  ->  Prims.string = (fun lid a -> (let _147_14 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (escape_null_name a))
in (FStar_All.pipe_left escape _147_14)))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Absyn_Syntax.bvvdef  ->  Prims.string = (fun lid a -> (

let a = (let _147_19 = (FStar_Absyn_Util.unmangle_field_name a.FStar_Absyn_Syntax.ppname)
in {FStar_Absyn_Syntax.ppname = _147_19; FStar_Absyn_Syntax.realname = a.FStar_Absyn_Syntax.realname})
in (let _147_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (escape_null_name a))
in (FStar_All.pipe_left escape _147_20))))


let primitive_projector_by_pos : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _50_62 -> (match (()) with
| () -> begin
(let _147_30 = (let _147_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _147_29 lid.FStar_Ident.str))
in (FStar_All.failwith _147_30))
end))
in (

let t = (FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _147_31 = (FStar_Absyn_Util.compress_typ t)
in _147_31.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _50_66) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(mk_typ_projector_name lid a.FStar_Absyn_Syntax.v)
end
| FStar_Util.Inr (x) -> begin
(mk_term_projector_name lid x.FStar_Absyn_Syntax.v)
end))
end
end
| _50_75 -> begin
(fail ())
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _147_37 = (let _147_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _147_36))
in (FStar_All.pipe_left escape _147_37)))


let mk_typ_projector : FStar_Ident.lident  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_ToSMT_Term.term = (fun lid a -> (let _147_43 = (let _147_42 = (mk_typ_projector_name lid a)
in ((_147_42), (FStar_ToSMT_Term.Arrow (((FStar_ToSMT_Term.Term_sort), (FStar_ToSMT_Term.Type_sort))))))
in (FStar_ToSMT_Term.mkFreeV _147_43)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_ToSMT_Term.term = (fun lid a -> (let _147_49 = (let _147_48 = (mk_term_projector_name lid a)
in ((_147_48), (FStar_ToSMT_Term.Arrow (((FStar_ToSMT_Term.Term_sort), (FStar_ToSMT_Term.Term_sort))))))
in (FStar_ToSMT_Term.mkFreeV _147_49)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_ToSMT_Term.term = (fun lid i -> (let _147_55 = (let _147_54 = (mk_term_projector_name_by_pos lid i)
in ((_147_54), (FStar_ToSMT_Term.Arrow (((FStar_ToSMT_Term.Term_sort), (FStar_ToSMT_Term.Term_sort))))))
in (FStar_ToSMT_Term.mkFreeV _147_55)))


let mk_data_tester = (fun env l x -> (FStar_ToSMT_Term.mk_tester (escape l.FStar_Ident.str) x))


type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  FStar_Ident.ident  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_ToSMT_Term.term; next_id : Prims.unit  ->  Prims.int}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "10")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _50_101 -> (match (()) with
| () -> begin
(let _147_159 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (let _147_158 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((_147_159), (_147_158))))
end))
in (

let scopes = (let _147_161 = (let _147_160 = (new_scope ())
in (_147_160)::[])
in (FStar_Util.mk_ref _147_161))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _147_165 = (FStar_ST.read scopes)
in (FStar_Util.find_map _147_165 (fun _50_109 -> (match (_50_109) with
| (names, _50_108) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_50_112) -> begin
(

let _50_114 = (FStar_Util.incr ctr)
in (let _147_168 = (let _147_167 = (let _147_166 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _147_166))
in (Prims.strcat "__" _147_167))
in (Prims.strcat y _147_168)))
end)
in (

let top_scope = (let _147_170 = (let _147_169 = (FStar_ST.read scopes)
in (FStar_List.hd _147_169))
in (FStar_All.pipe_left Prims.fst _147_170))
in (

let _50_118 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.strcat pp.FStar_Ident.idText (Prims.strcat "__" rn.FStar_Ident.idText))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _50_126 -> (match (()) with
| () -> begin
(

let _50_127 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _147_182 = (let _147_181 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _147_181))
in (FStar_Util.format2 "%s_%s" pfx _147_182)))
in (

let string_const = (fun s -> (match ((let _147_186 = (FStar_ST.read scopes)
in (FStar_Util.find_map _147_186 (fun _50_136 -> (match (_50_136) with
| (_50_134, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _147_187 = (FStar_ToSMT_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxString _147_187))
in (

let top_scope = (let _147_189 = (let _147_188 = (FStar_ST.read scopes)
in (FStar_List.hd _147_188))
in (FStar_All.pipe_left Prims.snd _147_189))
in (

let _50_143 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _50_146 -> (match (()) with
| () -> begin
(let _147_194 = (let _147_193 = (new_scope ())
in (let _147_192 = (FStar_ST.read scopes)
in (_147_193)::_147_192))
in (FStar_ST.op_Colon_Equals scopes _147_194))
end))
in (

let pop = (fun _50_148 -> (match (()) with
| () -> begin
(let _147_198 = (let _147_197 = (FStar_ST.read scopes)
in (FStar_List.tl _147_197))
in (FStar_ST.op_Colon_Equals scopes _147_198))
end))
in (

let mark = (fun _50_150 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _50_152 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _50_154 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(

let _50_167 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _50_172 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl))))
end
| _50_175 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))


let unmangle = (fun x -> (let _147_214 = (let _147_213 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.ppname)
in (let _147_212 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.realname)
in ((_147_213), (_147_212))))
in (FStar_Absyn_Util.mkbvd _147_214)))


type binding =
| Binding_var of (FStar_Absyn_Syntax.bvvdef * FStar_ToSMT_Term.term)
| Binding_tvar of (FStar_Absyn_Syntax.btvdef * FStar_ToSMT_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option)
| Binding_ftvar of (FStar_Ident.lident * Prims.string * FStar_ToSMT_Term.term Prims.option)


let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_tvar = (fun _discr_ -> (match (_discr_) with
| Binding_tvar (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_fvar = (fun _discr_ -> (match (_discr_) with
| Binding_fvar (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_ftvar = (fun _discr_ -> (match (_discr_) with
| Binding_ftvar (_) -> begin
true
end
| _ -> begin
false
end))


let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_50_180) -> begin
_50_180
end))


let ___Binding_tvar____0 = (fun projectee -> (match (projectee) with
| Binding_tvar (_50_183) -> begin
_50_183
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_50_186) -> begin
_50_186
end))


let ___Binding_ftvar____0 = (fun projectee -> (match (projectee) with
| Binding_ftvar (_50_189) -> begin
_50_189
end))


let binder_of_eithervar = (fun v -> ((v), (None)))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_Tc_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_ToSMT_Term.sort Prims.list * FStar_ToSMT_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _147_300 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _50_2 -> (match (_50_2) with
| Binding_var (x, t) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Binding_tvar (a, t) -> begin
(FStar_Absyn_Print.strBvd a)
end
| Binding_fvar (l, s, t, _50_214) -> begin
(FStar_Absyn_Print.sli l)
end
| Binding_ftvar (l, s, t) -> begin
(FStar_Absyn_Print.sli l)
end))))
in (FStar_All.pipe_right _147_300 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string Prims.option = (fun env t -> if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _147_310 = (FStar_Absyn_Print.typ_to_string t)
in Some (_147_310))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_ToSMT_Term.sort  ->  (Prims.string * FStar_ToSMT_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _147_315 = (FStar_ToSMT_Term.mkFreeV ((xsym), (s)))
in ((xsym), (_147_315)))))


let gen_term_var : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (let _147_320 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _147_320))
in (

let y = (FStar_ToSMT_Term.mkFreeV ((ysym), (FStar_ToSMT_Term.Term_sort)))
in ((ysym), (y), ((

let _50_233 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = _50_233.tcenv; warn = _50_233.warn; cache = _50_233.cache; nolabels = _50_233.nolabels; use_zfuel_name = _50_233.use_zfuel_name; encode_non_total_function_typ = _50_233.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (

let y = (FStar_ToSMT_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _50_239 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _50_239.depth; tcenv = _50_239.tcenv; warn = _50_239.warn; cache = _50_239.cache; nolabels = _50_239.nolabels; use_zfuel_name = _50_239.use_zfuel_name; encode_non_total_function_typ = _50_239.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_ToSMT_Term.term  ->  env_t = (fun env x t -> (

let _50_244 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = _50_244.depth; tcenv = _50_244.tcenv; warn = _50_244.warn; cache = _50_244.cache; nolabels = _50_244.nolabels; use_zfuel_name = _50_244.use_zfuel_name; encode_non_total_function_typ = _50_244.encode_non_total_function_typ}))


let lookup_term_var = (fun env a -> (match ((lookup_binding env (fun _50_3 -> (match (_50_3) with
| Binding_var (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (((b), (t)))
end
| _50_254 -> begin
None
end)))) with
| None -> begin
(let _147_335 = (let _147_334 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound term variable not found: %s" _147_334))
in (FStar_All.failwith _147_335))
end
| Some (b, t) -> begin
t
end))


let gen_typ_var : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (let _147_340 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@a" _147_340))
in (

let y = (FStar_ToSMT_Term.mkFreeV ((ysym), (FStar_ToSMT_Term.Type_sort)))
in ((ysym), (y), ((

let _50_264 = env
in {bindings = (Binding_tvar (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = _50_264.tcenv; warn = _50_264.warn; cache = _50_264.cache; nolabels = _50_264.nolabels; use_zfuel_name = _50_264.use_zfuel_name; encode_non_total_function_typ = _50_264.encode_non_total_function_typ}))))))


let new_typ_constant : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (

let y = (FStar_ToSMT_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _50_270 = env
in {bindings = (Binding_tvar (((x), (y))))::env.bindings; depth = _50_270.depth; tcenv = _50_270.tcenv; warn = _50_270.warn; cache = _50_270.cache; nolabels = _50_270.nolabels; use_zfuel_name = _50_270.use_zfuel_name; encode_non_total_function_typ = _50_270.encode_non_total_function_typ}))))))


let push_typ_var : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_ToSMT_Term.term  ->  env_t = (fun env x t -> (

let _50_275 = env
in {bindings = (Binding_tvar (((x), (t))))::env.bindings; depth = _50_275.depth; tcenv = _50_275.tcenv; warn = _50_275.warn; cache = _50_275.cache; nolabels = _50_275.nolabels; use_zfuel_name = _50_275.use_zfuel_name; encode_non_total_function_typ = _50_275.encode_non_total_function_typ}))


let lookup_typ_var = (fun env a -> (match ((lookup_binding env (fun _50_4 -> (match (_50_4) with
| Binding_tvar (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (((b), (t)))
end
| _50_285 -> begin
None
end)))) with
| None -> begin
(let _147_355 = (let _147_354 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound type variable not found: %s" _147_354))
in (FStar_All.failwith _147_355))
end
| Some (b, t) -> begin
t
end))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _147_366 = (

let _50_295 = env
in (let _147_365 = (let _147_364 = (let _147_363 = (let _147_362 = (let _147_361 = (FStar_ToSMT_Term.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _147_360 -> Some (_147_360)) _147_361))
in ((x), (fname), (_147_362), (None)))
in Binding_fvar (_147_363))
in (_147_364)::env.bindings)
in {bindings = _147_365; depth = _50_295.depth; tcenv = _50_295.tcenv; warn = _50_295.warn; cache = _50_295.cache; nolabels = _50_295.nolabels; use_zfuel_name = _50_295.use_zfuel_name; encode_non_total_function_typ = _50_295.encode_non_total_function_typ}))
in ((fname), (ftok), (_147_366))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _50_5 -> (match (_50_5) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| _50_307 -> begin
None
end))))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _147_377 = (let _147_376 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Name not found: %s" _147_376))
in (FStar_All.failwith _147_377))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _50_317 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = _50_317.depth; tcenv = _50_317.tcenv; warn = _50_317.warn; cache = _50_317.cache; nolabels = _50_317.nolabels; use_zfuel_name = _50_317.use_zfuel_name; encode_non_total_function_typ = _50_317.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _50_326 = (lookup_lid env x)
in (match (_50_326) with
| (t1, t2, _50_325) -> begin
(

let t3 = (let _147_394 = (let _147_393 = (let _147_392 = (FStar_ToSMT_Term.mkApp (("ZFuel"), ([])))
in (_147_392)::[])
in ((f), (_147_393)))
in (FStar_ToSMT_Term.mkApp _147_394))
in (

let _50_328 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = _50_328.depth; tcenv = _50_328.tcenv; warn = _50_328.warn; cache = _50_328.cache; nolabels = _50_328.nolabels; use_zfuel_name = _50_328.use_zfuel_name; encode_non_total_function_typ = _50_328.encode_non_total_function_typ}))
end)))


let lookup_free_var = (fun env a -> (

let _50_335 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_50_335) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
f
end
| _50_339 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (_50_343, (fuel)::[]) -> begin
if (let _147_398 = (let _147_397 = (FStar_ToSMT_Term.fv_of_term fuel)
in (FStar_All.pipe_right _147_397 Prims.fst))
in (FStar_Util.starts_with _147_398 "fuel")) then begin
(let _147_399 = (FStar_ToSMT_Term.mkFreeV ((name), (FStar_ToSMT_Term.Term_sort)))
in (FStar_ToSMT_Term.mk_ApplyEF _147_399 fuel))
end else begin
t
end
end
| _50_349 -> begin
t
end)
end
| _50_351 -> begin
(let _147_401 = (let _147_400 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _147_400))
in (FStar_All.failwith _147_401))
end)
end)
end)))


let lookup_free_var_name = (fun env a -> (

let _50_359 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_50_359) with
| (x, _50_356, _50_358) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _50_365 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_50_365) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (g, zf); FStar_ToSMT_Term.hash = _50_369; FStar_ToSMT_Term.freevars = _50_367}) when env.use_zfuel_name -> begin
((g), (zf))
end
| _50_377 -> begin
(match (sym) with
| None -> begin
((FStar_ToSMT_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| _50_387 -> begin
((FStar_ToSMT_Term.Var (name)), ([]))
end)
end)
end)
end)))


let new_typ_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _147_416 = (

let _50_392 = env
in (let _147_415 = (let _147_414 = (let _147_413 = (let _147_412 = (let _147_411 = (FStar_ToSMT_Term.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _147_410 -> Some (_147_410)) _147_411))
in ((x), (fname), (_147_412)))
in Binding_ftvar (_147_413))
in (_147_414)::env.bindings)
in {bindings = _147_415; depth = _50_392.depth; tcenv = _50_392.tcenv; warn = _50_392.warn; cache = _50_392.cache; nolabels = _50_392.nolabels; use_zfuel_name = _50_392.use_zfuel_name; encode_non_total_function_typ = _50_392.encode_non_total_function_typ}))
in ((fname), (ftok), (_147_416))))))


let lookup_tlid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option) = (fun env a -> (match ((lookup_binding env (fun _50_6 -> (match (_50_6) with
| Binding_ftvar (b, t1, t2) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2)))
end
| _50_403 -> begin
None
end)))) with
| None -> begin
(let _147_423 = (let _147_422 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Type name not found: %s" _147_422))
in (FStar_All.failwith _147_423))
end
| Some (s) -> begin
s
end))


let push_free_tvar : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _50_411 = env
in {bindings = (Binding_ftvar (((x), (fname), (ftok))))::env.bindings; depth = _50_411.depth; tcenv = _50_411.tcenv; warn = _50_411.warn; cache = _50_411.cache; nolabels = _50_411.nolabels; use_zfuel_name = _50_411.use_zfuel_name; encode_non_total_function_typ = _50_411.encode_non_total_function_typ}))


let lookup_free_tvar = (fun env a -> (match ((let _147_434 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _147_434 Prims.snd))) with
| None -> begin
(let _147_436 = (let _147_435 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Type name not found: %s" _147_435))
in (FStar_All.failwith _147_436))
end
| Some (t) -> begin
t
end))


let lookup_free_tvar_name = (fun env a -> (let _147_439 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _147_439 Prims.fst)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _50_7 -> (match (_50_7) with
| (Binding_fvar (_, nm', tok, _)) | (Binding_ftvar (_, nm', tok)) when (nm = nm') -> begin
tok
end
| _50_436 -> begin
None
end))))


let mkForall_fuel' = (fun n _50_441 -> (match (_50_441) with
| (pats, vars, body) -> begin
(

let fallback = (fun _50_443 -> (match (()) with
| () -> begin
(FStar_ToSMT_Term.mkForall ((pats), (vars), (body)))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _50_446 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_50_446) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var ("HasType"), args) -> begin
(FStar_ToSMT_Term.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| _50_456 -> begin
p
end)))))
in (

let pats = (FStar_List.map add_fuel pats)
in (

let body = (match (body.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, (guard)::(body')::[]) -> begin
(

let guard = (match (guard.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.And, guards) -> begin
(let _147_452 = (add_fuel guards)
in (FStar_ToSMT_Term.mk_and_l _147_452))
end
| _50_469 -> begin
(let _147_453 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _147_453 FStar_List.hd))
end)
in (FStar_ToSMT_Term.mkImp ((guard), (body'))))
end
| _50_472 -> begin
body
end)
in (

let vars = (((fsym), (FStar_ToSMT_Term.Fuel_sort)))::vars
in (FStar_ToSMT_Term.mkForall ((pats), (vars), (body)))))))
end))
end)
end))


let mkForall_fuel : (FStar_ToSMT_Term.pat Prims.list Prims.list * FStar_ToSMT_Term.fvs * FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term = (mkForall_fuel' (Prims.parse_int "1"))


let head_normal : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun env t -> (

let t = (FStar_Absyn_Util.unmeta_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_refine (_)) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| (FStar_Absyn_Syntax.Typ_const (v)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (v); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _147_459 = (FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _147_459 FStar_Option.isNone))
end
| _50_510 -> begin
false
end)))


let whnf : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.DeltaHard)::[]) env.tcenv t)
end)


let whnf_e : env_t  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp = (fun env e -> (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.WHNF)::[]) env.tcenv e))


let norm_t : env_t  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env.tcenv t))


let norm_k : env_t  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun env k -> (FStar_Tc_Normalize.normalize_kind env.tcenv k))


let trivial_post : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun t -> (let _147_481 = (let _147_480 = (let _147_478 = (FStar_Absyn_Syntax.null_v_binder t)
in (_147_478)::[])
in (let _147_479 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in ((_147_480), (_147_479))))
in (FStar_Absyn_Syntax.mk_Typ_lam _147_481 None t.FStar_Absyn_Syntax.pos)))


let mk_ApplyE : FStar_ToSMT_Term.term  ->  (Prims.string * FStar_ToSMT_Term.sort) Prims.list  ->  FStar_ToSMT_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _147_488 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyET out _147_488))
end
| FStar_ToSMT_Term.Fuel_sort -> begin
(let _147_489 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEF out _147_489))
end
| _50_527 -> begin
(let _147_490 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEE out _147_490))
end)) e)))


let mk_ApplyE_args : FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list  ->  FStar_ToSMT_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out arg -> (match (arg) with
| FStar_Util.Inl (t) -> begin
(FStar_ToSMT_Term.mk_ApplyET out t)
end
| FStar_Util.Inr (e) -> begin
(FStar_ToSMT_Term.mk_ApplyEE out e)
end)) e)))


let mk_ApplyT : FStar_ToSMT_Term.term  ->  (Prims.string * FStar_ToSMT_Term.sort) Prims.list  ->  FStar_ToSMT_Term.term = (fun t vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _147_503 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTT out _147_503))
end
| _50_542 -> begin
(let _147_504 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTE out _147_504))
end)) t)))


let mk_ApplyT_args : FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list  ->  FStar_ToSMT_Term.term = (fun t args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out arg -> (match (arg) with
| FStar_Util.Inl (t) -> begin
(FStar_ToSMT_Term.mk_ApplyTT out t)
end
| FStar_Util.Inr (e) -> begin
(FStar_ToSMT_Term.mk_ApplyTE out e)
end)) t)))


let is_app : FStar_ToSMT_Term.op  ->  Prims.bool = (fun _50_8 -> (match (_50_8) with
| (FStar_ToSMT_Term.Var ("ApplyTT")) | (FStar_ToSMT_Term.Var ("ApplyTE")) | (FStar_ToSMT_Term.Var ("ApplyET")) | (FStar_ToSMT_Term.Var ("ApplyEE")) -> begin
true
end
| _50_561 -> begin
false
end))


let is_eta : env_t  ->  FStar_ToSMT_Term.fv Prims.list  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_ToSMT_Term.tm), (xs))) with
| (FStar_ToSMT_Term.App (app, (f)::({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.FreeV (y); FStar_ToSMT_Term.hash = _50_572; FStar_ToSMT_Term.freevars = _50_570})::[]), (x)::xs) when ((is_app app) && (FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var (f), args), _50_590) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (fv) -> begin
(FStar_ToSMT_Term.fv_eq fv v)
end
| _50_597 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_50_599, []) -> begin
(

let fvs = (FStar_ToSMT_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_ToSMT_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _50_605 -> begin
None
end))
in (aux t (FStar_List.rev vars))))


type label =
(FStar_ToSMT_Term.fv * Prims.string * FStar_Range.range)


type labels =
label Prims.list


type pattern =
{pat_vars : (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t); guard : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term; projections : FStar_ToSMT_Term.term  ->  (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.term) Prims.list}


let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))


exception Let_rec_unencodeable


let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable (_) -> begin
true
end
| _ -> begin
false
end))


let constructor_string_of_int_qualifier : (FStar_Const.signedness * FStar_Const.width)  ->  Prims.string = (fun _50_9 -> (match (_50_9) with
| (FStar_Const.Unsigned, FStar_Const.Int8) -> begin
"FStar.UInt8.UInt8"
end
| (FStar_Const.Signed, FStar_Const.Int8) -> begin
"FStar.Int8.Int8"
end
| (FStar_Const.Unsigned, FStar_Const.Int16) -> begin
"FStar.UInt16.UInt16"
end
| (FStar_Const.Signed, FStar_Const.Int16) -> begin
"FStar.Int16.Int16"
end
| (FStar_Const.Unsigned, FStar_Const.Int32) -> begin
"FStar.UInt32.UInt32"
end
| (FStar_Const.Signed, FStar_Const.Int32) -> begin
"FStar.Int32.Int32"
end
| (FStar_Const.Unsigned, FStar_Const.Int64) -> begin
"FStar.UInt64.UInt64"
end
| (FStar_Const.Signed, FStar_Const.Int64) -> begin
"FStar.Int64.Int64"
end))


let encode_const : FStar_Const.sconst  ->  FStar_ToSMT_Term.term = (fun _50_10 -> (match (_50_10) with
| FStar_Const.Const_unit -> begin
FStar_ToSMT_Term.mk_Term_unit
end
| FStar_Const.Const_bool (true) -> begin
(FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
end
| FStar_Const.Const_bool (false) -> begin
(FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkFalse)
end
| FStar_Const.Const_char (c) -> begin
(let _147_565 = (let _147_564 = (let _147_563 = (let _147_562 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_ToSMT_Term.boxInt _147_562))
in (_147_563)::[])
in (("FStar.Char.Char"), (_147_564)))
in (FStar_ToSMT_Term.mkApp _147_565))
end
| FStar_Const.Const_int (i, None) -> begin
(let _147_566 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _147_566))
end
| FStar_Const.Const_int (i, Some (q)) -> begin
(let _147_570 = (let _147_569 = (let _147_568 = (let _147_567 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _147_567))
in (_147_568)::[])
in (((constructor_string_of_int_qualifier q)), (_147_569)))
in (FStar_ToSMT_Term.mkApp _147_570))
end
| FStar_Const.Const_string (bytes, _50_655) -> begin
(let _147_571 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _147_571))
end
| c -> begin
(let _147_573 = (let _147_572 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s\n" _147_572))
in (FStar_All.failwith _147_573))
end))


let as_function_typ : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_50_666) -> begin
t
end
| FStar_Absyn_Syntax.Typ_refine (_50_669) -> begin
(let _147_582 = (FStar_Absyn_Util.unrefine t)
in (aux true _147_582))
end
| _50_672 -> begin
if norm then begin
(let _147_583 = (whnf env t)
in (aux false _147_583))
end else begin
(let _147_586 = (let _147_585 = (FStar_Range.string_of_range t0.FStar_Absyn_Syntax.pos)
in (let _147_584 = (FStar_Absyn_Print.typ_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _147_585 _147_584)))
in (FStar_All.failwith _147_586))
end
end)))
in (aux true t0)))


let rec encode_knd_term : FStar_Absyn_Syntax.knd  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun k env -> (match ((let _147_623 = (FStar_Absyn_Util.compress_kind k)
in _147_623.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
((FStar_ToSMT_Term.mk_Kind_type), ([]))
end
| FStar_Absyn_Syntax.Kind_abbrev (_50_677, k0) -> begin
(

let _50_681 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _147_625 = (FStar_Absyn_Print.kind_to_string k)
in (let _147_624 = (FStar_Absyn_Print.kind_to_string k0)
in (FStar_Util.print2 "Encoding kind abbrev %s, expanded to %s\n" _147_625 _147_624)))
end else begin
()
end
in (encode_knd_term k0 env))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, _50_685) -> begin
(let _147_627 = (let _147_626 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Kind_uvar _147_626))
in ((_147_627), ([])))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, kbody) -> begin
(

let tsym = (let _147_628 = (varops.fresh "t")
in ((_147_628), (FStar_ToSMT_Term.Type_sort)))
in (

let t = (FStar_ToSMT_Term.mkFreeV tsym)
in (

let _50_700 = (encode_binders None bs env)
in (match (_50_700) with
| (vars, guards, env', decls, _50_699) -> begin
(

let app = (mk_ApplyT t vars)
in (

let _50_704 = (encode_knd kbody env' app)
in (match (_50_704) with
| (kbody, decls') -> begin
(

let rec aux = (fun app vars guards -> (match (((vars), (guards))) with
| ([], []) -> begin
kbody
end
| ((x)::vars, (g)::guards) -> begin
(

let app = (mk_ApplyT app ((x)::[]))
in (

let body = (aux app vars guards)
in (

let body = (match (vars) with
| [] -> begin
body
end
| _50_723 -> begin
(let _147_637 = (let _147_636 = (let _147_635 = (FStar_ToSMT_Term.mk_PreKind app)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _147_635))
in ((_147_636), (body)))
in (FStar_ToSMT_Term.mkAnd _147_637))
end)
in (let _147_639 = (let _147_638 = (FStar_ToSMT_Term.mkImp ((g), (body)))
in ((((app)::[])::[]), ((x)::[]), (_147_638)))
in (FStar_ToSMT_Term.mkForall _147_639)))))
end
| _50_726 -> begin
(FStar_All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (

let k_interp = (aux t vars guards)
in (

let cvars = (let _147_641 = (FStar_ToSMT_Term.free_variables k_interp)
in (FStar_All.pipe_right _147_641 (FStar_List.filter (fun _50_731 -> (match (_50_731) with
| (x, _50_730) -> begin
(x <> (Prims.fst tsym))
end)))))
in (

let tkey = (FStar_ToSMT_Term.mkForall (([]), ((tsym)::cvars), (k_interp)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (k', sorts, _50_737) -> begin
(let _147_644 = (let _147_643 = (let _147_642 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in ((k'), (_147_642)))
in (FStar_ToSMT_Term.mkApp _147_643))
in ((_147_644), ([])))
end
| None -> begin
(

let ksym = (varops.fresh "Kind_arrow")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _147_645 = (FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_147_645))
end else begin
None
end
in (

let kdecl = FStar_ToSMT_Term.DeclFun (((ksym), (cvar_sorts), (FStar_ToSMT_Term.Kind_sort), (caption)))
in (

let k = (let _147_647 = (let _147_646 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((ksym), (_147_646)))
in (FStar_ToSMT_Term.mkApp _147_647))
in (

let t_has_k = (FStar_ToSMT_Term.mk_HasKind t k)
in (

let k_interp = (let _147_656 = (let _147_655 = (let _147_654 = (let _147_653 = (let _147_652 = (let _147_651 = (let _147_650 = (let _147_649 = (let _147_648 = (FStar_ToSMT_Term.mk_PreKind t)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _147_648))
in ((_147_649), (k_interp)))
in (FStar_ToSMT_Term.mkAnd _147_650))
in ((t_has_k), (_147_651)))
in (FStar_ToSMT_Term.mkIff _147_652))
in ((((t_has_k)::[])::[]), ((tsym)::cvars), (_147_653)))
in (FStar_ToSMT_Term.mkForall _147_654))
in ((_147_655), (Some ((Prims.strcat ksym " interpretation")))))
in FStar_ToSMT_Term.Assume (_147_656))
in (

let k_decls = (FStar_List.append decls (FStar_List.append decls' ((kdecl)::(k_interp)::[])))
in (

let _50_749 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash ((ksym), (cvar_sorts), (k_decls)))
in ((k), (k_decls)))))))))))
end)))))
end)))
end))))
end
| _50_752 -> begin
(let _147_658 = (let _147_657 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.format1 "Unknown kind: %s" _147_657))
in (FStar_All.failwith _147_658))
end))
and encode_knd : FStar_Absyn_Syntax.knd  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decl Prims.list) = (fun k env t -> (

let _50_758 = (encode_knd_term k env)
in (match (_50_758) with
| (k, decls) -> begin
(let _147_662 = (FStar_ToSMT_Term.mk_HasKind t k)
in ((_147_662), (decls)))
end)))
and encode_binders : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.binders  ->  env_t  ->  (FStar_ToSMT_Term.fv Prims.list * FStar_ToSMT_Term.term Prims.list * env_t * FStar_ToSMT_Term.decls_t * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list) = (fun fuel_opt bs env -> (

let _50_762 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _147_666 = (FStar_Absyn_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _147_666))
end else begin
()
end
in (

let _50_812 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _50_769 b -> (match (_50_769) with
| (vars, guards, env, decls, names) -> begin
(

let _50_806 = (match ((Prims.fst b)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.v = a; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _50_772}) -> begin
(

let a = (unmangle a)
in (

let _50_781 = (gen_typ_var env a)
in (match (_50_781) with
| (aasym, aa, env') -> begin
(

let _50_782 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _147_670 = (FStar_Absyn_Print.strBvd a)
in (let _147_669 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print3 "Encoding type binder %s (%s) at kind %s\n" _147_670 aasym _147_669)))
end else begin
()
end
in (

let _50_786 = (encode_knd k env aa)
in (match (_50_786) with
| (guard_a_k, decls') -> begin
((((aasym), (FStar_ToSMT_Term.Type_sort))), (guard_a_k), (env'), (decls'), (FStar_Util.Inl (a)))
end)))
end)))
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.v = x; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _50_788}) -> begin
(

let x = (unmangle x)
in (

let _50_797 = (gen_term_var env x)
in (match (_50_797) with
| (xxsym, xx, env') -> begin
(

let _50_800 = (let _147_671 = (norm_t env t)
in (encode_typ_pred fuel_opt _147_671 env xx))
in (match (_50_800) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_ToSMT_Term.Term_sort))), (guard_x_t), (env'), (decls'), (FStar_Util.Inr (x)))
end))
end)))
end)
in (match (_50_806) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (_50_812) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end))))
and encode_typ_pred : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun fuel_opt t env e -> (

let t = (FStar_Absyn_Util.compress_typ t)
in (

let _50_820 = (encode_typ_term t env)
in (match (_50_820) with
| (t, decls) -> begin
(let _147_676 = (FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_147_676), (decls)))
end))))
and encode_typ_pred' : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun fuel_opt t env e -> (

let t = (FStar_Absyn_Util.compress_typ t)
in (

let _50_828 = (encode_typ_term t env)
in (match (_50_828) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _147_681 = (FStar_ToSMT_Term.mk_HasTypeZ e t)
in ((_147_681), (decls)))
end
| Some (f) -> begin
(let _147_682 = (FStar_ToSMT_Term.mk_HasTypeFuel f e t)
in ((_147_682), (decls)))
end)
end))))
and encode_typ_term : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Absyn_Util.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _147_685 = (lookup_typ_var env a)
in ((_147_685), ([])))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _147_686 = (lookup_free_tvar env fv)
in ((_147_686), ([])))
end
| FStar_Absyn_Syntax.Typ_fun (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (FStar_Absyn_Util.is_tot_or_gtot_comp res)) then begin
(

let _50_849 = (encode_binders None binders env)
in (match (_50_849) with
| (vars, guards, env', decls, _50_848) -> begin
(

let fsym = (let _147_687 = (varops.fresh "f")
in ((_147_687), (FStar_ToSMT_Term.Term_sort)))
in (

let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (

let app = (mk_ApplyE f vars)
in (

let _50_855 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_50_855) with
| (pre_opt, res_t) -> begin
(

let _50_858 = (encode_typ_pred None res_t env' app)
in (match (_50_858) with
| (res_pred, decls') -> begin
(

let _50_867 = (match (pre_opt) with
| None -> begin
(let _147_688 = (FStar_ToSMT_Term.mk_and_l guards)
in ((_147_688), (decls)))
end
| Some (pre) -> begin
(

let _50_864 = (encode_formula pre env')
in (match (_50_864) with
| (guard, decls0) -> begin
(let _147_689 = (FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in ((_147_689), ((FStar_List.append decls decls0))))
end))
end)
in (match (_50_867) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _147_691 = (let _147_690 = (FStar_ToSMT_Term.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_147_690)))
in (FStar_ToSMT_Term.mkForall _147_691))
in (

let cvars = (let _147_693 = (FStar_ToSMT_Term.free_variables t_interp)
in (FStar_All.pipe_right _147_693 (FStar_List.filter (fun _50_872 -> (match (_50_872) with
| (x, _50_871) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_ToSMT_Term.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t', sorts, _50_878) -> begin
(let _147_696 = (let _147_695 = (let _147_694 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in ((t'), (_147_694)))
in (FStar_ToSMT_Term.mkApp _147_695))
in ((_147_696), ([])))
end
| None -> begin
(

let tsym = (varops.fresh "Typ_fun")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _147_697 = (FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_147_697))
end else begin
None
end
in (

let tdecl = FStar_ToSMT_Term.DeclFun (((tsym), (cvar_sorts), (FStar_ToSMT_Term.Type_sort), (caption)))
in (

let t = (let _147_699 = (let _147_698 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((tsym), (_147_698)))
in (FStar_ToSMT_Term.mkApp _147_699))
in (

let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (

let k_assumption = (let _147_701 = (let _147_700 = (FStar_ToSMT_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_147_700), (Some ((Prims.strcat tsym " kinding")))))
in FStar_ToSMT_Term.Assume (_147_701))
in (

let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_ToSMT_Term.mk_HasTypeZ f t)
in (

let pre_typing = (let _147_708 = (let _147_707 = (let _147_706 = (let _147_705 = (let _147_704 = (let _147_703 = (let _147_702 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _147_702))
in ((f_has_t), (_147_703)))
in (FStar_ToSMT_Term.mkImp _147_704))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_147_705)))
in (mkForall_fuel _147_706))
in ((_147_707), (Some ("pre-typing for functions"))))
in FStar_ToSMT_Term.Assume (_147_708))
in (

let t_interp = (let _147_712 = (let _147_711 = (let _147_710 = (let _147_709 = (FStar_ToSMT_Term.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_147_709)))
in (FStar_ToSMT_Term.mkForall _147_710))
in ((_147_711), (Some ((Prims.strcat tsym " interpretation")))))
in FStar_ToSMT_Term.Assume (_147_712))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[])))
in (

let _50_894 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(

let tsym = (varops.fresh "Non_total_Typ_fun")
in (

let tdecl = FStar_ToSMT_Term.DeclFun (((tsym), ([]), (FStar_ToSMT_Term.Type_sort), (None)))
in (

let t = (FStar_ToSMT_Term.mkApp ((tsym), ([])))
in (

let t_kinding = (let _147_714 = (let _147_713 = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in ((_147_713), (None)))
in FStar_ToSMT_Term.Assume (_147_714))
in (

let fsym = (("f"), (FStar_ToSMT_Term.Term_sort))
in (

let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (

let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (

let t_interp = (let _147_721 = (let _147_720 = (let _147_719 = (let _147_718 = (let _147_717 = (let _147_716 = (let _147_715 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _147_715))
in ((f_has_t), (_147_716)))
in (FStar_ToSMT_Term.mkImp _147_717))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_147_718)))
in (mkForall_fuel _147_719))
in ((_147_720), (Some ("pre-typing"))))
in FStar_ToSMT_Term.Assume (_147_721))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end
end
| FStar_Absyn_Syntax.Typ_refine (_50_905) -> begin
(

let _50_924 = (match ((FStar_Tc_Normalize.normalize_refinement [] env.tcenv t0)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, f); FStar_Absyn_Syntax.tk = _50_914; FStar_Absyn_Syntax.pos = _50_912; FStar_Absyn_Syntax.fvs = _50_910; FStar_Absyn_Syntax.uvs = _50_908} -> begin
((x), (f))
end
| _50_921 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_50_924) with
| (x, f) -> begin
(

let _50_927 = (encode_typ_term x.FStar_Absyn_Syntax.sort env)
in (match (_50_927) with
| (base_t, decls) -> begin
(

let _50_931 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_50_931) with
| (x, xtm, env') -> begin
(

let _50_934 = (encode_formula f env')
in (match (_50_934) with
| (refinement, decls') -> begin
(

let _50_937 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_50_937) with
| (fsym, fterm) -> begin
(

let encoding = (let _147_723 = (let _147_722 = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_147_722), (refinement)))
in (FStar_ToSMT_Term.mkAnd _147_723))
in (

let cvars = (let _147_725 = (FStar_ToSMT_Term.free_variables encoding)
in (FStar_All.pipe_right _147_725 (FStar_List.filter (fun _50_942 -> (match (_50_942) with
| (y, _50_941) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = ((x), (FStar_ToSMT_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_ToSMT_Term.Fuel_sort))
in (

let tkey = (FStar_ToSMT_Term.mkForall (([]), ((ffv)::(xfv)::cvars), (encoding)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _50_949, _50_951) -> begin
(let _147_728 = (let _147_727 = (let _147_726 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in ((t), (_147_726)))
in (FStar_ToSMT_Term.mkApp _147_727))
in ((_147_728), ([])))
end
| None -> begin
(

let tsym = (varops.fresh "Typ_refine")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_ToSMT_Term.DeclFun (((tsym), (cvar_sorts), (FStar_ToSMT_Term.Type_sort), (None)))
in (

let t = (let _147_730 = (let _147_729 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((tsym), (_147_729)))
in (FStar_ToSMT_Term.mkApp _147_730))
in (

let x_has_t = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (

let t_kinding = (FStar_ToSMT_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in (

let assumption = (let _147_732 = (let _147_731 = (FStar_ToSMT_Term.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_147_731)))
in (FStar_ToSMT_Term.mkForall _147_732))
in (

let t_decls = (let _147_740 = (let _147_739 = (let _147_738 = (let _147_737 = (let _147_736 = (let _147_735 = (let _147_734 = (let _147_733 = (FStar_Absyn_Print.typ_to_string t0)
in Some (_147_733))
in ((assumption), (_147_734)))
in FStar_ToSMT_Term.Assume (_147_735))
in (_147_736)::[])
in (FStar_ToSMT_Term.Assume (((t_kinding), (None))))::_147_737)
in (tdecl)::_147_738)
in (FStar_List.append decls' _147_739))
in (FStar_List.append decls _147_740))
in (

let _50_964 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls))))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(

let ttm = (let _147_741 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _147_741))
in (

let _50_973 = (encode_knd k env ttm)
in (match (_50_973) with
| (t_has_k, decls) -> begin
(

let d = FStar_ToSMT_Term.Assume (((t_has_k), (None)))
in ((ttm), ((d)::decls)))
end)))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(

let is_full_app = (fun _50_980 -> (match (()) with
| () -> begin
(

let kk = (FStar_Tc_Recheck.recompute_kind head)
in (

let _50_985 = (FStar_Absyn_Util.kind_formals kk)
in (match (_50_985) with
| (formals, _50_984) -> begin
((FStar_List.length formals) = (FStar_List.length args))
end)))
end))
in (

let head = (FStar_Absyn_Util.compress_typ head)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(

let head = (lookup_typ_var env a)
in (

let _50_992 = (encode_args args env)
in (match (_50_992) with
| (args, decls) -> begin
(

let t = (mk_ApplyT_args head args)
in ((t), (decls)))
end)))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(

let _50_998 = (encode_args args env)
in (match (_50_998) with
| (args, decls) -> begin
if (is_full_app ()) then begin
(

let head = (lookup_free_tvar_name env fv)
in (

let t = (let _147_746 = (let _147_745 = (FStar_List.map (fun _50_11 -> (match (_50_11) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in ((head), (_147_745)))
in (FStar_ToSMT_Term.mkApp _147_746))
in ((t), (decls))))
end else begin
(

let head = (lookup_free_tvar env fv)
in (

let t = (mk_ApplyT_args head args)
in ((t), (decls))))
end
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(

let ttm = (let _147_747 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _147_747))
in (

let _50_1014 = (encode_knd k env ttm)
in (match (_50_1014) with
| (t_has_k, decls) -> begin
(

let d = FStar_ToSMT_Term.Assume (((t_has_k), (None)))
in ((ttm), ((d)::decls)))
end)))
end
| _50_1017 -> begin
(

let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, body) -> begin
(

let _50_1029 = (encode_binders None bs env)
in (match (_50_1029) with
| (vars, guards, env, decls, _50_1028) -> begin
(

let _50_1032 = (encode_typ_term body env)
in (match (_50_1032) with
| (body, decls') -> begin
(

let key_body = (let _147_751 = (let _147_750 = (let _147_749 = (let _147_748 = (FStar_ToSMT_Term.mk_and_l guards)
in ((_147_748), (body)))
in (FStar_ToSMT_Term.mkImp _147_749))
in (([]), (vars), (_147_750)))
in (FStar_ToSMT_Term.mkForall _147_751))
in (

let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (

let tkey = (FStar_ToSMT_Term.mkForall (([]), (cvars), (key_body)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _50_1038, _50_1040) -> begin
(let _147_754 = (let _147_753 = (let _147_752 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((t), (_147_752)))
in (FStar_ToSMT_Term.mkApp _147_753))
in ((_147_754), ([])))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (head) -> begin
((head), ([]))
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tsym = (varops.fresh "Typ_lam")
in (

let tdecl = FStar_ToSMT_Term.DeclFun (((tsym), (cvar_sorts), (FStar_ToSMT_Term.Type_sort), (None)))
in (

let t = (let _147_756 = (let _147_755 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((tsym), (_147_755)))
in (FStar_ToSMT_Term.mkApp _147_756))
in (

let app = (mk_ApplyT t vars)
in (

let interp = (let _147_763 = (let _147_762 = (let _147_761 = (let _147_760 = (let _147_759 = (let _147_758 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _147_757 = (FStar_ToSMT_Term.mkEq ((app), (body)))
in ((_147_758), (_147_757))))
in (FStar_ToSMT_Term.mkImp _147_759))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_147_760)))
in (FStar_ToSMT_Term.mkForall _147_761))
in ((_147_762), (Some ("Typ_lam interpretation"))))
in FStar_ToSMT_Term.Assume (_147_763))
in (

let kinding = (

let _50_1055 = (let _147_764 = (FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _147_764 env t))
in (match (_50_1055) with
| (ktm, decls'') -> begin
(let _147_768 = (let _147_767 = (let _147_766 = (let _147_765 = (FStar_ToSMT_Term.mkForall ((((t)::[])::[]), (cvars), (ktm)))
in ((_147_765), (Some ("Typ_lam kinding"))))
in FStar_ToSMT_Term.Assume (_147_766))
in (_147_767)::[])
in (FStar_List.append decls'' _147_768))
end))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(interp)::kinding)))
in (

let _50_1058 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))
end)
end))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _50_1062) -> begin
(encode_typ_term t env)
end
| FStar_Absyn_Syntax.Typ_meta (_50_1066) -> begin
(let _147_769 = (FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _147_769 env))
end
| (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _147_774 = (let _147_773 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Absyn_Syntax.pos)
in (let _147_772 = (FStar_Absyn_Print.tag_of_typ t0)
in (let _147_771 = (FStar_Absyn_Print.typ_to_string t0)
in (let _147_770 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _147_773 _147_772 _147_771 _147_770)))))
in (FStar_All.failwith _147_774))
end)))
and encode_exp : FStar_Absyn_Syntax.exp  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun e env -> (

let e = (FStar_Absyn_Visit.compress_exp_uvars e)
in (

let e0 = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_50_1077) -> begin
(let _147_777 = (FStar_Absyn_Util.compress_exp e)
in (encode_exp _147_777 env))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Absyn_Syntax.Exp_fvar (v, _50_1084) -> begin
(let _147_778 = (lookup_free_var env v)
in ((_147_778), ([])))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _147_779 = (encode_const c)
in ((_147_779), ([])))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _50_1092) -> begin
(

let _50_1095 = (FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _50_1099)) -> begin
(encode_exp e env)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, _50_1105) -> begin
(

let e = (let _147_780 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Exp_uvar _147_780))
in ((e), ([])))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(

let fallback = (fun _50_1114 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Exp_abs")
in (

let decl = FStar_ToSMT_Term.DeclFun (((f), ([]), (FStar_ToSMT_Term.Term_sort), (None)))
in (let _147_783 = (FStar_ToSMT_Term.mkFreeV ((f), (FStar_ToSMT_Term.Term_sort)))
in ((_147_783), ((decl)::[])))))
end))
in (match ((FStar_ST.read e.FStar_Absyn_Syntax.tk)) with
| None -> begin
(

let _50_1118 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
if (let _147_784 = (FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (FStar_All.pipe_left Prims.op_Negation _147_784)) then begin
(fallback ())
end else begin
(

let tfun = (as_function_typ env tfun)
in (match (tfun.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(

let nformals = (FStar_List.length bs')
in if ((nformals < (FStar_List.length bs)) && (FStar_Absyn_Util.is_total_comp c)) then begin
(

let _50_1130 = (FStar_Util.first_N nformals bs)
in (match (_50_1130) with
| (bs0, rest) -> begin
(

let res_t = (match ((FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s (FStar_Absyn_Util.comp_result c))
end
| _50_1134 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let e = (let _147_786 = (let _147_785 = (FStar_Absyn_Syntax.mk_Exp_abs ((rest), (body)) (Some (res_t)) body.FStar_Absyn_Syntax.pos)
in ((bs0), (_147_785)))
in (FStar_Absyn_Syntax.mk_Exp_abs _147_786 (Some (tfun)) e0.FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end else begin
(

let _50_1143 = (encode_binders None bs env)
in (match (_50_1143) with
| (vars, guards, envbody, decls, _50_1142) -> begin
(

let _50_1146 = (encode_exp body envbody)
in (match (_50_1146) with
| (body, decls') -> begin
(

let key_body = (let _147_790 = (let _147_789 = (let _147_788 = (let _147_787 = (FStar_ToSMT_Term.mk_and_l guards)
in ((_147_787), (body)))
in (FStar_ToSMT_Term.mkImp _147_788))
in (([]), (vars), (_147_789)))
in (FStar_ToSMT_Term.mkForall _147_790))
in (

let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (

let tkey = (FStar_ToSMT_Term.mkForall (([]), (cvars), (key_body)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _50_1152, _50_1154) -> begin
(let _147_793 = (let _147_792 = (let _147_791 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((t), (_147_791)))
in (FStar_ToSMT_Term.mkApp _147_792))
in ((_147_793), ([])))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
((t), ([]))
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let fsym = (varops.fresh "Exp_abs")
in (

let fdecl = FStar_ToSMT_Term.DeclFun (((fsym), (cvar_sorts), (FStar_ToSMT_Term.Term_sort), (None)))
in (

let f = (let _147_795 = (let _147_794 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((fsym), (_147_794)))
in (FStar_ToSMT_Term.mkApp _147_795))
in (

let app = (mk_ApplyE f vars)
in (

let _50_1168 = (encode_typ_pred None tfun env f)
in (match (_50_1168) with
| (f_has_t, decls'') -> begin
(

let typing_f = (let _147_797 = (let _147_796 = (FStar_ToSMT_Term.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_147_796), (Some ((Prims.strcat fsym " typing")))))
in FStar_ToSMT_Term.Assume (_147_797))
in (

let interp_f = (let _147_804 = (let _147_803 = (let _147_802 = (let _147_801 = (let _147_800 = (let _147_799 = (FStar_ToSMT_Term.mk_IsTyped app)
in (let _147_798 = (FStar_ToSMT_Term.mkEq ((app), (body)))
in ((_147_799), (_147_798))))
in (FStar_ToSMT_Term.mkImp _147_800))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_147_801)))
in (FStar_ToSMT_Term.mkForall _147_802))
in ((_147_803), (Some ((Prims.strcat fsym " interpretation")))))
in FStar_ToSMT_Term.Assume (_147_804))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::decls'') ((typing_f)::(interp_f)::[]))))
in (

let _50_1172 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash ((fsym), (cvar_sorts), (f_decls)))
in ((f), (f_decls))))))
end)))))))
end)
end))))
end))
end))
end)
end
| _50_1175 -> begin
(FStar_All.failwith "Impossible")
end))
end
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (l, _50_1186); FStar_Absyn_Syntax.tk = _50_1183; FStar_Absyn_Syntax.pos = _50_1181; FStar_Absyn_Syntax.fvs = _50_1179; FStar_Absyn_Syntax.uvs = _50_1177}, ((FStar_Util.Inl (_50_1201), _50_1204))::((FStar_Util.Inr (v1), _50_1198))::((FStar_Util.Inr (v2), _50_1193))::[]) when (FStar_Ident.lid_equals l.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
(

let _50_1211 = (encode_exp v1 env)
in (match (_50_1211) with
| (v1, decls1) -> begin
(

let _50_1214 = (encode_exp v2 env)
in (match (_50_1214) with
| (v2, decls2) -> begin
(let _147_805 = (FStar_ToSMT_Term.mk_LexCons v1 v2)
in ((_147_805), ((FStar_List.append decls1 decls2))))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_50_1224); FStar_Absyn_Syntax.tk = _50_1222; FStar_Absyn_Syntax.pos = _50_1220; FStar_Absyn_Syntax.fvs = _50_1218; FStar_Absyn_Syntax.uvs = _50_1216}, _50_1228) -> begin
(let _147_806 = (whnf_e env e)
in (encode_exp _147_806 env))
end
| FStar_Absyn_Syntax.Exp_app (head, args_e) -> begin
(

let _50_1237 = (encode_args args_e env)
in (match (_50_1237) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _50_1242 = (encode_exp head env)
in (match (_50_1242) with
| (head, decls') -> begin
(

let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let _50_1251 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_50_1251) with
| (formals, rest) -> begin
(

let subst = (FStar_Absyn_Util.formals_for_actuals formals args_e)
in (

let ty = (let _147_809 = (FStar_Absyn_Syntax.mk_Typ_fun ((rest), (c)) (Some (FStar_Absyn_Syntax.ktype)) e0.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _147_809 (FStar_Absyn_Util.subst_typ subst)))
in (

let _50_1256 = (encode_typ_pred None ty env app_tm)
in (match (_50_1256) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_ToSMT_Term.free_variables has_type)
in (

let e_typing = (let _147_811 = (let _147_810 = (FStar_ToSMT_Term.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in ((_147_810), (None)))
in FStar_ToSMT_Term.Assume (_147_811))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _50_1263 = (lookup_free_var_sym env fv)
in (match (_50_1263) with
| (fname, fuel_args) -> begin
(

let tm = (let _147_817 = (let _147_816 = (let _147_815 = (FStar_List.map (fun _50_12 -> (match (_50_12) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (FStar_List.append fuel_args _147_815))
in ((fname), (_147_816)))
in (FStar_ToSMT_Term.mkApp' _147_817))
in ((tm), (decls)))
end)))
in (

let head = (FStar_Absyn_Util.compress_exp head)
in (

let _50_1270 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("186"))) then begin
(let _147_819 = (FStar_Absyn_Print.exp_to_string head)
in (let _147_818 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.print2 "Recomputing type for %s\nFull term is %s\n" _147_819 _147_818)))
end else begin
()
end
in (

let head_type = (let _147_822 = (let _147_821 = (let _147_820 = (FStar_Tc_Recheck.recompute_typ head)
in (FStar_Absyn_Util.unrefine _147_820))
in (whnf env _147_821))
in (FStar_All.pipe_left FStar_Absyn_Util.unrefine _147_822))
in (

let _50_1273 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _147_825 = (FStar_Absyn_Print.exp_to_string head)
in (let _147_824 = (FStar_Absyn_Print.tag_of_exp head)
in (let _147_823 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.print3 "Recomputed type of head %s (%s) to be %s\n" _147_825 _147_824 _147_823))))
end else begin
()
end
in (match ((FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _147_829 = (let _147_828 = (FStar_Range.string_of_range e0.FStar_Absyn_Syntax.pos)
in (let _147_827 = (FStar_Absyn_Print.exp_to_string e0)
in (let _147_826 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.format3 "(%s) term is %s; head type is %s\n" _147_828 _147_827 _147_826))))
in (FStar_All.failwith _147_829))
end
| Some (formals, c) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _50_1282) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _50_1286 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some (((formals), (c)))))
end else begin
(encode_partial_app None)
end
end)
end)))))))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_50_1295); FStar_Absyn_Syntax.lbtyp = _50_1293; FStar_Absyn_Syntax.lbeff = _50_1291; FStar_Absyn_Syntax.lbdef = _50_1289})::[]), _50_1301) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Absyn_Syntax.Exp_let ((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = t1; FStar_Absyn_Syntax.lbeff = _50_1307; FStar_Absyn_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _50_1319 = (encode_exp e1 env)
in (match (_50_1319) with
| (ee1, decls1) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _50_1323 = (encode_exp e2 env')
in (match (_50_1323) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let (_50_1325) -> begin
(

let _50_1327 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_ToSMT_Term.DeclFun (((e), ([]), (FStar_ToSMT_Term.Term_sort), (None)))
in (let _147_830 = (FStar_ToSMT_Term.mkFreeV ((e), (FStar_ToSMT_Term.Term_sort)))
in ((_147_830), ((decl_e)::[]))))))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(

let _50_1337 = (encode_exp e env)
in (match (_50_1337) with
| (scr, decls) -> begin
(

let _50_1377 = (FStar_List.fold_right (fun _50_1341 _50_1344 -> (match (((_50_1341), (_50_1344))) with
| ((p, w, br), (else_case, decls)) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _50_1348 _50_1351 -> (match (((_50_1348), (_50_1351))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _50_1357 -> (match (_50_1357) with
| (x, t) -> begin
(match (x) with
| FStar_Util.Inl (a) -> begin
(push_typ_var env a.FStar_Absyn_Syntax.v t)
end
| FStar_Util.Inr (x) -> begin
(push_term_var env x.FStar_Absyn_Syntax.v t)
end)
end)) env))
in (

let _50_1371 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let _50_1368 = (encode_exp w env)
in (match (_50_1368) with
| (w, decls2) -> begin
(let _147_841 = (let _147_840 = (let _147_839 = (let _147_838 = (let _147_837 = (FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
in ((w), (_147_837)))
in (FStar_ToSMT_Term.mkEq _147_838))
in ((guard), (_147_839)))
in (FStar_ToSMT_Term.mkAnd _147_840))
in ((_147_841), (decls2)))
end))
end)
in (match (_50_1371) with
| (guard, decls2) -> begin
(

let _50_1374 = (encode_exp br env)
in (match (_50_1374) with
| (br, decls3) -> begin
(let _147_842 = (FStar_ToSMT_Term.mkITE ((guard), (br), (else_case)))
in ((_147_842), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end)) pats ((FStar_ToSMT_Term.mk_Term_unit), (decls)))
in (match (_50_1377) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (_50_1379) -> begin
(let _147_845 = (let _147_844 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _147_843 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "(%s): Impossible: encode_exp got %s" _147_844 _147_843)))
in (FStar_All.failwith _147_845))
end))))
and encode_pat : env_t  ->  FStar_Absyn_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _50_1386 -> begin
(let _147_848 = (encode_one_pat env pat)
in (_147_848)::[])
end))
and encode_one_pat : env_t  ->  FStar_Absyn_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _50_1389 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _147_851 = (FStar_Absyn_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _147_851))
end else begin
()
end
in (

let _50_1393 = (FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_50_1393) with
| (vars, pat_exp_or_typ) -> begin
(

let _50_1414 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _50_1396 v -> (match (_50_1396) with
| (env, vars) -> begin
(match (v) with
| FStar_Util.Inl (a) -> begin
(

let _50_1404 = (gen_typ_var env a.FStar_Absyn_Syntax.v)
in (match (_50_1404) with
| (aa, _50_1402, env) -> begin
((env), ((((v), (((aa), (FStar_ToSMT_Term.Type_sort)))))::vars))
end))
end
| FStar_Util.Inr (x) -> begin
(

let _50_1411 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_50_1411) with
| (xx, _50_1409, env) -> begin
((env), ((((v), (((xx), (FStar_ToSMT_Term.Term_sort)))))::vars))
end))
end)
end)) ((env), ([]))))
in (match (_50_1414) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_50_1419) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
FStar_ToSMT_Term.mkTrue
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _147_859 = (let _147_858 = (encode_const c)
in ((scrutinee), (_147_858)))
in (FStar_ToSMT_Term.mkEq _147_859))
end
| FStar_Absyn_Syntax.Pat_cons (f, _50_1443, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Absyn_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _50_1452 -> (match (_50_1452) with
| (arg, _50_1451) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _147_862 = (FStar_ToSMT_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _147_862)))
end))))
in (FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_50_1459) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _)) | (FStar_Absyn_Syntax.Pat_var (x)) | (FStar_Absyn_Syntax.Pat_wild (x)) -> begin
(((FStar_Util.Inr (x)), (scrutinee)))::[]
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _)) | (FStar_Absyn_Syntax.Pat_tvar (a)) | (FStar_Absyn_Syntax.Pat_twild (a)) -> begin
(((FStar_Util.Inl (a)), (scrutinee)))::[]
end
| FStar_Absyn_Syntax.Pat_constant (_50_1476) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_cons (f, _50_1480, args) -> begin
(let _147_870 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _50_1488 -> (match (_50_1488) with
| (arg, _50_1487) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _147_869 = (FStar_ToSMT_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _147_869)))
end))))
in (FStar_All.pipe_right _147_870 FStar_List.flatten))
end))
in (

let pat_term = (fun _50_1491 -> (match (()) with
| () -> begin
(match (pat_exp_or_typ) with
| FStar_Util.Inl (t) -> begin
(encode_typ_term t env)
end
| FStar_Util.Inr (e) -> begin
(encode_exp e env)
end)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end))))
and encode_args : FStar_Absyn_Syntax.args  ->  env_t  ->  ((FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list * FStar_ToSMT_Term.decls_t) = (fun l env -> (

let _50_1521 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _50_1501 x -> (match (_50_1501) with
| (tms, decls) -> begin
(match (x) with
| (FStar_Util.Inl (t), _50_1506) -> begin
(

let _50_1510 = (encode_typ_term t env)
in (match (_50_1510) with
| (t, decls') -> begin
(((FStar_Util.Inl (t))::tms), ((FStar_List.append decls decls')))
end))
end
| (FStar_Util.Inr (e), _50_1514) -> begin
(

let _50_1518 = (encode_exp e env)
in (match (_50_1518) with
| (t, decls') -> begin
(((FStar_Util.Inr (t))::tms), ((FStar_List.append decls decls')))
end))
end)
end)) (([]), ([]))))
in (match (_50_1521) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_formula : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun phi env -> (

let _50_1527 = (encode_formula_with_labels phi env)
in (match (_50_1527) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
((t), (decls))
end
| _50_1530 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.exp Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun induction_on new_pats t env -> (

let rec list_elements = (fun e -> (match ((let _147_885 = (FStar_Absyn_Util.unmeta_exp e)
in _147_885.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1547); FStar_Absyn_Syntax.tk = _50_1544; FStar_Absyn_Syntax.pos = _50_1542; FStar_Absyn_Syntax.fvs = _50_1540; FStar_Absyn_Syntax.uvs = _50_1538}, _50_1552) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.nil_lid) -> begin
[]
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1565); FStar_Absyn_Syntax.tk = _50_1562; FStar_Absyn_Syntax.pos = _50_1560; FStar_Absyn_Syntax.fvs = _50_1558; FStar_Absyn_Syntax.uvs = _50_1556}, (_50_1580)::((FStar_Util.Inr (hd), _50_1577))::((FStar_Util.Inr (tl), _50_1572))::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(let _147_886 = (list_elements tl)
in (hd)::_147_886)
end
| _50_1585 -> begin
(

let _50_1586 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (

let v_or_t_pat = (fun p -> (match ((let _147_889 = (FStar_Absyn_Util.unmeta_exp p)
in _147_889.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1600); FStar_Absyn_Syntax.tk = _50_1597; FStar_Absyn_Syntax.pos = _50_1595; FStar_Absyn_Syntax.fvs = _50_1593; FStar_Absyn_Syntax.uvs = _50_1591}, ((FStar_Util.Inl (_50_1610), _50_1613))::((FStar_Util.Inr (e), _50_1607))::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpat_lid) -> begin
(FStar_Absyn_Syntax.varg e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1628); FStar_Absyn_Syntax.tk = _50_1625; FStar_Absyn_Syntax.pos = _50_1623; FStar_Absyn_Syntax.fvs = _50_1621; FStar_Absyn_Syntax.uvs = _50_1619}, ((FStar_Util.Inl (t), _50_1635))::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatT_lid) -> begin
(FStar_Absyn_Syntax.targ t)
end
| _50_1641 -> begin
(FStar_All.failwith "Unexpected pattern term")
end))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (match (elts) with
| ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1663); FStar_Absyn_Syntax.tk = _50_1660; FStar_Absyn_Syntax.pos = _50_1658; FStar_Absyn_Syntax.fvs = _50_1656; FStar_Absyn_Syntax.uvs = _50_1654}, ((FStar_Util.Inr (e), _50_1670))::[]); FStar_Absyn_Syntax.tk = _50_1652; FStar_Absyn_Syntax.pos = _50_1650; FStar_Absyn_Syntax.fvs = _50_1648; FStar_Absyn_Syntax.uvs = _50_1646})::[] when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatOr_lid) -> begin
(let _147_894 = (list_elements e)
in (FStar_All.pipe_right _147_894 (FStar_List.map (fun branch -> (let _147_893 = (list_elements branch)
in (FStar_All.pipe_right _147_893 (FStar_List.map v_or_t_pat)))))))
end
| _50_1679 -> begin
(let _147_895 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_147_895)::[])
end)))
in (

let _50_1722 = (match ((let _147_896 = (FStar_Absyn_Util.compress_typ t)
in _147_896.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (ct); FStar_Absyn_Syntax.tk = _50_1688; FStar_Absyn_Syntax.pos = _50_1686; FStar_Absyn_Syntax.fvs = _50_1684; FStar_Absyn_Syntax.uvs = _50_1682}) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| ((FStar_Util.Inl (pre), _50_1707))::((FStar_Util.Inl (post), _50_1702))::((FStar_Util.Inr (pats), _50_1697))::[] -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _147_897 = (lemma_pats pats')
in ((binders), (pre), (post), (_147_897))))
end
| _50_1715 -> begin
(FStar_All.failwith "impos")
end)
end
| _50_1717 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_50_1722) with
| (binders, pre, post, patterns) -> begin
(

let _50_1729 = (encode_binders None binders env)
in (match (_50_1729) with
| (vars, guards, env, decls, _50_1728) -> begin
(

let _50_1749 = (let _147_901 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _50_1746 = (let _147_900 = (FStar_All.pipe_right branch (FStar_List.map (fun _50_13 -> (match (_50_13) with
| (FStar_Util.Inl (t), _50_1735) -> begin
(encode_formula t env)
end
| (FStar_Util.Inr (e), _50_1740) -> begin
(encode_exp e (

let _50_1742 = env
in {bindings = _50_1742.bindings; depth = _50_1742.depth; tcenv = _50_1742.tcenv; warn = _50_1742.warn; cache = _50_1742.cache; nolabels = _50_1742.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _50_1742.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _147_900 FStar_List.unzip))
in (match (_50_1746) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _147_901 FStar_List.unzip))
in (match (_50_1749) with
| (pats, decls') -> begin
(

let decls' = (FStar_List.flatten decls')
in (

let pats = (match (induction_on) with
| None -> begin
pats
end
| Some (e) -> begin
(match (vars) with
| [] -> begin
pats
end
| (l)::[] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _147_904 = (let _147_903 = (FStar_ToSMT_Term.mkFreeV l)
in (FStar_ToSMT_Term.mk_Precedes _147_903 e))
in (_147_904)::p))))
end
| _50_1759 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _147_910 = (FStar_ToSMT_Term.mk_Precedes tl e)
in (_147_910)::p))))
end
| ((x, FStar_ToSMT_Term.Term_sort))::vars -> begin
(let _147_912 = (let _147_911 = (FStar_ToSMT_Term.mkFreeV ((x), (FStar_ToSMT_Term.Term_sort)))
in (FStar_ToSMT_Term.mk_LexCons _147_911 tl))
in (aux _147_912 vars))
end
| _50_1771 -> begin
pats
end))
in (let _147_913 = (FStar_ToSMT_Term.mkFreeV (("Prims.LexTop"), (FStar_ToSMT_Term.Term_sort)))
in (aux _147_913 vars)))
end)
end)
in (

let env = (

let _50_1773 = env
in {bindings = _50_1773.bindings; depth = _50_1773.depth; tcenv = _50_1773.tcenv; warn = _50_1773.warn; cache = _50_1773.cache; nolabels = true; use_zfuel_name = _50_1773.use_zfuel_name; encode_non_total_function_typ = _50_1773.encode_non_total_function_typ})
in (

let _50_1778 = (let _147_914 = (FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _147_914 env))
in (match (_50_1778) with
| (pre, decls'') -> begin
(

let _50_1781 = (let _147_915 = (FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _147_915 env))
in (match (_50_1781) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _147_920 = (let _147_919 = (let _147_918 = (let _147_917 = (let _147_916 = (FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in ((_147_916), (post)))
in (FStar_ToSMT_Term.mkImp _147_917))
in ((pats), (vars), (_147_918)))
in (FStar_ToSMT_Term.mkForall _147_919))
in ((_147_920), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * labels * FStar_ToSMT_Term.decls_t) = (fun phi env -> (

let enc = (fun f l -> (

let _50_1802 = (FStar_Util.fold_map (fun decls x -> (match ((Prims.fst x)) with
| FStar_Util.Inl (t) -> begin
(

let _50_1794 = (encode_typ_term t env)
in (match (_50_1794) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))
end
| FStar_Util.Inr (e) -> begin
(

let _50_1799 = (encode_exp e env)
in (match (_50_1799) with
| (e, decls') -> begin
(((FStar_List.append decls decls')), (e))
end))
end)) [] l)
in (match (_50_1802) with
| (decls, args) -> begin
(let _147_938 = (f args)
in ((_147_938), ([]), (decls)))
end)))
in (

let enc_prop_c = (fun f l -> (

let _50_1822 = (FStar_List.fold_right (fun t _50_1810 -> (match (_50_1810) with
| (phis, labs, decls) -> begin
(match ((Prims.fst t)) with
| FStar_Util.Inl (t) -> begin
(

let _50_1816 = (encode_formula_with_labels t env)
in (match (_50_1816) with
| (phi, labs', decls') -> begin
(((phi)::phis), ((FStar_List.append labs' labs)), ((FStar_List.append decls' decls)))
end))
end
| _50_1818 -> begin
(FStar_All.failwith "Expected a formula")
end)
end)) l (([]), ([]), ([])))
in (match (_50_1822) with
| (phis, labs, decls) -> begin
(let _147_954 = (f phis)
in ((_147_954), (labs), (decls)))
end)))
in (

let const_op = (fun f _50_1825 -> ((f), ([]), ([])))
in (

let un_op = (fun f l -> (let _147_968 = (FStar_List.hd l)
in (FStar_All.pipe_left f _147_968)))
in (

let bin_op = (fun f _50_14 -> (match (_50_14) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| _50_1836 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let eq_op = (fun _50_15 -> (match (_50_15) with
| (_50_1844)::(_50_1842)::(e1)::(e2)::[] -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) l)
end))
in (

let mk_imp = (fun _50_16 -> (match (_50_16) with
| ((FStar_Util.Inl (lhs), _50_1857))::((FStar_Util.Inl (rhs), _50_1852))::[] -> begin
(

let _50_1863 = (encode_formula_with_labels rhs env)
in (match (_50_1863) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _50_1866) -> begin
((l1), (labs1), (decls1))
end
| _50_1870 -> begin
(

let _50_1874 = (encode_formula_with_labels lhs env)
in (match (_50_1874) with
| (l2, labs2, decls2) -> begin
(let _147_982 = (FStar_ToSMT_Term.mkImp ((l2), (l1)))
in ((_147_982), ((FStar_List.append labs1 labs2)), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| _50_1876 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun _50_17 -> (match (_50_17) with
| ((FStar_Util.Inl (guard), _50_1892))::((FStar_Util.Inl (_then), _50_1887))::((FStar_Util.Inl (_else), _50_1882))::[] -> begin
(

let _50_1898 = (encode_formula_with_labels guard env)
in (match (_50_1898) with
| (g, labs1, decls1) -> begin
(

let _50_1902 = (encode_formula_with_labels _then env)
in (match (_50_1902) with
| (t, labs2, decls2) -> begin
(

let _50_1906 = (encode_formula_with_labels _else env)
in (match (_50_1906) with
| (e, labs3, decls3) -> begin
(

let res = (FStar_ToSMT_Term.mkITE ((g), (t), (e)))
in ((res), ((FStar_List.append labs1 (FStar_List.append labs2 labs3))), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| _50_1909 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _147_994 = (FStar_List.map FStar_ToSMT_Term.unboxInt l)
in (f _147_994)))
in (

let connectives = (let _147_1055 = (let _147_1003 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkAnd))
in ((FStar_Absyn_Const.and_lid), (_147_1003)))
in (let _147_1054 = (let _147_1053 = (let _147_1009 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkOr))
in ((FStar_Absyn_Const.or_lid), (_147_1009)))
in (let _147_1052 = (let _147_1051 = (let _147_1050 = (let _147_1018 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkIff))
in ((FStar_Absyn_Const.iff_lid), (_147_1018)))
in (let _147_1049 = (let _147_1048 = (let _147_1047 = (let _147_1027 = (FStar_All.pipe_left enc_prop_c (un_op FStar_ToSMT_Term.mkNot))
in ((FStar_Absyn_Const.not_lid), (_147_1027)))
in (let _147_1046 = (let _147_1045 = (let _147_1033 = (FStar_All.pipe_left enc (bin_op FStar_ToSMT_Term.mkEq))
in ((FStar_Absyn_Const.eqT_lid), (_147_1033)))
in (_147_1045)::(((FStar_Absyn_Const.eq2_lid), (eq_op)))::(((FStar_Absyn_Const.true_lid), ((const_op FStar_ToSMT_Term.mkTrue))))::(((FStar_Absyn_Const.false_lid), ((const_op FStar_ToSMT_Term.mkFalse))))::[])
in (_147_1047)::_147_1046))
in (((FStar_Absyn_Const.ite_lid), (mk_ite)))::_147_1048)
in (_147_1050)::_147_1049))
in (((FStar_Absyn_Const.imp_lid), (mk_imp)))::_147_1051)
in (_147_1053)::_147_1052))
in (_147_1055)::_147_1054))
in (

let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (phi', msg, r, b)) -> begin
(

let _50_1927 = (encode_formula_with_labels phi' env)
in (match (_50_1927) with
| (phi, labs, decls) -> begin
if env.nolabels then begin
((phi), ([]), (decls))
end else begin
(

let lvar = (let _147_1058 = (varops.fresh "label")
in ((_147_1058), (FStar_ToSMT_Term.Bool_sort)))
in (

let lterm = (FStar_ToSMT_Term.mkFreeV lvar)
in (

let lphi = (FStar_ToSMT_Term.mkOr ((lterm), (phi)))
in ((lphi), ((((lvar), (msg), (r)))::labs), (decls)))))
end
end))
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _50_1938; FStar_Absyn_Syntax.pos = _50_1936; FStar_Absyn_Syntax.fvs = _50_1934; FStar_Absyn_Syntax.uvs = _50_1932}, (_50_1953)::((FStar_Util.Inr (l), _50_1950))::((FStar_Util.Inl (phi), _50_1945))::[]) when (FStar_Ident.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_IH) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(

let _50_1959 = (encode_exp l env)
in (match (_50_1959) with
| (e, decls) -> begin
(

let _50_1962 = (encode_function_type_as_formula (Some (e)) None phi env)
in (match (_50_1962) with
| (f, decls') -> begin
((f), ([]), ((FStar_List.append decls decls')))
end))
end))
end else begin
((FStar_ToSMT_Term.mkTrue), ([]), ([]))
end
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _50_1970; FStar_Absyn_Syntax.pos = _50_1968; FStar_Absyn_Syntax.fvs = _50_1966; FStar_Absyn_Syntax.uvs = _50_1964}, (_50_1982)::((FStar_Util.Inl (phi), _50_1978))::tl) when (FStar_Ident.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_lem) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(

let pat = (match (tl) with
| [] -> begin
None
end
| ((FStar_Util.Inr (pat), _50_1990))::[] -> begin
Some (pat)
end)
in (

let _50_1996 = (encode_function_type_as_formula None pat phi env)
in (match (_50_1996) with
| (f, decls) -> begin
((f), ([]), (decls))
end)))
end else begin
((FStar_ToSMT_Term.mkTrue), ([]), ([]))
end
end
| _50_1998 -> begin
(

let _50_2001 = (encode_typ_term phi env)
in (match (_50_2001) with
| (tt, decls) -> begin
(let _147_1059 = (FStar_ToSMT_Term.mk_Valid tt)
in ((_147_1059), ([]), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _50_2013 = (encode_binders None bs env)
in (match (_50_2013) with
| (vars, guards, env, decls, _50_2012) -> begin
(

let _50_2033 = (let _147_1071 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _50_2030 = (let _147_1070 = (FStar_All.pipe_right p (FStar_List.map (fun _50_18 -> (match (_50_18) with
| (FStar_Util.Inl (t), _50_2019) -> begin
(encode_typ_term t env)
end
| (FStar_Util.Inr (e), _50_2024) -> begin
(encode_exp e (

let _50_2026 = env
in {bindings = _50_2026.bindings; depth = _50_2026.depth; tcenv = _50_2026.tcenv; warn = _50_2026.warn; cache = _50_2026.cache; nolabels = _50_2026.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _50_2026.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _147_1070 FStar_List.unzip))
in (match (_50_2030) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _147_1071 FStar_List.unzip))
in (match (_50_2033) with
| (pats, decls') -> begin
(

let _50_2037 = (encode_formula_with_labels body env)
in (match (_50_2037) with
| (body, labs, decls'') -> begin
(let _147_1072 = (FStar_ToSMT_Term.mk_and_l guards)
in ((vars), (pats), (_147_1072), (body), (labs), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls'')))))
end))
end))
end)))
in (

let _50_2038 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _147_1073 = (FStar_Absyn_Print.formula_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _147_1073))
end else begin
()
end
in (

let phi = (FStar_Absyn_Util.compress_typ phi)
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _50_2050 -> (match (_50_2050) with
| (l, _50_2049) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_50_2053, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, pats, body)) -> begin
(

let _50_2063 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _147_1090 = (FStar_All.pipe_right vars (FStar_Absyn_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _147_1090))
end else begin
()
end
in (

let _50_2071 = (encode_q_body env vars pats body)
in (match (_50_2071) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _147_1093 = (let _147_1092 = (let _147_1091 = (FStar_ToSMT_Term.mkImp ((guard), (body)))
in ((pats), (vars), (_147_1091)))
in (FStar_ToSMT_Term.mkForall _147_1092))
in ((_147_1093), (labs), (decls)))
end)))
end
| Some (FStar_Absyn_Util.QEx (vars, pats, body)) -> begin
(

let _50_2084 = (encode_q_body env vars pats body)
in (match (_50_2084) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _147_1096 = (let _147_1095 = (let _147_1094 = (FStar_ToSMT_Term.mkAnd ((guard), (body)))
in ((pats), (vars), (_147_1094)))
in (FStar_ToSMT_Term.mkExists _147_1095))
in ((_147_1096), (labs), (decls)))
end))
end))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _50_2090 = (fresh_fvar "a" FStar_ToSMT_Term.Type_sort)
in (match (_50_2090) with
| (asym, a) -> begin
(

let _50_2093 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_50_2093) with
| (xsym, x) -> begin
(

let _50_2096 = (fresh_fvar "y" FStar_ToSMT_Term.Term_sort)
in (match (_50_2096) with
| (ysym, y) -> begin
(

let deffun = (fun vars body x -> (let _147_1131 = (let _147_1130 = (let _147_1129 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _147_1128 = (FStar_ToSMT_Term.abstr vars body)
in ((x), (_147_1129), (FStar_ToSMT_Term.Term_sort), (_147_1128), (None))))
in FStar_ToSMT_Term.DefineFun (_147_1130))
in (_147_1131)::[]))
in (

let quant = (fun vars body x -> (

let t1 = (let _147_1143 = (let _147_1142 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in ((x), (_147_1142)))
in (FStar_ToSMT_Term.mkApp _147_1143))
in (

let vname_decl = (let _147_1145 = (let _147_1144 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_147_1144), (FStar_ToSMT_Term.Term_sort), (None)))
in FStar_ToSMT_Term.DeclFun (_147_1145))
in (let _147_1151 = (let _147_1150 = (let _147_1149 = (let _147_1148 = (let _147_1147 = (let _147_1146 = (FStar_ToSMT_Term.mkEq ((t1), (body)))
in ((((t1)::[])::[]), (vars), (_147_1146)))
in (FStar_ToSMT_Term.mkForall _147_1147))
in ((_147_1148), (None)))
in FStar_ToSMT_Term.Assume (_147_1149))
in (_147_1150)::[])
in (vname_decl)::_147_1151))))
in (

let def_or_quant = (fun vars body x -> if (FStar_Options.inline_arith ()) then begin
(deffun vars body x)
end else begin
(quant vars body x)
end)
in (

let axy = (((asym), (FStar_ToSMT_Term.Type_sort)))::(((xsym), (FStar_ToSMT_Term.Term_sort)))::(((ysym), (FStar_ToSMT_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_ToSMT_Term.Term_sort)))::(((ysym), (FStar_ToSMT_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_ToSMT_Term.Term_sort)))::[]
in (

let prims = (let _147_1317 = (let _147_1166 = (let _147_1165 = (let _147_1164 = (FStar_ToSMT_Term.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1164))
in (def_or_quant axy _147_1165))
in ((FStar_Absyn_Const.op_Eq), (_147_1166)))
in (let _147_1316 = (let _147_1315 = (let _147_1173 = (let _147_1172 = (let _147_1171 = (let _147_1170 = (FStar_ToSMT_Term.mkEq ((x), (y)))
in (FStar_ToSMT_Term.mkNot _147_1170))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1171))
in (def_or_quant axy _147_1172))
in ((FStar_Absyn_Const.op_notEq), (_147_1173)))
in (let _147_1314 = (let _147_1313 = (let _147_1182 = (let _147_1181 = (let _147_1180 = (let _147_1179 = (let _147_1178 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1177 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1178), (_147_1177))))
in (FStar_ToSMT_Term.mkLT _147_1179))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1180))
in (def_or_quant xy _147_1181))
in ((FStar_Absyn_Const.op_LT), (_147_1182)))
in (let _147_1312 = (let _147_1311 = (let _147_1191 = (let _147_1190 = (let _147_1189 = (let _147_1188 = (let _147_1187 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1186 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1187), (_147_1186))))
in (FStar_ToSMT_Term.mkLTE _147_1188))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1189))
in (def_or_quant xy _147_1190))
in ((FStar_Absyn_Const.op_LTE), (_147_1191)))
in (let _147_1310 = (let _147_1309 = (let _147_1200 = (let _147_1199 = (let _147_1198 = (let _147_1197 = (let _147_1196 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1195 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1196), (_147_1195))))
in (FStar_ToSMT_Term.mkGT _147_1197))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1198))
in (def_or_quant xy _147_1199))
in ((FStar_Absyn_Const.op_GT), (_147_1200)))
in (let _147_1308 = (let _147_1307 = (let _147_1209 = (let _147_1208 = (let _147_1207 = (let _147_1206 = (let _147_1205 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1204 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1205), (_147_1204))))
in (FStar_ToSMT_Term.mkGTE _147_1206))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1207))
in (def_or_quant xy _147_1208))
in ((FStar_Absyn_Const.op_GTE), (_147_1209)))
in (let _147_1306 = (let _147_1305 = (let _147_1218 = (let _147_1217 = (let _147_1216 = (let _147_1215 = (let _147_1214 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1213 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1214), (_147_1213))))
in (FStar_ToSMT_Term.mkSub _147_1215))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _147_1216))
in (def_or_quant xy _147_1217))
in ((FStar_Absyn_Const.op_Subtraction), (_147_1218)))
in (let _147_1304 = (let _147_1303 = (let _147_1225 = (let _147_1224 = (let _147_1223 = (let _147_1222 = (FStar_ToSMT_Term.unboxInt x)
in (FStar_ToSMT_Term.mkMinus _147_1222))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _147_1223))
in (def_or_quant qx _147_1224))
in ((FStar_Absyn_Const.op_Minus), (_147_1225)))
in (let _147_1302 = (let _147_1301 = (let _147_1234 = (let _147_1233 = (let _147_1232 = (let _147_1231 = (let _147_1230 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1229 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1230), (_147_1229))))
in (FStar_ToSMT_Term.mkAdd _147_1231))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _147_1232))
in (def_or_quant xy _147_1233))
in ((FStar_Absyn_Const.op_Addition), (_147_1234)))
in (let _147_1300 = (let _147_1299 = (let _147_1243 = (let _147_1242 = (let _147_1241 = (let _147_1240 = (let _147_1239 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1238 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1239), (_147_1238))))
in (FStar_ToSMT_Term.mkMul _147_1240))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _147_1241))
in (def_or_quant xy _147_1242))
in ((FStar_Absyn_Const.op_Multiply), (_147_1243)))
in (let _147_1298 = (let _147_1297 = (let _147_1252 = (let _147_1251 = (let _147_1250 = (let _147_1249 = (let _147_1248 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1247 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1248), (_147_1247))))
in (FStar_ToSMT_Term.mkDiv _147_1249))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _147_1250))
in (def_or_quant xy _147_1251))
in ((FStar_Absyn_Const.op_Division), (_147_1252)))
in (let _147_1296 = (let _147_1295 = (let _147_1261 = (let _147_1260 = (let _147_1259 = (let _147_1258 = (let _147_1257 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1256 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1257), (_147_1256))))
in (FStar_ToSMT_Term.mkMod _147_1258))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _147_1259))
in (def_or_quant xy _147_1260))
in ((FStar_Absyn_Const.op_Modulus), (_147_1261)))
in (let _147_1294 = (let _147_1293 = (let _147_1270 = (let _147_1269 = (let _147_1268 = (let _147_1267 = (let _147_1266 = (FStar_ToSMT_Term.unboxBool x)
in (let _147_1265 = (FStar_ToSMT_Term.unboxBool y)
in ((_147_1266), (_147_1265))))
in (FStar_ToSMT_Term.mkAnd _147_1267))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1268))
in (def_or_quant xy _147_1269))
in ((FStar_Absyn_Const.op_And), (_147_1270)))
in (let _147_1292 = (let _147_1291 = (let _147_1279 = (let _147_1278 = (let _147_1277 = (let _147_1276 = (let _147_1275 = (FStar_ToSMT_Term.unboxBool x)
in (let _147_1274 = (FStar_ToSMT_Term.unboxBool y)
in ((_147_1275), (_147_1274))))
in (FStar_ToSMT_Term.mkOr _147_1276))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1277))
in (def_or_quant xy _147_1278))
in ((FStar_Absyn_Const.op_Or), (_147_1279)))
in (let _147_1290 = (let _147_1289 = (let _147_1286 = (let _147_1285 = (let _147_1284 = (let _147_1283 = (FStar_ToSMT_Term.unboxBool x)
in (FStar_ToSMT_Term.mkNot _147_1283))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1284))
in (def_or_quant qx _147_1285))
in ((FStar_Absyn_Const.op_Negation), (_147_1286)))
in (_147_1289)::[])
in (_147_1291)::_147_1290))
in (_147_1293)::_147_1292))
in (_147_1295)::_147_1294))
in (_147_1297)::_147_1296))
in (_147_1299)::_147_1298))
in (_147_1301)::_147_1300))
in (_147_1303)::_147_1302))
in (_147_1305)::_147_1304))
in (_147_1307)::_147_1306))
in (_147_1309)::_147_1308))
in (_147_1311)::_147_1310))
in (_147_1313)::_147_1312))
in (_147_1315)::_147_1314))
in (_147_1317)::_147_1316))
in (

let mk = (fun l v -> (let _147_1349 = (FStar_All.pipe_right prims (FStar_List.filter (fun _50_2120 -> (match (_50_2120) with
| (l', _50_2119) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _147_1349 (FStar_List.collect (fun _50_2124 -> (match (_50_2124) with
| (_50_2122, b) -> begin
(b v)
end))))))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _50_2130 -> (match (_50_2130) with
| (l', _50_2129) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))))
end))
end))
end))


let primitive_type_axioms : FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.decl Prims.list = (

let xx = (("x"), (FStar_ToSMT_Term.Term_sort))
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let yy = (("y"), (FStar_ToSMT_Term.Term_sort))
in (

let y = (FStar_ToSMT_Term.mkFreeV yy)
in (

let mk_unit = (fun _50_2136 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let _147_1381 = (let _147_1372 = (let _147_1371 = (FStar_ToSMT_Term.mk_HasType FStar_ToSMT_Term.mk_Term_unit tt)
in ((_147_1371), (Some ("unit typing"))))
in FStar_ToSMT_Term.Assume (_147_1372))
in (let _147_1380 = (let _147_1379 = (let _147_1378 = (let _147_1377 = (let _147_1376 = (let _147_1375 = (let _147_1374 = (let _147_1373 = (FStar_ToSMT_Term.mkEq ((x), (FStar_ToSMT_Term.mk_Term_unit)))
in ((typing_pred), (_147_1373)))
in (FStar_ToSMT_Term.mkImp _147_1374))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_147_1375)))
in (mkForall_fuel _147_1376))
in ((_147_1377), (Some ("unit inversion"))))
in FStar_ToSMT_Term.Assume (_147_1378))
in (_147_1379)::[])
in (_147_1381)::_147_1380))))
in (

let mk_bool = (fun _50_2141 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_ToSMT_Term.Bool_sort))
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _147_1402 = (let _147_1391 = (let _147_1390 = (let _147_1389 = (let _147_1388 = (let _147_1387 = (let _147_1386 = (FStar_ToSMT_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_147_1386)))
in (FStar_ToSMT_Term.mkImp _147_1387))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_147_1388)))
in (mkForall_fuel _147_1389))
in ((_147_1390), (Some ("bool inversion"))))
in FStar_ToSMT_Term.Assume (_147_1391))
in (let _147_1401 = (let _147_1400 = (let _147_1399 = (let _147_1398 = (let _147_1397 = (let _147_1396 = (let _147_1393 = (let _147_1392 = (FStar_ToSMT_Term.boxBool b)
in (_147_1392)::[])
in (_147_1393)::[])
in (let _147_1395 = (let _147_1394 = (FStar_ToSMT_Term.boxBool b)
in (FStar_ToSMT_Term.mk_HasType _147_1394 tt))
in ((_147_1396), ((bb)::[]), (_147_1395))))
in (FStar_ToSMT_Term.mkForall _147_1397))
in ((_147_1398), (Some ("bool typing"))))
in FStar_ToSMT_Term.Assume (_147_1399))
in (_147_1400)::[])
in (_147_1402)::_147_1401))))))
in (

let mk_int = (fun _50_2148 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (

let typing_pred_y = (FStar_ToSMT_Term.mk_HasType y tt)
in (

let aa = (("a"), (FStar_ToSMT_Term.Int_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let bb = (("b"), (FStar_ToSMT_Term.Int_sort))
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let precedes = (let _147_1414 = (let _147_1413 = (let _147_1412 = (let _147_1411 = (let _147_1410 = (let _147_1409 = (FStar_ToSMT_Term.boxInt a)
in (let _147_1408 = (let _147_1407 = (FStar_ToSMT_Term.boxInt b)
in (_147_1407)::[])
in (_147_1409)::_147_1408))
in (tt)::_147_1410)
in (tt)::_147_1411)
in (("Prims.Precedes"), (_147_1412)))
in (FStar_ToSMT_Term.mkApp _147_1413))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _147_1414))
in (

let precedes_y_x = (let _147_1415 = (FStar_ToSMT_Term.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _147_1415))
in (let _147_1457 = (let _147_1421 = (let _147_1420 = (let _147_1419 = (let _147_1418 = (let _147_1417 = (let _147_1416 = (FStar_ToSMT_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_147_1416)))
in (FStar_ToSMT_Term.mkImp _147_1417))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_147_1418)))
in (mkForall_fuel _147_1419))
in ((_147_1420), (Some ("int inversion"))))
in FStar_ToSMT_Term.Assume (_147_1421))
in (let _147_1456 = (let _147_1455 = (let _147_1429 = (let _147_1428 = (let _147_1427 = (let _147_1426 = (let _147_1423 = (let _147_1422 = (FStar_ToSMT_Term.boxInt b)
in (_147_1422)::[])
in (_147_1423)::[])
in (let _147_1425 = (let _147_1424 = (FStar_ToSMT_Term.boxInt b)
in (FStar_ToSMT_Term.mk_HasType _147_1424 tt))
in ((_147_1426), ((bb)::[]), (_147_1425))))
in (FStar_ToSMT_Term.mkForall _147_1427))
in ((_147_1428), (Some ("int typing"))))
in FStar_ToSMT_Term.Assume (_147_1429))
in (let _147_1454 = (let _147_1453 = (let _147_1452 = (let _147_1451 = (let _147_1450 = (let _147_1449 = (let _147_1448 = (let _147_1447 = (let _147_1446 = (let _147_1445 = (let _147_1444 = (let _147_1443 = (let _147_1432 = (let _147_1431 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1430 = (FStar_ToSMT_Term.mkInteger' (Prims.parse_int "0"))
in ((_147_1431), (_147_1430))))
in (FStar_ToSMT_Term.mkGT _147_1432))
in (let _147_1442 = (let _147_1441 = (let _147_1435 = (let _147_1434 = (FStar_ToSMT_Term.unboxInt y)
in (let _147_1433 = (FStar_ToSMT_Term.mkInteger' (Prims.parse_int "0"))
in ((_147_1434), (_147_1433))))
in (FStar_ToSMT_Term.mkGTE _147_1435))
in (let _147_1440 = (let _147_1439 = (let _147_1438 = (let _147_1437 = (FStar_ToSMT_Term.unboxInt y)
in (let _147_1436 = (FStar_ToSMT_Term.unboxInt x)
in ((_147_1437), (_147_1436))))
in (FStar_ToSMT_Term.mkLT _147_1438))
in (_147_1439)::[])
in (_147_1441)::_147_1440))
in (_147_1443)::_147_1442))
in (typing_pred_y)::_147_1444)
in (typing_pred)::_147_1445)
in (FStar_ToSMT_Term.mk_and_l _147_1446))
in ((_147_1447), (precedes_y_x)))
in (FStar_ToSMT_Term.mkImp _147_1448))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_147_1449)))
in (mkForall_fuel _147_1450))
in ((_147_1451), (Some ("well-founded ordering on nat (alt)"))))
in FStar_ToSMT_Term.Assume (_147_1452))
in (_147_1453)::[])
in (_147_1455)::_147_1454))
in (_147_1457)::_147_1456)))))))))))
in (

let mk_int_alias = (fun _50_2160 tt -> (let _147_1466 = (let _147_1465 = (let _147_1464 = (let _147_1463 = (let _147_1462 = (FStar_ToSMT_Term.mkApp ((FStar_Absyn_Const.int_lid.FStar_Ident.str), ([])))
in ((tt), (_147_1462)))
in (FStar_ToSMT_Term.mkEq _147_1463))
in ((_147_1464), (Some ("mapping to int; for now"))))
in FStar_ToSMT_Term.Assume (_147_1465))
in (_147_1466)::[]))
in (

let mk_str = (fun _50_2164 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_ToSMT_Term.String_sort))
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _147_1487 = (let _147_1476 = (let _147_1475 = (let _147_1474 = (let _147_1473 = (let _147_1472 = (let _147_1471 = (FStar_ToSMT_Term.mk_tester "BoxString" x)
in ((typing_pred), (_147_1471)))
in (FStar_ToSMT_Term.mkImp _147_1472))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_147_1473)))
in (mkForall_fuel _147_1474))
in ((_147_1475), (Some ("string inversion"))))
in FStar_ToSMT_Term.Assume (_147_1476))
in (let _147_1486 = (let _147_1485 = (let _147_1484 = (let _147_1483 = (let _147_1482 = (let _147_1481 = (let _147_1478 = (let _147_1477 = (FStar_ToSMT_Term.boxString b)
in (_147_1477)::[])
in (_147_1478)::[])
in (let _147_1480 = (let _147_1479 = (FStar_ToSMT_Term.boxString b)
in (FStar_ToSMT_Term.mk_HasType _147_1479 tt))
in ((_147_1481), ((bb)::[]), (_147_1480))))
in (FStar_ToSMT_Term.mkForall _147_1482))
in ((_147_1483), (Some ("string typing"))))
in FStar_ToSMT_Term.Assume (_147_1484))
in (_147_1485)::[])
in (_147_1487)::_147_1486))))))
in (

let mk_ref = (fun reft_name _50_2172 -> (

let r = (("r"), (FStar_ToSMT_Term.Ref_sort))
in (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let refa = (let _147_1494 = (let _147_1493 = (let _147_1492 = (FStar_ToSMT_Term.mkFreeV aa)
in (_147_1492)::[])
in ((reft_name), (_147_1493)))
in (FStar_ToSMT_Term.mkApp _147_1494))
in (

let refb = (let _147_1497 = (let _147_1496 = (let _147_1495 = (FStar_ToSMT_Term.mkFreeV bb)
in (_147_1495)::[])
in ((reft_name), (_147_1496)))
in (FStar_ToSMT_Term.mkApp _147_1497))
in (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_ToSMT_Term.mk_HasType x refb)
in (let _147_1516 = (let _147_1503 = (let _147_1502 = (let _147_1501 = (let _147_1500 = (let _147_1499 = (let _147_1498 = (FStar_ToSMT_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_147_1498)))
in (FStar_ToSMT_Term.mkImp _147_1499))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_147_1500)))
in (mkForall_fuel _147_1501))
in ((_147_1502), (Some ("ref inversion"))))
in FStar_ToSMT_Term.Assume (_147_1503))
in (let _147_1515 = (let _147_1514 = (let _147_1513 = (let _147_1512 = (let _147_1511 = (let _147_1510 = (let _147_1509 = (let _147_1508 = (FStar_ToSMT_Term.mkAnd ((typing_pred), (typing_pred_b)))
in (let _147_1507 = (let _147_1506 = (let _147_1505 = (FStar_ToSMT_Term.mkFreeV aa)
in (let _147_1504 = (FStar_ToSMT_Term.mkFreeV bb)
in ((_147_1505), (_147_1504))))
in (FStar_ToSMT_Term.mkEq _147_1506))
in ((_147_1508), (_147_1507))))
in (FStar_ToSMT_Term.mkImp _147_1509))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_147_1510)))
in (mkForall_fuel' (Prims.parse_int "2") _147_1511))
in ((_147_1512), (Some ("ref typing is injective"))))
in FStar_ToSMT_Term.Assume (_147_1513))
in (_147_1514)::[])
in (_147_1516)::_147_1515))))))))))
in (

let mk_false_interp = (fun _50_2182 false_tm -> (

let valid = (FStar_ToSMT_Term.mkApp (("Valid"), ((false_tm)::[])))
in (let _147_1523 = (let _147_1522 = (let _147_1521 = (FStar_ToSMT_Term.mkIff ((FStar_ToSMT_Term.mkFalse), (valid)))
in ((_147_1521), (Some ("False interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1522))
in (_147_1523)::[])))
in (

let mk_and_interp = (fun conj _50_2188 -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _147_1530 = (let _147_1529 = (let _147_1528 = (FStar_ToSMT_Term.mkApp ((conj), ((a)::(b)::[])))
in (_147_1528)::[])
in (("Valid"), (_147_1529)))
in (FStar_ToSMT_Term.mkApp _147_1530))
in (

let valid_a = (FStar_ToSMT_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_ToSMT_Term.mkApp (("Valid"), ((b)::[])))
in (let _147_1537 = (let _147_1536 = (let _147_1535 = (let _147_1534 = (let _147_1533 = (let _147_1532 = (let _147_1531 = (FStar_ToSMT_Term.mkAnd ((valid_a), (valid_b)))
in ((_147_1531), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1532))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_147_1533)))
in (FStar_ToSMT_Term.mkForall _147_1534))
in ((_147_1535), (Some ("/\\ interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1536))
in (_147_1537)::[])))))))))
in (

let mk_or_interp = (fun disj _50_2199 -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _147_1544 = (let _147_1543 = (let _147_1542 = (FStar_ToSMT_Term.mkApp ((disj), ((a)::(b)::[])))
in (_147_1542)::[])
in (("Valid"), (_147_1543)))
in (FStar_ToSMT_Term.mkApp _147_1544))
in (

let valid_a = (FStar_ToSMT_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_ToSMT_Term.mkApp (("Valid"), ((b)::[])))
in (let _147_1551 = (let _147_1550 = (let _147_1549 = (let _147_1548 = (let _147_1547 = (let _147_1546 = (let _147_1545 = (FStar_ToSMT_Term.mkOr ((valid_a), (valid_b)))
in ((_147_1545), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1546))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_147_1547)))
in (FStar_ToSMT_Term.mkForall _147_1548))
in ((_147_1549), (Some ("\\/ interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1550))
in (_147_1551)::[])))))))))
in (

let mk_eq2_interp = (fun eq2 tt -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let xx = (("x"), (FStar_ToSMT_Term.Term_sort))
in (

let yy = (("y"), (FStar_ToSMT_Term.Term_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let y = (FStar_ToSMT_Term.mkFreeV yy)
in (

let valid = (let _147_1558 = (let _147_1557 = (let _147_1556 = (FStar_ToSMT_Term.mkApp ((eq2), ((a)::(b)::(x)::(y)::[])))
in (_147_1556)::[])
in (("Valid"), (_147_1557)))
in (FStar_ToSMT_Term.mkApp _147_1558))
in (let _147_1565 = (let _147_1564 = (let _147_1563 = (let _147_1562 = (let _147_1561 = (let _147_1560 = (let _147_1559 = (FStar_ToSMT_Term.mkEq ((x), (y)))
in ((_147_1559), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1560))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_147_1561)))
in (FStar_ToSMT_Term.mkForall _147_1562))
in ((_147_1563), (Some ("Eq2 interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1564))
in (_147_1565)::[])))))))))))
in (

let mk_imp_interp = (fun imp tt -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _147_1572 = (let _147_1571 = (let _147_1570 = (FStar_ToSMT_Term.mkApp ((imp), ((a)::(b)::[])))
in (_147_1570)::[])
in (("Valid"), (_147_1571)))
in (FStar_ToSMT_Term.mkApp _147_1572))
in (

let valid_a = (FStar_ToSMT_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_ToSMT_Term.mkApp (("Valid"), ((b)::[])))
in (let _147_1579 = (let _147_1578 = (let _147_1577 = (let _147_1576 = (let _147_1575 = (let _147_1574 = (let _147_1573 = (FStar_ToSMT_Term.mkImp ((valid_a), (valid_b)))
in ((_147_1573), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1574))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_147_1575)))
in (FStar_ToSMT_Term.mkForall _147_1576))
in ((_147_1577), (Some ("==> interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1578))
in (_147_1579)::[])))))))))
in (

let mk_iff_interp = (fun iff tt -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _147_1586 = (let _147_1585 = (let _147_1584 = (FStar_ToSMT_Term.mkApp ((iff), ((a)::(b)::[])))
in (_147_1584)::[])
in (("Valid"), (_147_1585)))
in (FStar_ToSMT_Term.mkApp _147_1586))
in (

let valid_a = (FStar_ToSMT_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_ToSMT_Term.mkApp (("Valid"), ((b)::[])))
in (let _147_1593 = (let _147_1592 = (let _147_1591 = (let _147_1590 = (let _147_1589 = (let _147_1588 = (let _147_1587 = (FStar_ToSMT_Term.mkIff ((valid_a), (valid_b)))
in ((_147_1587), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1588))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_147_1589)))
in (FStar_ToSMT_Term.mkForall _147_1590))
in ((_147_1591), (Some ("<==> interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1592))
in (_147_1593)::[])))))))))
in (

let mk_forall_interp = (fun for_all tt -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let xx = (("x"), (FStar_ToSMT_Term.Term_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let valid = (let _147_1600 = (let _147_1599 = (let _147_1598 = (FStar_ToSMT_Term.mkApp ((for_all), ((a)::(b)::[])))
in (_147_1598)::[])
in (("Valid"), (_147_1599)))
in (FStar_ToSMT_Term.mkApp _147_1600))
in (

let valid_b_x = (let _147_1603 = (let _147_1602 = (let _147_1601 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_147_1601)::[])
in (("Valid"), (_147_1602)))
in (FStar_ToSMT_Term.mkApp _147_1603))
in (let _147_1617 = (let _147_1616 = (let _147_1615 = (let _147_1614 = (let _147_1613 = (let _147_1612 = (let _147_1611 = (let _147_1610 = (let _147_1609 = (let _147_1605 = (let _147_1604 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_147_1604)::[])
in (_147_1605)::[])
in (let _147_1608 = (let _147_1607 = (let _147_1606 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in ((_147_1606), (valid_b_x)))
in (FStar_ToSMT_Term.mkImp _147_1607))
in ((_147_1609), ((xx)::[]), (_147_1608))))
in (FStar_ToSMT_Term.mkForall _147_1610))
in ((_147_1611), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1612))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_147_1613)))
in (FStar_ToSMT_Term.mkForall _147_1614))
in ((_147_1615), (Some ("forall interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1616))
in (_147_1617)::[]))))))))))
in (

let mk_exists_interp = (fun for_all tt -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let xx = (("x"), (FStar_ToSMT_Term.Term_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let valid = (let _147_1624 = (let _147_1623 = (let _147_1622 = (FStar_ToSMT_Term.mkApp ((for_all), ((a)::(b)::[])))
in (_147_1622)::[])
in (("Valid"), (_147_1623)))
in (FStar_ToSMT_Term.mkApp _147_1624))
in (

let valid_b_x = (let _147_1627 = (let _147_1626 = (let _147_1625 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_147_1625)::[])
in (("Valid"), (_147_1626)))
in (FStar_ToSMT_Term.mkApp _147_1627))
in (let _147_1641 = (let _147_1640 = (let _147_1639 = (let _147_1638 = (let _147_1637 = (let _147_1636 = (let _147_1635 = (let _147_1634 = (let _147_1633 = (let _147_1629 = (let _147_1628 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_147_1628)::[])
in (_147_1629)::[])
in (let _147_1632 = (let _147_1631 = (let _147_1630 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in ((_147_1630), (valid_b_x)))
in (FStar_ToSMT_Term.mkImp _147_1631))
in ((_147_1633), ((xx)::[]), (_147_1632))))
in (FStar_ToSMT_Term.mkExists _147_1634))
in ((_147_1635), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1636))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_147_1637)))
in (FStar_ToSMT_Term.mkForall _147_1638))
in ((_147_1639), (Some ("exists interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1640))
in (_147_1641)::[]))))))))))
in (

let mk_foralltyp_interp = (fun for_all tt -> (

let kk = (("k"), (FStar_ToSMT_Term.Kind_sort))
in (

let aa = (("aa"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("bb"), (FStar_ToSMT_Term.Term_sort))
in (

let k = (FStar_ToSMT_Term.mkFreeV kk)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _147_1648 = (let _147_1647 = (let _147_1646 = (FStar_ToSMT_Term.mkApp ((for_all), ((k)::(a)::[])))
in (_147_1646)::[])
in (("Valid"), (_147_1647)))
in (FStar_ToSMT_Term.mkApp _147_1648))
in (

let valid_a_b = (let _147_1651 = (let _147_1650 = (let _147_1649 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_147_1649)::[])
in (("Valid"), (_147_1650)))
in (FStar_ToSMT_Term.mkApp _147_1651))
in (let _147_1665 = (let _147_1664 = (let _147_1663 = (let _147_1662 = (let _147_1661 = (let _147_1660 = (let _147_1659 = (let _147_1658 = (let _147_1657 = (let _147_1653 = (let _147_1652 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_147_1652)::[])
in (_147_1653)::[])
in (let _147_1656 = (let _147_1655 = (let _147_1654 = (FStar_ToSMT_Term.mk_HasKind b k)
in ((_147_1654), (valid_a_b)))
in (FStar_ToSMT_Term.mkImp _147_1655))
in ((_147_1657), ((bb)::[]), (_147_1656))))
in (FStar_ToSMT_Term.mkForall _147_1658))
in ((_147_1659), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1660))
in ((((valid)::[])::[]), ((kk)::(aa)::[]), (_147_1661)))
in (FStar_ToSMT_Term.mkForall _147_1662))
in ((_147_1663), (Some ("ForallTyp interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1664))
in (_147_1665)::[]))))))))))
in (

let mk_existstyp_interp = (fun for_some tt -> (

let kk = (("k"), (FStar_ToSMT_Term.Kind_sort))
in (

let aa = (("aa"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("bb"), (FStar_ToSMT_Term.Term_sort))
in (

let k = (FStar_ToSMT_Term.mkFreeV kk)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _147_1672 = (let _147_1671 = (let _147_1670 = (FStar_ToSMT_Term.mkApp ((for_some), ((k)::(a)::[])))
in (_147_1670)::[])
in (("Valid"), (_147_1671)))
in (FStar_ToSMT_Term.mkApp _147_1672))
in (

let valid_a_b = (let _147_1675 = (let _147_1674 = (let _147_1673 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_147_1673)::[])
in (("Valid"), (_147_1674)))
in (FStar_ToSMT_Term.mkApp _147_1675))
in (let _147_1689 = (let _147_1688 = (let _147_1687 = (let _147_1686 = (let _147_1685 = (let _147_1684 = (let _147_1683 = (let _147_1682 = (let _147_1681 = (let _147_1677 = (let _147_1676 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_147_1676)::[])
in (_147_1677)::[])
in (let _147_1680 = (let _147_1679 = (let _147_1678 = (FStar_ToSMT_Term.mk_HasKind b k)
in ((_147_1678), (valid_a_b)))
in (FStar_ToSMT_Term.mkImp _147_1679))
in ((_147_1681), ((bb)::[]), (_147_1680))))
in (FStar_ToSMT_Term.mkExists _147_1682))
in ((_147_1683), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1684))
in ((((valid)::[])::[]), ((kk)::(aa)::[]), (_147_1685)))
in (FStar_ToSMT_Term.mkForall _147_1686))
in ((_147_1687), (Some ("ExistsTyp interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1688))
in (_147_1689)::[]))))))))))
in (

let prims = (((FStar_Absyn_Const.unit_lid), (mk_unit)))::(((FStar_Absyn_Const.bool_lid), (mk_bool)))::(((FStar_Absyn_Const.int_lid), (mk_int)))::(((FStar_Absyn_Const.string_lid), (mk_str)))::(((FStar_Absyn_Const.ref_lid), (mk_ref)))::(((FStar_Absyn_Const.false_lid), (mk_false_interp)))::(((FStar_Absyn_Const.and_lid), (mk_and_interp)))::(((FStar_Absyn_Const.or_lid), (mk_or_interp)))::(((FStar_Absyn_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Absyn_Const.imp_lid), (mk_imp_interp)))::(((FStar_Absyn_Const.iff_lid), (mk_iff_interp)))::(((FStar_Absyn_Const.forall_lid), (mk_forall_interp)))::(((FStar_Absyn_Const.exists_lid), (mk_exists_interp)))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _50_2292 -> (match (_50_2292) with
| (l, _50_2291) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_50_2295, f) -> begin
(f s tt)
end)))))))))))))))))))))))


let rec encode_sigelt : env_t  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_ToSMT_Term.decls_t * env_t) = (fun env se -> (

let _50_2301 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _147_1820 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _147_1820))
end else begin
()
end
in (

let nm = (match ((FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (

let _50_2309 = (encode_sigelt' env se)
in (match (_50_2309) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _147_1823 = (let _147_1822 = (let _147_1821 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_ToSMT_Term.Caption (_147_1821))
in (_147_1822)::[])
in ((_147_1823), (e)))
end
| _50_2312 -> begin
(let _147_1830 = (let _147_1829 = (let _147_1825 = (let _147_1824 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_147_1824))
in (_147_1825)::g)
in (let _147_1828 = (let _147_1827 = (let _147_1826 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_147_1826))
in (_147_1827)::[])
in (FStar_List.append _147_1829 _147_1828)))
in ((_147_1830), (e)))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_ToSMT_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> ((((FStar_Util.starts_with l.FStar_Ident.str "Prims.pure_") || (FStar_Util.starts_with l.FStar_Ident.str "Prims.ex_")) || (FStar_Util.starts_with l.FStar_Ident.str "Prims.st_")) || (FStar_Util.starts_with l.FStar_Ident.str "Prims.all_")))
in (

let encode_top_level_val = (fun env lid t quals -> (

let tt = (whnf env t)
in (

let _50_2325 = (encode_free_var env lid t tt quals)
in (match (_50_2325) with
| (decls, env) -> begin
if (FStar_Absyn_Util.is_smt_lemma t) then begin
(let _147_1844 = (let _147_1843 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _147_1843))
in ((_147_1844), (env)))
end else begin
((decls), (env))
end
end))))
in (

let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _50_2332 lb -> (match (_50_2332) with
| (decls, env) -> begin
(

let _50_2336 = (let _147_1853 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (encode_top_level_val env _147_1853 lb.FStar_Absyn_Syntax.lbtyp quals))
in (match (_50_2336) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))
in (match (se) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_50_2338, _50_2340, _50_2342, _50_2344, (FStar_Absyn_Syntax.Effect)::[], _50_2348) -> begin
(([]), (env))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _50_2353, _50_2355, _50_2357, _50_2359, _50_2361) when (should_skip lid) -> begin
(([]), (env))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _50_2366, _50_2368, _50_2370, _50_2372, _50_2374) when (FStar_Ident.lid_equals lid FStar_Absyn_Const.b2t_lid) -> begin
(

let _50_2380 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_50_2380) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_ToSMT_Term.Term_sort))
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let valid_b2t_x = (let _147_1856 = (let _147_1855 = (let _147_1854 = (FStar_ToSMT_Term.mkApp (("Prims.b2t"), ((x)::[])))
in (_147_1854)::[])
in (("Valid"), (_147_1855)))
in (FStar_ToSMT_Term.mkApp _147_1856))
in (

let decls = (let _147_1864 = (let _147_1863 = (let _147_1862 = (let _147_1861 = (let _147_1860 = (let _147_1859 = (let _147_1858 = (let _147_1857 = (FStar_ToSMT_Term.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_147_1857)))
in (FStar_ToSMT_Term.mkEq _147_1858))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_147_1859)))
in (FStar_ToSMT_Term.mkForall _147_1860))
in ((_147_1861), (Some ("b2t def"))))
in FStar_ToSMT_Term.Assume (_147_1862))
in (_147_1863)::[])
in (FStar_ToSMT_Term.DeclFun (((tname), ((FStar_ToSMT_Term.Term_sort)::[]), (FStar_ToSMT_Term.Type_sort), (None))))::_147_1864)
in ((decls), (env))))))
end))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _50_2388, t, tags, _50_2392) -> begin
(

let _50_2398 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_50_2398) with
| (tname, ttok, env) -> begin
(

let _50_2407 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (tps', body) -> begin
(((FStar_List.append tps tps')), (body))
end
| _50_2404 -> begin
((tps), (t))
end)
in (match (_50_2407) with
| (tps, t) -> begin
(

let _50_2414 = (encode_binders None tps env)
in (match (_50_2414) with
| (vars, guards, env', binder_decls, _50_2413) -> begin
(

let tok_app = (let _147_1865 = (FStar_ToSMT_Term.mkApp ((ttok), ([])))
in (mk_ApplyT _147_1865 vars))
in (

let tok_decl = FStar_ToSMT_Term.DeclFun (((ttok), ([]), (FStar_ToSMT_Term.Type_sort), (None)))
in (

let app = (let _147_1867 = (let _147_1866 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in ((tname), (_147_1866)))
in (FStar_ToSMT_Term.mkApp _147_1867))
in (

let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _50_2420 -> begin
(let _147_1869 = (let _147_1868 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token ((ttok), (FStar_ToSMT_Term.Type_sort)) _147_1868))
in (_147_1869)::[])
end)
in (

let decls = (let _147_1880 = (let _147_1872 = (let _147_1871 = (let _147_1870 = (FStar_List.map Prims.snd vars)
in ((tname), (_147_1870), (FStar_ToSMT_Term.Type_sort), (None)))
in FStar_ToSMT_Term.DeclFun (_147_1871))
in (_147_1872)::(tok_decl)::[])
in (let _147_1879 = (let _147_1878 = (let _147_1877 = (let _147_1876 = (let _147_1875 = (let _147_1874 = (let _147_1873 = (FStar_ToSMT_Term.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (vars), (_147_1873)))
in (FStar_ToSMT_Term.mkForall _147_1874))
in ((_147_1875), (Some ("name-token correspondence"))))
in FStar_ToSMT_Term.Assume (_147_1876))
in (_147_1877)::[])
in (FStar_List.append fresh_tok _147_1878))
in (FStar_List.append _147_1880 _147_1879)))
in (

let t = if (FStar_All.pipe_right tags (FStar_List.contains FStar_Absyn_Syntax.Opaque)) then begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
end else begin
(whnf env t)
end
in (

let _50_2432 = if (FStar_All.pipe_right tags (FStar_Util.for_some (fun _50_19 -> (match (_50_19) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _50_2427 -> begin
false
end)))) then begin
(let _147_1883 = (FStar_ToSMT_Term.mk_Valid app)
in (let _147_1882 = (encode_formula t env')
in ((_147_1883), (_147_1882))))
end else begin
(let _147_1884 = (encode_typ_term t env')
in ((app), (_147_1884)))
end
in (match (_50_2432) with
| (def, (body, decls1)) -> begin
(

let abbrev_def = (let _147_1891 = (let _147_1890 = (let _147_1889 = (let _147_1888 = (let _147_1887 = (let _147_1886 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _147_1885 = (FStar_ToSMT_Term.mkEq ((def), (body)))
in ((_147_1886), (_147_1885))))
in (FStar_ToSMT_Term.mkImp _147_1887))
in ((((def)::[])::[]), (vars), (_147_1888)))
in (FStar_ToSMT_Term.mkForall _147_1889))
in ((_147_1890), (Some ("abbrev. elimination"))))
in FStar_ToSMT_Term.Assume (_147_1891))
in (

let kindingAx = (

let _50_2436 = (let _147_1892 = (FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _147_1892 env' app))
in (match (_50_2436) with
| (k, decls) -> begin
(let _147_1900 = (let _147_1899 = (let _147_1898 = (let _147_1897 = (let _147_1896 = (let _147_1895 = (let _147_1894 = (let _147_1893 = (FStar_ToSMT_Term.mk_and_l guards)
in ((_147_1893), (k)))
in (FStar_ToSMT_Term.mkImp _147_1894))
in ((((app)::[])::[]), (vars), (_147_1895)))
in (FStar_ToSMT_Term.mkForall _147_1896))
in ((_147_1897), (Some ("abbrev. kinding"))))
in FStar_ToSMT_Term.Assume (_147_1898))
in (_147_1899)::[])
in (FStar_List.append decls _147_1900))
end))
in (

let g = (let _147_1904 = (let _147_1903 = (let _147_1902 = (let _147_1901 = (primitive_type_axioms lid tname app)
in (FStar_List.append ((abbrev_def)::kindingAx) _147_1901))
in (FStar_List.append decls1 _147_1902))
in (FStar_List.append decls _147_1903))
in (FStar_List.append binder_decls _147_1904))
in ((g), (env)))))
end))))))))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _50_2443) -> begin
if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || env.tcenv.FStar_Tc_Env.is_iface) then begin
(encode_top_level_val env lid t quals)
end else begin
(([]), (env))
end
end
| FStar_Absyn_Syntax.Sig_assume (l, f, _50_2449, _50_2451) -> begin
(

let _50_2456 = (encode_formula f env)
in (match (_50_2456) with
| (f, decls) -> begin
(

let g = (let _147_1909 = (let _147_1908 = (let _147_1907 = (let _147_1906 = (let _147_1905 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "Assumption: %s" _147_1905))
in Some (_147_1906))
in ((f), (_147_1907)))
in FStar_ToSMT_Term.Assume (_147_1908))
in (_147_1909)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _50_2462, datas, quals, _50_2466) when (FStar_Ident.lid_equals t FStar_Absyn_Const.precedes_lid) -> begin
(

let _50_2472 = (new_typ_constant_and_tok_from_lid env t)
in (match (_50_2472) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, _50_2475, _50_2477, _50_2479, _50_2481, _50_2483, _50_2485) when ((FStar_Ident.lid_equals t FStar_Absyn_Const.char_lid) || (FStar_Ident.lid_equals t FStar_Absyn_Const.uint8_lid)) -> begin
(

let tname = t.FStar_Ident.str
in (

let tsym = (FStar_ToSMT_Term.mkFreeV ((tname), (FStar_ToSMT_Term.Type_sort)))
in (

let decl = FStar_ToSMT_Term.DeclFun (((tname), ([]), (FStar_ToSMT_Term.Type_sort), (None)))
in (let _147_1911 = (let _147_1910 = (primitive_type_axioms t tname tsym)
in (decl)::_147_1910)
in ((_147_1911), ((push_free_tvar env t tname (Some (tsym)))))))))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _50_2495, datas, quals, _50_2499) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _50_20 -> (match (_50_20) with
| (FStar_Absyn_Syntax.Logic) | (FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _50_2506 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _50_2516 = c
in (match (_50_2516) with
| (name, args, _50_2513, _50_2515) -> begin
(let _147_1917 = (let _147_1916 = (let _147_1915 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_147_1915), (FStar_ToSMT_Term.Type_sort), (None)))
in FStar_ToSMT_Term.DeclFun (_147_1916))
in (_147_1917)::[])
end))
end else begin
(FStar_ToSMT_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (((FStar_List.length datas) = (Prims.parse_int "0")) || (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _147_1923 = (FStar_Tc_Env.lookup_qname env.tcenv l)
in (FStar_All.pipe_right _147_1923 FStar_Option.isNone)))))) then begin
[]
end else begin
(

let _50_2523 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_50_2523) with
| (xxsym, xx) -> begin
(

let _50_2566 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _50_2526 l -> (match (_50_2526) with
| (out, decls) -> begin
(

let data_t = (FStar_Tc_Env.lookup_datacon env.tcenv l)
in (

let _50_2536 = (match ((FStar_Absyn_Util.function_formals data_t)) with
| Some (formals, res) -> begin
((formals), ((FStar_Absyn_Util.comp_result res)))
end
| None -> begin
(([]), (data_t))
end)
in (match (_50_2536) with
| (args, res) -> begin
(

let indices = (match ((let _147_1926 = (FStar_Absyn_Util.compress_typ res)
in _147_1926.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (_50_2538, indices) -> begin
indices
end
| _50_2543 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (a) -> begin
(let _147_1931 = (let _147_1930 = (let _147_1929 = (mk_typ_projector_name l a.FStar_Absyn_Syntax.v)
in ((_147_1929), ((xx)::[])))
in (FStar_ToSMT_Term.mkApp _147_1930))
in (push_typ_var env a.FStar_Absyn_Syntax.v _147_1931))
end
| FStar_Util.Inr (x) -> begin
(let _147_1934 = (let _147_1933 = (let _147_1932 = (mk_term_projector_name l x.FStar_Absyn_Syntax.v)
in ((_147_1932), ((xx)::[])))
in (FStar_ToSMT_Term.mkApp _147_1933))
in (push_term_var env x.FStar_Absyn_Syntax.v _147_1934))
end)) env))
in (

let _50_2554 = (encode_args indices env)
in (match (_50_2554) with
| (indices, decls') -> begin
(

let _50_2555 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _147_1941 = (FStar_List.map2 (fun v a -> (match (a) with
| FStar_Util.Inl (a) -> begin
(let _147_1938 = (let _147_1937 = (FStar_ToSMT_Term.mkFreeV v)
in ((_147_1937), (a)))
in (FStar_ToSMT_Term.mkEq _147_1938))
end
| FStar_Util.Inr (a) -> begin
(let _147_1940 = (let _147_1939 = (FStar_ToSMT_Term.mkFreeV v)
in ((_147_1939), (a)))
in (FStar_ToSMT_Term.mkEq _147_1940))
end)) vars indices)
in (FStar_All.pipe_right _147_1941 FStar_ToSMT_Term.mk_and_l))
in (let _147_1946 = (let _147_1945 = (let _147_1944 = (let _147_1943 = (let _147_1942 = (mk_data_tester env l xx)
in ((_147_1942), (eqs)))
in (FStar_ToSMT_Term.mkAnd _147_1943))
in ((out), (_147_1944)))
in (FStar_ToSMT_Term.mkOr _147_1945))
in ((_147_1946), ((FStar_List.append decls decls'))))))
end))))
end)))
end)) ((FStar_ToSMT_Term.mkFalse), ([]))))
in (match (_50_2566) with
| (data_ax, decls) -> begin
(

let _50_2569 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2569) with
| (ffsym, ff) -> begin
(

let xx_has_type = (let _147_1947 = (FStar_ToSMT_Term.mkApp (("SFuel"), ((ff)::[])))
in (FStar_ToSMT_Term.mk_HasTypeFuel _147_1947 xx tapp))
in (let _147_1954 = (let _147_1953 = (let _147_1952 = (let _147_1951 = (let _147_1950 = (let _147_1949 = (add_fuel ((ffsym), (FStar_ToSMT_Term.Fuel_sort)) ((((xxsym), (FStar_ToSMT_Term.Term_sort)))::vars))
in (let _147_1948 = (FStar_ToSMT_Term.mkImp ((xx_has_type), (data_ax)))
in ((((xx_has_type)::[])::[]), (_147_1949), (_147_1948))))
in (FStar_ToSMT_Term.mkForall _147_1950))
in ((_147_1951), (Some ("inversion axiom"))))
in FStar_ToSMT_Term.Assume (_147_1952))
in (_147_1953)::[])
in (FStar_List.append decls _147_1954)))
end))
end))
end))
end)
in (

let k = (FStar_Absyn_Util.close_kind tps k)
in (

let _50_2581 = (match ((let _147_1955 = (FStar_Absyn_Util.compress_kind k)
in _147_1955.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_arrow (bs, res) -> begin
((true), (bs), (res))
end
| _50_2577 -> begin
((false), ([]), (k))
end)
in (match (_50_2581) with
| (is_kind_arrow, formals, res) -> begin
(

let _50_2588 = (encode_binders None formals env)
in (match (_50_2588) with
| (vars, guards, env', binder_decls, _50_2587) -> begin
(

let projection_axioms = (fun tapp vars -> (match ((FStar_All.pipe_right quals (FStar_Util.find_opt (fun _50_21 -> (match (_50_21) with
| FStar_Absyn_Syntax.Projector (_50_2594) -> begin
true
end
| _50_2597 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.Projector (d, FStar_Util.Inl (a))) -> begin
(

let rec projectee = (fun i _50_22 -> (match (_50_22) with
| [] -> begin
i
end
| (f)::tl -> begin
(match ((Prims.fst f)) with
| FStar_Util.Inl (_50_2612) -> begin
(projectee (i + (Prims.parse_int "1")) tl)
end
| FStar_Util.Inr (x) -> begin
if (x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = "projectee") then begin
i
end else begin
(projectee (i + (Prims.parse_int "1")) tl)
end
end)
end))
in (

let projectee_pos = (projectee (Prims.parse_int "0") formals)
in (

let _50_2627 = (match ((FStar_Util.first_N projectee_pos vars)) with
| (_50_2618, (xx)::suffix) -> begin
((xx), (suffix))
end
| _50_2624 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_50_2627) with
| (xx, suffix) -> begin
(

let dproj_app = (let _147_1969 = (let _147_1968 = (let _147_1967 = (mk_typ_projector_name d a)
in (let _147_1966 = (let _147_1965 = (FStar_ToSMT_Term.mkFreeV xx)
in (_147_1965)::[])
in ((_147_1967), (_147_1966))))
in (FStar_ToSMT_Term.mkApp _147_1968))
in (mk_ApplyT _147_1969 suffix))
in (let _147_1974 = (let _147_1973 = (let _147_1972 = (let _147_1971 = (let _147_1970 = (FStar_ToSMT_Term.mkEq ((tapp), (dproj_app)))
in ((((tapp)::[])::[]), (vars), (_147_1970)))
in (FStar_ToSMT_Term.mkForall _147_1971))
in ((_147_1972), (Some ("projector axiom"))))
in FStar_ToSMT_Term.Assume (_147_1973))
in (_147_1974)::[]))
end))))
end
| _50_2630 -> begin
[]
end))
in (

let pretype_axioms = (fun tapp vars -> (

let _50_2636 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_50_2636) with
| (xxsym, xx) -> begin
(

let _50_2639 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2639) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _147_1987 = (let _147_1986 = (let _147_1985 = (let _147_1984 = (let _147_1983 = (let _147_1982 = (let _147_1981 = (let _147_1980 = (let _147_1979 = (FStar_ToSMT_Term.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_147_1979)))
in (FStar_ToSMT_Term.mkEq _147_1980))
in ((xx_has_type), (_147_1981)))
in (FStar_ToSMT_Term.mkImp _147_1982))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_ToSMT_Term.Term_sort)))::(((ffsym), (FStar_ToSMT_Term.Fuel_sort)))::vars), (_147_1983)))
in (FStar_ToSMT_Term.mkForall _147_1984))
in ((_147_1985), (Some ("pretyping"))))
in FStar_ToSMT_Term.Assume (_147_1986))
in (_147_1987)::[]))
end))
end)))
in (

let _50_2644 = (new_typ_constant_and_tok_from_lid env t)
in (match (_50_2644) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_ToSMT_Term.mkApp ((ttok), ([])))
in (

let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (

let tapp = (let _147_1989 = (let _147_1988 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in ((tname), (_147_1988)))
in (FStar_ToSMT_Term.mkApp _147_1989))
in (

let _50_2665 = (

let tname_decl = (let _147_1993 = (let _147_1992 = (FStar_All.pipe_right vars (FStar_List.map (fun _50_2650 -> (match (_50_2650) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _147_1991 = (varops.next_id ())
in ((tname), (_147_1992), (FStar_ToSMT_Term.Type_sort), (_147_1991))))
in (constructor_or_logic_type_decl _147_1993))
in (

let _50_2662 = (match (vars) with
| [] -> begin
(let _147_1997 = (let _147_1996 = (let _147_1995 = (FStar_ToSMT_Term.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _147_1994 -> Some (_147_1994)) _147_1995))
in (push_free_tvar env t tname _147_1996))
in (([]), (_147_1997)))
end
| _50_2654 -> begin
(

let ttok_decl = FStar_ToSMT_Term.DeclFun (((ttok), ([]), (FStar_ToSMT_Term.Type_sort), (Some ("token"))))
in (

let ttok_fresh = (let _147_1998 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token ((ttok), (FStar_ToSMT_Term.Type_sort)) _147_1998))
in (

let ttok_app = (mk_ApplyT ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _147_2002 = (let _147_2001 = (let _147_2000 = (let _147_1999 = (FStar_ToSMT_Term.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_147_1999)))
in (FStar_ToSMT_Term.mkForall' _147_2000))
in ((_147_2001), (Some ("name-token correspondence"))))
in FStar_ToSMT_Term.Assume (_147_2002))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (_50_2662) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (_50_2665) with
| (decls, env) -> begin
(

let kindingAx = (

let _50_2668 = (encode_knd res env' tapp)
in (match (_50_2668) with
| (k, decls) -> begin
(

let karr = if is_kind_arrow then begin
(let _147_2006 = (let _147_2005 = (let _147_2004 = (let _147_2003 = (FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _147_2003))
in ((_147_2004), (Some ("kinding"))))
in FStar_ToSMT_Term.Assume (_147_2005))
in (_147_2006)::[])
end else begin
[]
end
in (let _147_2013 = (let _147_2012 = (let _147_2011 = (let _147_2010 = (let _147_2009 = (let _147_2008 = (let _147_2007 = (FStar_ToSMT_Term.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_147_2007)))
in (FStar_ToSMT_Term.mkForall _147_2008))
in ((_147_2009), (Some ("kinding"))))
in FStar_ToSMT_Term.Assume (_147_2010))
in (_147_2011)::[])
in (FStar_List.append karr _147_2012))
in (FStar_List.append decls _147_2013)))
end))
in (

let aux = if is_logical then begin
(let _147_2014 = (projection_axioms tapp vars)
in (FStar_List.append kindingAx _147_2014))
end else begin
(let _147_2021 = (let _147_2020 = (primitive_type_axioms t tname tapp)
in (let _147_2019 = (let _147_2018 = (inversion_axioms tapp vars)
in (let _147_2017 = (let _147_2016 = (projection_axioms tapp vars)
in (let _147_2015 = (pretype_axioms tapp vars)
in (FStar_List.append _147_2016 _147_2015)))
in (FStar_List.append _147_2018 _147_2017)))
in (FStar_List.append _147_2020 _147_2019)))
in (FStar_List.append kindingAx _147_2021))
end
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))))
end))
end))))))
end
| FStar_Absyn_Syntax.Sig_datacon (d, _50_2675, _50_2677, _50_2679, _50_2681, _50_2683) when (FStar_Ident.lid_equals d FStar_Absyn_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Absyn_Syntax.Sig_datacon (d, t, (_50_2689, tps, _50_2692), quals, _50_2696, drange) -> begin
(

let t = (let _147_2023 = (FStar_List.map (fun _50_2703 -> (match (_50_2703) with
| (x, _50_2702) -> begin
((x), (Some (FStar_Absyn_Syntax.Implicit (true))))
end)) tps)
in (FStar_Absyn_Util.close_typ _147_2023 t))
in (

let _50_2708 = (new_term_constant_and_tok_from_lid env d)
in (match (_50_2708) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_ToSMT_Term.mkApp ((ddtok), ([])))
in (

let _50_2717 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
((f), ((FStar_Absyn_Util.comp_result c)))
end
| None -> begin
(([]), (t))
end)
in (match (_50_2717) with
| (formals, t_res) -> begin
(

let _50_2720 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2720) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_ToSMT_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let _50_2727 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_50_2727) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun _50_23 -> (match (_50_23) with
| FStar_Util.Inl (a) -> begin
(let _147_2025 = (mk_typ_projector_name d a)
in ((_147_2025), (FStar_ToSMT_Term.Type_sort)))
end
| FStar_Util.Inr (x) -> begin
(let _147_2026 = (mk_term_projector_name d x)
in ((_147_2026), (FStar_ToSMT_Term.Term_sort)))
end))))
in (

let datacons = (let _147_2028 = (let _147_2027 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_ToSMT_Term.Term_sort), (_147_2027)))
in (FStar_All.pipe_right _147_2028 FStar_ToSMT_Term.constructor_to_decl))
in (

let app = (mk_ApplyE ddtok_tm vars)
in (

let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let dapp = (FStar_ToSMT_Term.mkApp ((ddconstrsym), (xvars)))
in (

let _50_2741 = (encode_typ_pred None t env ddtok_tm)
in (match (_50_2741) with
| (tok_typing, decls3) -> begin
(

let _50_2748 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_50_2748) with
| (vars', guards', env'', decls_formals, _50_2747) -> begin
(

let _50_2753 = (

let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars')
in (

let dapp = (FStar_ToSMT_Term.mkApp ((ddconstrsym), (xvars)))
in (encode_typ_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_50_2753) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_ToSMT_Term.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _50_2757 -> begin
(let _147_2030 = (let _147_2029 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token ((ddtok), (FStar_ToSMT_Term.Term_sort)) _147_2029))
in (_147_2030)::[])
end)
in (

let encode_elim = (fun _50_2760 -> (match (()) with
| () -> begin
(

let _50_2763 = (FStar_Absyn_Util.head_and_args t_res)
in (match (_50_2763) with
| (head, args) -> begin
(match ((let _147_2033 = (FStar_Absyn_Util.compress_typ head)
in _147_2033.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(

let encoded_head = (lookup_free_tvar_name env' fv)
in (

let _50_2769 = (encode_args args env')
in (match (_50_2769) with
| (encoded_args, arg_decls) -> begin
(

let _50_2793 = (FStar_List.fold_left (fun _50_2773 arg -> (match (_50_2773) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| FStar_Util.Inl (targ) -> begin
(

let _50_2781 = (let _147_2036 = (FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _147_2036))
in (match (_50_2781) with
| (_50_2778, tv, env) -> begin
(let _147_2038 = (let _147_2037 = (FStar_ToSMT_Term.mkEq ((targ), (tv)))
in (_147_2037)::eqns)
in ((env), ((tv)::arg_vars), (_147_2038)))
end))
end
| FStar_Util.Inr (varg) -> begin
(

let _50_2788 = (let _147_2039 = (FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _147_2039))
in (match (_50_2788) with
| (_50_2785, xv, env) -> begin
(let _147_2041 = (let _147_2040 = (FStar_ToSMT_Term.mkEq ((varg), (xv)))
in (_147_2040)::eqns)
in ((env), ((xv)::arg_vars), (_147_2041)))
end))
end)
end)) ((env'), ([]), ([])) encoded_args)
in (match (_50_2793) with
| (_50_2790, arg_vars, eqns) -> begin
(

let arg_vars = (FStar_List.rev arg_vars)
in (

let ty = (FStar_ToSMT_Term.mkApp ((encoded_head), (arg_vars)))
in (

let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let dapp = (FStar_ToSMT_Term.mkApp ((ddconstrsym), (xvars)))
in (

let ty_pred = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (

let arg_binders = (FStar_List.map FStar_ToSMT_Term.fv_of_term arg_vars)
in (

let typing_inversion = (let _147_2048 = (let _147_2047 = (let _147_2046 = (let _147_2045 = (add_fuel ((fuel_var), (FStar_ToSMT_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _147_2044 = (let _147_2043 = (let _147_2042 = (FStar_ToSMT_Term.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_147_2042)))
in (FStar_ToSMT_Term.mkImp _147_2043))
in ((((ty_pred)::[])::[]), (_147_2045), (_147_2044))))
in (FStar_ToSMT_Term.mkForall _147_2046))
in ((_147_2047), (Some ("data constructor typing elim"))))
in FStar_ToSMT_Term.Assume (_147_2048))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Absyn_Const.lextop_lid) then begin
(

let x = (let _147_2049 = (varops.fresh "x")
in ((_147_2049), (FStar_ToSMT_Term.Term_sort)))
in (

let xtm = (FStar_ToSMT_Term.mkFreeV x)
in (let _147_2059 = (let _147_2058 = (let _147_2057 = (let _147_2056 = (let _147_2051 = (let _147_2050 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_147_2050)::[])
in (_147_2051)::[])
in (let _147_2055 = (let _147_2054 = (let _147_2053 = (FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _147_2052 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in ((_147_2053), (_147_2052))))
in (FStar_ToSMT_Term.mkImp _147_2054))
in ((_147_2056), ((x)::[]), (_147_2055))))
in (FStar_ToSMT_Term.mkForall _147_2057))
in ((_147_2058), (Some ("lextop is top"))))
in FStar_ToSMT_Term.Assume (_147_2059))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| (FStar_ToSMT_Term.Type_sort) | (FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| FStar_ToSMT_Term.Term_sort -> begin
(let _147_2062 = (let _147_2061 = (FStar_ToSMT_Term.mkFreeV v)
in (FStar_ToSMT_Term.mk_Precedes _147_2061 dapp))
in (_147_2062)::[])
end
| _50_2808 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _147_2069 = (let _147_2068 = (let _147_2067 = (let _147_2066 = (add_fuel ((fuel_var), (FStar_ToSMT_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _147_2065 = (let _147_2064 = (let _147_2063 = (FStar_ToSMT_Term.mk_and_l prec)
in ((ty_pred), (_147_2063)))
in (FStar_ToSMT_Term.mkImp _147_2064))
in ((((ty_pred)::[])::[]), (_147_2066), (_147_2065))))
in (FStar_ToSMT_Term.mkForall _147_2067))
in ((_147_2068), (Some ("subterm ordering"))))
in FStar_ToSMT_Term.Assume (_147_2069)))
end
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| _50_2812 -> begin
(

let _50_2813 = (let _147_2072 = (let _147_2071 = (FStar_Absyn_Print.sli d)
in (let _147_2070 = (FStar_Absyn_Print.typ_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _147_2071 _147_2070)))
in (FStar_Tc_Errors.warn drange _147_2072))
in (([]), ([])))
end)
end))
end))
in (

let _50_2817 = (encode_elim ())
in (match (_50_2817) with
| (decls2, elim) -> begin
(

let g = (let _147_2099 = (let _147_2098 = (let _147_2097 = (let _147_2096 = (let _147_2077 = (let _147_2076 = (let _147_2075 = (let _147_2074 = (let _147_2073 = (FStar_Absyn_Print.sli d)
in (FStar_Util.format1 "data constructor proxy: %s" _147_2073))
in Some (_147_2074))
in ((ddtok), ([]), (FStar_ToSMT_Term.Term_sort), (_147_2075)))
in FStar_ToSMT_Term.DeclFun (_147_2076))
in (_147_2077)::[])
in (let _147_2095 = (let _147_2094 = (let _147_2093 = (let _147_2092 = (let _147_2091 = (let _147_2090 = (let _147_2089 = (let _147_2081 = (let _147_2080 = (let _147_2079 = (let _147_2078 = (FStar_ToSMT_Term.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_147_2078)))
in (FStar_ToSMT_Term.mkForall _147_2079))
in ((_147_2080), (Some ("equality for proxy"))))
in FStar_ToSMT_Term.Assume (_147_2081))
in (let _147_2088 = (let _147_2087 = (let _147_2086 = (let _147_2085 = (let _147_2084 = (let _147_2083 = (add_fuel ((fuel_var), (FStar_ToSMT_Term.Fuel_sort)) vars')
in (let _147_2082 = (FStar_ToSMT_Term.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_147_2083), (_147_2082))))
in (FStar_ToSMT_Term.mkForall _147_2084))
in ((_147_2085), (Some ("data constructor typing intro"))))
in FStar_ToSMT_Term.Assume (_147_2086))
in (_147_2087)::[])
in (_147_2089)::_147_2088))
in (FStar_ToSMT_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")))))::_147_2090)
in (FStar_List.append _147_2091 elim))
in (FStar_List.append decls_pred _147_2092))
in (FStar_List.append decls_formals _147_2093))
in (FStar_List.append proxy_fresh _147_2094))
in (FStar_List.append _147_2096 _147_2095)))
in (FStar_List.append decls3 _147_2097))
in (FStar_List.append decls2 _147_2098))
in (FStar_List.append binder_decls _147_2099))
in (((FStar_List.append datacons g)), (env)))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end)))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _50_2821, _50_2823, _50_2825) -> begin
(

let _50_2830 = (encode_signature env ses)
in (match (_50_2830) with
| (g, env) -> begin
(

let _50_2842 = (FStar_All.pipe_right g (FStar_List.partition (fun _50_24 -> (match (_50_24) with
| FStar_ToSMT_Term.Assume (_50_2833, Some ("inversion axiom")) -> begin
false
end
| _50_2839 -> begin
true
end))))
in (match (_50_2842) with
| (g', inversions) -> begin
(

let _50_2851 = (FStar_All.pipe_right g' (FStar_List.partition (fun _50_25 -> (match (_50_25) with
| FStar_ToSMT_Term.DeclFun (_50_2845) -> begin
true
end
| _50_2848 -> begin
false
end))))
in (match (_50_2851) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_let (_50_2853, _50_2855, _50_2857, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _50_26 -> (match (_50_26) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _50_2869 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Absyn_Syntax.Sig_let ((is_rec, bindings), _50_2874, _50_2876, quals) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _50_2888 = (FStar_Util.first_N nbinders formals)
in (match (_50_2888) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun formal binder -> (match ((((Prims.fst formal)), ((Prims.fst binder)))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _147_2114 = (let _147_2113 = (FStar_Absyn_Util.btvar_to_typ b)
in ((a.FStar_Absyn_Syntax.v), (_147_2113)))
in FStar_Util.Inl (_147_2114))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _147_2116 = (let _147_2115 = (FStar_Absyn_Util.bvar_to_exp y)
in ((x.FStar_Absyn_Syntax.v), (_147_2115)))
in FStar_Util.Inr (_147_2116))
end
| _50_2902 -> begin
(FStar_All.failwith "Impossible")
end)) formals binders)
in (

let extra_formals = (let _147_2117 = (FStar_Absyn_Util.subst_binders subst extra_formals)
in (FStar_All.pipe_right _147_2117 FStar_Absyn_Util.name_binders))
in (

let body = (let _147_2123 = (let _147_2119 = (let _147_2118 = (FStar_Absyn_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _147_2118))
in ((body), (_147_2119)))
in (let _147_2122 = (let _147_2121 = (FStar_Absyn_Util.subst_typ subst t)
in (FStar_All.pipe_left (fun _147_2120 -> Some (_147_2120)) _147_2121))
in (FStar_Absyn_Syntax.mk_Exp_app_flat _147_2123 _147_2122 body.FStar_Absyn_Syntax.pos)))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_ascribed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (binders, body); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _, _)) | (FStar_Absyn_Syntax.Exp_abs (binders, body)) -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (FStar_Absyn_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Absyn_Util.is_total_comp c)) then begin
(

let _50_2940 = (FStar_Util.first_N nformals binders)
in (match (_50_2940) with
| (bs0, rest) -> begin
(

let tres = (match ((FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tres)
end
| _50_2944 -> begin
(FStar_All.failwith "impossible")
end)
in (

let body = (FStar_Absyn_Syntax.mk_Exp_abs ((rest), (body)) (Some (tres)) body.FStar_Absyn_Syntax.pos)
in ((bs0), (body), (bs0), (tres))))
end))
end else begin
if (nformals > nbinders) then begin
(

let _50_2949 = (eta_expand binders formals body tres)
in (match (_50_2949) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end))
end else begin
((binders), (body), (formals), (tres))
end
end)))
end
| _50_2951 -> begin
(let _147_2132 = (let _147_2131 = (FStar_Absyn_Print.exp_to_string e)
in (let _147_2130 = (FStar_Absyn_Print.typ_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _147_2131 _147_2130)))
in (FStar_All.failwith _147_2132))
end)
end
| _50_2953 -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(

let tres = (FStar_Absyn_Util.comp_result c)
in (

let _50_2961 = (eta_expand [] formals e tres)
in (match (_50_2961) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end)))
end
| _50_2963 -> begin
(([]), (e), ([]), (t_norm))
end)
end))
in try
(match (()) with
| () -> begin
if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _50_27 -> (match (_50_27) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _50_2976 -> begin
false
end)))) || (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp))))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(

let _50_2995 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _50_2982 lb -> (match (_50_2982) with
| (toks, typs, decls, env) -> begin
(

let _50_2984 = if (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (let _147_2138 = (whnf env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_right _147_2138 FStar_Absyn_Util.compress_typ))
in (

let _50_2990 = (let _147_2139 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _147_2139 lb.FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_50_2990) with
| (tok, decl, env) -> begin
(let _147_2142 = (let _147_2141 = (let _147_2140 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in ((_147_2140), (tok)))
in (_147_2141)::toks)
in ((_147_2142), ((t_norm)::typs), ((decl)::decls), (env)))
end))))
end)) (([]), ([]), ([]), (env))))
in (match (_50_2995) with
| (toks, typs, decls, env) -> begin
(

let toks = (FStar_List.rev toks)
in (

let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _50_28 -> (match (_50_28) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _50_3002 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> ((FStar_Absyn_Util.is_lemma t) || (let _147_2145 = (FStar_Absyn_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _147_2145))))))) then begin
((decls), (env))
end else begin
if (not (is_rec)) then begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Absyn_Syntax.lbname = _50_3010; FStar_Absyn_Syntax.lbtyp = _50_3008; FStar_Absyn_Syntax.lbeff = _50_3006; FStar_Absyn_Syntax.lbdef = e})::[], (t_norm)::[], ((flid, (f, ftok)))::[]) -> begin
(

let _50_3026 = (destruct_bound_function flid t_norm e)
in (match (_50_3026) with
| (binders, body, formals, tres) -> begin
(

let _50_3033 = (encode_binders None binders env)
in (match (_50_3033) with
| (vars, guards, env', binder_decls, _50_3032) -> begin
(

let app = (match (vars) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV ((f), (FStar_ToSMT_Term.Term_sort)))
end
| _50_3036 -> begin
(let _147_2147 = (let _147_2146 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in ((f), (_147_2146)))
in (FStar_ToSMT_Term.mkApp _147_2147))
end)
in (

let _50_3040 = (encode_exp body env')
in (match (_50_3040) with
| (body, decls2) -> begin
(

let eqn = (let _147_2156 = (let _147_2155 = (let _147_2152 = (let _147_2151 = (let _147_2150 = (let _147_2149 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _147_2148 = (FStar_ToSMT_Term.mkEq ((app), (body)))
in ((_147_2149), (_147_2148))))
in (FStar_ToSMT_Term.mkImp _147_2150))
in ((((app)::[])::[]), (vars), (_147_2151)))
in (FStar_ToSMT_Term.mkForall _147_2152))
in (let _147_2154 = (let _147_2153 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_147_2153))
in ((_147_2155), (_147_2154))))
in FStar_ToSMT_Term.Assume (_147_2156))
in (((FStar_List.append decls (FStar_List.append binder_decls (FStar_List.append decls2 ((eqn)::[]))))), (env)))
end)))
end))
end))
end
| _50_3043 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _147_2157 = (varops.fresh "fuel")
in ((_147_2157), (FStar_ToSMT_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_ToSMT_Term.mkFreeV fuel)
in (

let env0 = env
in (

let _50_3060 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _50_3049 _50_3054 -> (match (((_50_3049), (_50_3054))) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(

let g = (varops.new_fvar flid)
in (

let gtok = (varops.new_fvar flid)
in (

let env = (let _147_2162 = (let _147_2161 = (FStar_ToSMT_Term.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _147_2160 -> Some (_147_2160)) _147_2161))
in (push_free_var env flid gtok _147_2162))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env)))))
end)) (([]), (env))))
in (match (_50_3060) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _50_3069 t_norm _50_3078 -> (match (((_50_3069), (_50_3078))) with
| ((flid, f, ftok, g, gtok), {FStar_Absyn_Syntax.lbname = _50_3077; FStar_Absyn_Syntax.lbtyp = _50_3075; FStar_Absyn_Syntax.lbeff = _50_3073; FStar_Absyn_Syntax.lbdef = e}) -> begin
(

let _50_3083 = (destruct_bound_function flid t_norm e)
in (match (_50_3083) with
| (binders, body, formals, tres) -> begin
(

let _50_3090 = (encode_binders None binders env)
in (match (_50_3090) with
| (vars, guards, env', binder_decls, _50_3089) -> begin
(

let decl_g = (let _147_2173 = (let _147_2172 = (let _147_2171 = (FStar_List.map Prims.snd vars)
in (FStar_ToSMT_Term.Fuel_sort)::_147_2171)
in ((g), (_147_2172), (FStar_ToSMT_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_ToSMT_Term.DeclFun (_147_2173))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_ToSMT_Term.DeclFun (((gtok), ([]), (FStar_ToSMT_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let app = (FStar_ToSMT_Term.mkApp ((f), (vars_tm)))
in (

let gsapp = (let _147_2176 = (let _147_2175 = (let _147_2174 = (FStar_ToSMT_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_147_2174)::vars_tm)
in ((g), (_147_2175)))
in (FStar_ToSMT_Term.mkApp _147_2176))
in (

let gmax = (let _147_2179 = (let _147_2178 = (let _147_2177 = (FStar_ToSMT_Term.mkApp (("MaxFuel"), ([])))
in (_147_2177)::vars_tm)
in ((g), (_147_2178)))
in (FStar_ToSMT_Term.mkApp _147_2179))
in (

let _50_3100 = (encode_exp body env')
in (match (_50_3100) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _147_2188 = (let _147_2187 = (let _147_2184 = (let _147_2183 = (let _147_2182 = (let _147_2181 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _147_2180 = (FStar_ToSMT_Term.mkEq ((gsapp), (body_tm)))
in ((_147_2181), (_147_2180))))
in (FStar_ToSMT_Term.mkImp _147_2182))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_147_2183)))
in (FStar_ToSMT_Term.mkForall _147_2184))
in (let _147_2186 = (let _147_2185 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_147_2185))
in ((_147_2187), (_147_2186))))
in FStar_ToSMT_Term.Assume (_147_2188))
in (

let eqn_f = (let _147_2192 = (let _147_2191 = (let _147_2190 = (let _147_2189 = (FStar_ToSMT_Term.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_147_2189)))
in (FStar_ToSMT_Term.mkForall _147_2190))
in ((_147_2191), (Some ("Correspondence of recursive function to instrumented version"))))
in FStar_ToSMT_Term.Assume (_147_2192))
in (

let eqn_g' = (let _147_2201 = (let _147_2200 = (let _147_2199 = (let _147_2198 = (let _147_2197 = (let _147_2196 = (let _147_2195 = (let _147_2194 = (let _147_2193 = (FStar_ToSMT_Term.n_fuel (Prims.parse_int "0"))
in (_147_2193)::vars_tm)
in ((g), (_147_2194)))
in (FStar_ToSMT_Term.mkApp _147_2195))
in ((gsapp), (_147_2196)))
in (FStar_ToSMT_Term.mkEq _147_2197))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_147_2198)))
in (FStar_ToSMT_Term.mkForall _147_2199))
in ((_147_2200), (Some ("Fuel irrelevance"))))
in FStar_ToSMT_Term.Assume (_147_2201))
in (

let _50_3123 = (

let _50_3110 = (encode_binders None formals env0)
in (match (_50_3110) with
| (vars, v_guards, env, binder_decls, _50_3109) -> begin
(

let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let gapp = (FStar_ToSMT_Term.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _147_2202 = (FStar_ToSMT_Term.mkFreeV ((gtok), (FStar_ToSMT_Term.Term_sort)))
in (mk_ApplyE _147_2202 ((fuel)::vars)))
in (let _147_2206 = (let _147_2205 = (let _147_2204 = (let _147_2203 = (FStar_ToSMT_Term.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_147_2203)))
in (FStar_ToSMT_Term.mkForall _147_2204))
in ((_147_2205), (Some ("Fuel token correspondence"))))
in FStar_ToSMT_Term.Assume (_147_2206)))
in (

let _50_3120 = (

let _50_3117 = (encode_typ_pred None tres env gapp)
in (match (_50_3117) with
| (g_typing, d3) -> begin
(let _147_2214 = (let _147_2213 = (let _147_2212 = (let _147_2211 = (let _147_2210 = (let _147_2209 = (let _147_2208 = (let _147_2207 = (FStar_ToSMT_Term.mk_and_l v_guards)
in ((_147_2207), (g_typing)))
in (FStar_ToSMT_Term.mkImp _147_2208))
in ((((gapp)::[])::[]), ((fuel)::vars), (_147_2209)))
in (FStar_ToSMT_Term.mkForall _147_2210))
in ((_147_2211), (None)))
in FStar_ToSMT_Term.Assume (_147_2212))
in (_147_2213)::[])
in ((d3), (_147_2214)))
end))
in (match (_50_3120) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (_50_3123) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end))
end))
end))
in (

let _50_3139 = (let _147_2217 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _50_3127 _50_3131 -> (match (((_50_3127), (_50_3131))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _50_3135 = (encode_one_binding env0 gtok ty bs)
in (match (_50_3135) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _147_2217))
in (match (_50_3139) with
| (decls, eqns, env0) -> begin
(

let _50_3148 = (let _147_2219 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _147_2219 (FStar_List.partition (fun _50_29 -> (match (_50_29) with
| FStar_ToSMT_Term.DeclFun (_50_3142) -> begin
true
end
| _50_3145 -> begin
false
end)))))
in (match (_50_3148) with
| (prefix_decls, rest) -> begin
(

let eqns = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns))), (env0)))
end))
end))))
end)))))
end
end)))
end))
end
end)
with
| Let_rec_unencodeable -> begin
(

let msg = (let _147_2222 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname))))
in (FStar_All.pipe_right _147_2222 (FStar_String.concat " and ")))
in (

let decl = FStar_ToSMT_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end
| (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end)))))
and declare_top_level_let : env_t  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((Prims.string * FStar_ToSMT_Term.term Prims.option) * FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(

let _50_3175 = (encode_free_var env x t t_norm [])
in (match (_50_3175) with
| (decls, env) -> begin
(

let _50_3180 = (lookup_lid env x)
in (match (_50_3180) with
| (n, x', _50_3179) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, _50_3184) -> begin
((((n), (x))), ([]), (env))
end))
and encode_smt_lemma : env_t  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_ToSMT_Term.decl Prims.list = (fun env lid t -> (

let _50_3192 = (encode_function_type_as_formula None None t env)
in (match (_50_3192) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_ToSMT_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))))))::[]))
end)))
and encode_free_var : env_t  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env lid tt t_norm quals -> if ((let _147_2235 = (FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _147_2235)) || (FStar_Absyn_Util.is_lemma t_norm)) then begin
(

let _50_3201 = (new_term_constant_and_tok_from_lid env lid)
in (match (_50_3201) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _50_3204) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _50_30 -> (match (_50_30) with
| (FStar_Util.Inl (_50_3209), _50_3212) -> begin
FStar_ToSMT_Term.Type_sort
end
| _50_3215 -> begin
FStar_ToSMT_Term.Term_sort
end))))
end
| _50_3217 -> begin
[]
end)
in (

let d = FStar_ToSMT_Term.DeclFun (((vname), (arg_sorts), (FStar_ToSMT_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_ToSMT_Term.DeclFun (((vtok), ([]), (FStar_ToSMT_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end else begin
if (prims.is lid) then begin
(

let vname = (varops.new_fvar lid)
in (

let definition = (prims.mk lid vname)
in (

let env = (push_free_var env lid vname None)
in ((definition), (env)))))
end else begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let _50_3234 = (match ((FStar_Absyn_Util.function_formals t_norm)) with
| Some (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _147_2237 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_147_2237)))
end else begin
((args), (((None), ((FStar_Absyn_Util.comp_result comp)))))
end
end
| None -> begin
(([]), (((None), (t_norm))))
end)
in (match (_50_3234) with
| (formals, (pre_opt, res_t)) -> begin
(

let _50_3238 = (new_term_constant_and_tok_from_lid env lid)
in (match (_50_3238) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV ((vname), (FStar_ToSMT_Term.Term_sort)))
end
| _50_3241 -> begin
(FStar_ToSMT_Term.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _50_31 -> (match (_50_31) with
| FStar_Absyn_Syntax.Discriminator (d) -> begin
(

let _50_3257 = (FStar_Util.prefix vars)
in (match (_50_3257) with
| (_50_3252, (xxsym, _50_3255)) -> begin
(

let xx = (FStar_ToSMT_Term.mkFreeV ((xxsym), (FStar_ToSMT_Term.Term_sort)))
in (let _147_2254 = (let _147_2253 = (let _147_2252 = (let _147_2251 = (let _147_2250 = (let _147_2249 = (let _147_2248 = (let _147_2247 = (FStar_ToSMT_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_2247))
in ((vapp), (_147_2248)))
in (FStar_ToSMT_Term.mkEq _147_2249))
in ((((vapp)::[])::[]), (vars), (_147_2250)))
in (FStar_ToSMT_Term.mkForall _147_2251))
in ((_147_2252), (Some ("Discriminator equation"))))
in FStar_ToSMT_Term.Assume (_147_2253))
in (_147_2254)::[]))
end))
end
| FStar_Absyn_Syntax.Projector (d, FStar_Util.Inr (f)) -> begin
(

let _50_3270 = (FStar_Util.prefix vars)
in (match (_50_3270) with
| (_50_3265, (xxsym, _50_3268)) -> begin
(

let xx = (FStar_ToSMT_Term.mkFreeV ((xxsym), (FStar_ToSMT_Term.Term_sort)))
in (

let prim_app = (let _147_2256 = (let _147_2255 = (mk_term_projector_name d f)
in ((_147_2255), ((xx)::[])))
in (FStar_ToSMT_Term.mkApp _147_2256))
in (let _147_2261 = (let _147_2260 = (let _147_2259 = (let _147_2258 = (let _147_2257 = (FStar_ToSMT_Term.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_147_2257)))
in (FStar_ToSMT_Term.mkForall _147_2258))
in ((_147_2259), (Some ("Projector equation"))))
in FStar_ToSMT_Term.Assume (_147_2260))
in (_147_2261)::[])))
end))
end
| _50_3274 -> begin
[]
end)))))
in (

let _50_3281 = (encode_binders None formals env)
in (match (_50_3281) with
| (vars, guards, env', decls1, _50_3280) -> begin
(

let _50_3290 = (match (pre_opt) with
| None -> begin
(let _147_2262 = (FStar_ToSMT_Term.mk_and_l guards)
in ((_147_2262), (decls1)))
end
| Some (p) -> begin
(

let _50_3287 = (encode_formula p env')
in (match (_50_3287) with
| (g, ds) -> begin
(let _147_2263 = (FStar_ToSMT_Term.mk_and_l ((g)::guards))
in ((_147_2263), ((FStar_List.append decls1 ds))))
end))
end)
in (match (_50_3290) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_ApplyE vtok_tm vars)
in (

let vapp = (let _147_2265 = (let _147_2264 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in ((vname), (_147_2264)))
in (FStar_ToSMT_Term.mkApp _147_2265))
in (

let _50_3321 = (

let vname_decl = (let _147_2268 = (let _147_2267 = (FStar_All.pipe_right formals (FStar_List.map (fun _50_32 -> (match (_50_32) with
| (FStar_Util.Inl (_50_3295), _50_3298) -> begin
FStar_ToSMT_Term.Type_sort
end
| _50_3301 -> begin
FStar_ToSMT_Term.Term_sort
end))))
in ((vname), (_147_2267), (FStar_ToSMT_Term.Term_sort), (None)))
in FStar_ToSMT_Term.DeclFun (_147_2268))
in (

let _50_3308 = (

let env = (

let _50_3303 = env
in {bindings = _50_3303.bindings; depth = _50_3303.depth; tcenv = _50_3303.tcenv; warn = _50_3303.warn; cache = _50_3303.cache; nolabels = _50_3303.nolabels; use_zfuel_name = _50_3303.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_typ_pred None tt env vtok_tm)
end else begin
(encode_typ_pred None t_norm env vtok_tm)
end)
in (match (_50_3308) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_ToSMT_Term.Assume (((tok_typing), (Some ("function token typing"))))
in (

let _50_3318 = (match (formals) with
| [] -> begin
(let _147_2272 = (let _147_2271 = (let _147_2270 = (FStar_ToSMT_Term.mkFreeV ((vname), (FStar_ToSMT_Term.Term_sort)))
in (FStar_All.pipe_left (fun _147_2269 -> Some (_147_2269)) _147_2270))
in (push_free_var env lid vname _147_2271))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_147_2272)))
end
| _50_3312 -> begin
(

let vtok_decl = FStar_ToSMT_Term.DeclFun (((vtok), ([]), (FStar_ToSMT_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _147_2273 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token ((vtok), (FStar_ToSMT_Term.Term_sort)) _147_2273))
in (

let name_tok_corr = (let _147_2277 = (let _147_2276 = (let _147_2275 = (let _147_2274 = (FStar_ToSMT_Term.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::[]), (vars), (_147_2274)))
in (FStar_ToSMT_Term.mkForall _147_2275))
in ((_147_2276), (None)))
in FStar_ToSMT_Term.Assume (_147_2277))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (_50_3318) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (_50_3321) with
| (decls2, env) -> begin
(

let _50_3329 = (

let res_t = (FStar_Absyn_Util.compress_typ res_t)
in (

let _50_3325 = (encode_typ_term res_t env')
in (match (_50_3325) with
| (encoded_res_t, decls) -> begin
(let _147_2278 = (FStar_ToSMT_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_147_2278), (decls)))
end)))
in (match (_50_3329) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _147_2282 = (let _147_2281 = (let _147_2280 = (let _147_2279 = (FStar_ToSMT_Term.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_147_2279)))
in (FStar_ToSMT_Term.mkForall _147_2280))
in ((_147_2281), (Some ("free var typing"))))
in FStar_ToSMT_Term.Assume (_147_2282))
in (

let g = (let _147_2286 = (let _147_2285 = (let _147_2284 = (let _147_2283 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_147_2283)
in (FStar_List.append decls3 _147_2284))
in (FStar_List.append decls2 _147_2285))
in (FStar_List.append decls1 _147_2286))
in ((g), (env))))
end))
end))))
end))
end))))
end))
end)))
end
end)
and encode_signature : env_t  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _50_3336 se -> (match (_50_3336) with
| (g, env) -> begin
(

let _50_3340 = (encode_sigelt env se)
in (match (_50_3340) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_Tc_Env.binding Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env bindings -> (

let encode_binding = (fun b _50_3347 -> (match (_50_3347) with
| (decls, env) -> begin
(match (b) with
| FStar_Tc_Env.Binding_var (x, t0) -> begin
(

let _50_3355 = (new_term_constant env x)
in (match (_50_3355) with
| (xxsym, xx, env') -> begin
(

let t1 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (

let _50_3357 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _147_2301 = (FStar_Absyn_Print.strBvd x)
in (let _147_2300 = (FStar_Absyn_Print.typ_to_string t0)
in (let _147_2299 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _147_2301 _147_2300 _147_2299))))
end else begin
()
end
in (

let _50_3361 = (encode_typ_pred None t1 env xx)
in (match (_50_3361) with
| (t, decls') -> begin
(

let caption = if (FStar_Options.log_queries ()) then begin
(let _147_2305 = (let _147_2304 = (FStar_Absyn_Print.strBvd x)
in (let _147_2303 = (FStar_Absyn_Print.typ_to_string t0)
in (let _147_2302 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _147_2304 _147_2303 _147_2302))))
in Some (_147_2305))
end else begin
None
end
in (

let g = (FStar_List.append ((FStar_ToSMT_Term.DeclFun (((xxsym), ([]), (FStar_ToSMT_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((FStar_ToSMT_Term.Assume (((t), (None))))::[])))
in (((FStar_List.append decls g)), (env'))))
end))))
end))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(

let _50_3371 = (new_typ_constant env a)
in (match (_50_3371) with
| (aasym, aa, env') -> begin
(

let _50_3374 = (encode_knd k env aa)
in (match (_50_3374) with
| (k, decls') -> begin
(

let g = (let _147_2310 = (let _147_2309 = (let _147_2308 = (let _147_2307 = (let _147_2306 = (FStar_Absyn_Print.strBvd a)
in Some (_147_2306))
in ((aasym), ([]), (FStar_ToSMT_Term.Type_sort), (_147_2307)))
in FStar_ToSMT_Term.DeclFun (_147_2308))
in (_147_2309)::[])
in (FStar_List.append _147_2310 (FStar_List.append decls' ((FStar_ToSMT_Term.Assume (((k), (None))))::[]))))
in (((FStar_List.append decls g)), (env')))
end))
end))
end
| FStar_Tc_Env.Binding_lid (x, t) -> begin
(

let t_norm = (whnf env t)
in (

let _50_3383 = (encode_free_var env x t t_norm [])
in (match (_50_3383) with
| (g, env') -> begin
(((FStar_List.append decls g)), (env'))
end)))
end
| FStar_Tc_Env.Binding_sig (se) -> begin
(

let _50_3388 = (encode_sigelt env se)
in (match (_50_3388) with
| (g, env') -> begin
(((FStar_List.append decls g)), (env'))
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings (([]), (env)))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _50_3395 -> (match (_50_3395) with
| (l, _50_3392, _50_3394) -> begin
FStar_ToSMT_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_ToSMT_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _50_3402 -> (match (_50_3402) with
| (l, _50_3399, _50_3401) -> begin
(let _147_2318 = (FStar_All.pipe_left (fun _147_2314 -> FStar_ToSMT_Term.Echo (_147_2314)) (Prims.fst l))
in (let _147_2317 = (let _147_2316 = (let _147_2315 = (FStar_ToSMT_Term.mkFreeV l)
in FStar_ToSMT_Term.Eval (_147_2315))
in (_147_2316)::[])
in (_147_2318)::_147_2317))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_Tc_Env.env  ->  Prims.unit = (fun tcenv -> (let _147_2323 = (let _147_2322 = (let _147_2321 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = _147_2321; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_147_2322)::[])
in (FStar_ST.op_Colon_Equals last_env _147_2323)))


let get_env : FStar_Tc_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_50_3408 -> begin
(

let _50_3411 = e
in {bindings = _50_3411.bindings; depth = _50_3411.depth; tcenv = tcenv; warn = _50_3411.warn; cache = _50_3411.cache; nolabels = _50_3411.nolabels; use_zfuel_name = _50_3411.use_zfuel_name; encode_non_total_function_typ = _50_3411.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_50_3417)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _50_3419 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (hd)::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let _50_3425 = hd
in {bindings = _50_3425.bindings; depth = _50_3425.depth; tcenv = _50_3425.tcenv; warn = _50_3425.warn; cache = refs; nolabels = _50_3425.nolabels; use_zfuel_name = _50_3425.use_zfuel_name; encode_non_total_function_typ = _50_3425.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _50_3428 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_50_3432)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _50_3434 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _50_3435 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _50_3436 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_50_3439)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _50_3444 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_Tc_Env.env  ->  Prims.unit = (fun tcenv -> (

let _50_3446 = (init_env tcenv)
in (

let _50_3448 = (FStar_ToSMT_Z3.init ())
in (FStar_ToSMT_Z3.giveZ3 ((FStar_ToSMT_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _50_3451 = (push_env ())
in (

let _50_3453 = (varops.push ())
in (FStar_ToSMT_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _50_3456 = (let _147_2344 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _147_2344))
in (

let _50_3458 = (varops.pop ())
in (FStar_ToSMT_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _50_3461 = (mark_env ())
in (

let _50_3463 = (varops.mark ())
in (FStar_ToSMT_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _50_3466 = (reset_mark_env ())
in (

let _50_3468 = (varops.reset_mark ())
in (FStar_ToSMT_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _50_3471 = (commit_mark_env ())
in (

let _50_3473 = (varops.commit_mark ())
in (FStar_ToSMT_Z3.commit_mark msg))))


let encode_sig : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _147_2358 = (let _147_2357 = (let _147_2356 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (Prims.strcat "encoding sigelt " _147_2356))
in FStar_ToSMT_Term.Caption (_147_2357))
in (_147_2358)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _50_3482 = (encode_sigelt env se)
in (match (_50_3482) with
| (decls, env) -> begin
(

let _50_3483 = (set_env env)
in (let _147_2359 = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 _147_2359)))
end)))))


let encode_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Ident.str)
in (

let _50_3488 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _147_2364 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Absyn_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "Encoding externals for %s ... %s exports\n" name _147_2364))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _50_3495 = (encode_signature (

let _50_3491 = env
in {bindings = _50_3491.bindings; depth = _50_3491.depth; tcenv = _50_3491.tcenv; warn = false; cache = _50_3491.cache; nolabels = _50_3491.nolabels; use_zfuel_name = _50_3491.use_zfuel_name; encode_non_total_function_typ = _50_3491.encode_non_total_function_typ}) modul.FStar_Absyn_Syntax.exports)
in (match (_50_3495) with
| (decls, env) -> begin
(

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::decls) ((FStar_ToSMT_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (

let _50_3501 = (set_env (

let _50_3499 = env
in {bindings = _50_3499.bindings; depth = _50_3499.depth; tcenv = _50_3499.tcenv; warn = true; cache = _50_3499.cache; nolabels = _50_3499.nolabels; use_zfuel_name = _50_3499.use_zfuel_name; encode_non_total_function_typ = _50_3499.encode_non_total_function_typ}))
in (

let _50_3503 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))


let solve : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun tcenv q -> (

let _50_3508 = (let _147_2373 = (let _147_2372 = (let _147_2371 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _147_2371))
in (FStar_Util.format1 "Starting query at %s" _147_2372))
in (push _147_2373))
in (

let pop = (fun _50_3511 -> (match (()) with
| () -> begin
(let _147_2378 = (let _147_2377 = (let _147_2376 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _147_2376))
in (FStar_Util.format1 "Ending query at %s" _147_2377))
in (pop _147_2378))
end))
in (

let _50_3570 = (

let env = (get_env tcenv)
in (

let bindings = (FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _50_3544 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_Tc_Env.Binding_var (x, t))::rest -> begin
(

let _50_3526 = (aux rest)
in (match (_50_3526) with
| (out, rest) -> begin
(

let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
in (let _147_2384 = (let _147_2383 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_147_2383)::out)
in ((_147_2384), (rest))))
end))
end
| (FStar_Tc_Env.Binding_typ (a, k))::rest -> begin
(

let _50_3536 = (aux rest)
in (match (_50_3536) with
| (out, rest) -> begin
(let _147_2386 = (let _147_2385 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_147_2385)::out)
in ((_147_2386), (rest)))
end))
end
| _50_3538 -> begin
(([]), (bindings))
end))
in (

let _50_3541 = (aux bindings)
in (match (_50_3541) with
| (closing, bindings) -> begin
(let _147_2387 = (FStar_Absyn_Util.close_forall (FStar_List.rev closing) q)
in ((_147_2387), (bindings)))
end)))
in (match (_50_3544) with
| (q, bindings) -> begin
(

let _50_3553 = (let _147_2389 = (FStar_List.filter (fun _50_33 -> (match (_50_33) with
| FStar_Tc_Env.Binding_sig (_50_3547) -> begin
false
end
| _50_3550 -> begin
true
end)) bindings)
in (encode_env_bindings env _147_2389))
in (match (_50_3553) with
| (env_decls, env) -> begin
(

let _50_3554 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _147_2390 = (FStar_Absyn_Print.formula_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _147_2390))
end else begin
()
end
in (

let _50_3559 = (encode_formula_with_labels q env)
in (match (_50_3559) with
| (phi, labels, qdecls) -> begin
(

let _50_3562 = (encode_labels labels)
in (match (_50_3562) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (let _147_2392 = (let _147_2391 = (FStar_ToSMT_Term.mkNot phi)
in ((_147_2391), (Some ("query"))))
in FStar_ToSMT_Term.Assume (_147_2392))
in (

let suffix = (FStar_List.append label_suffix ((FStar_ToSMT_Term.Echo ("Done!"))::[]))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end)))
end))
end))))
in (match (_50_3570) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_ToSMT_Term.Assume ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (FStar_ToSMT_Term.False, _50_3577); FStar_ToSMT_Term.hash = _50_3574; FStar_ToSMT_Term.freevars = _50_3572}, _50_3582) -> begin
(

let _50_3585 = (pop ())
in ())
end
| _50_3588 when tcenv.FStar_Tc_Env.admit -> begin
(

let _50_3589 = (pop ())
in ())
end
| FStar_ToSMT_Term.Assume (q, _50_3593) -> begin
(

let fresh = ((FStar_String.length q.FStar_ToSMT_Term.hash) >= (Prims.parse_int "2048"))
in (

let _50_3597 = (FStar_ToSMT_Z3.giveZ3 prefix)
in (

let with_fuel = (fun p _50_3603 -> (match (_50_3603) with
| (n, i) -> begin
(let _147_2415 = (let _147_2414 = (let _147_2399 = (let _147_2398 = (FStar_Util.string_of_int n)
in (let _147_2397 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _147_2398 _147_2397)))
in FStar_ToSMT_Term.Caption (_147_2399))
in (let _147_2413 = (let _147_2412 = (let _147_2404 = (let _147_2403 = (let _147_2402 = (let _147_2401 = (FStar_ToSMT_Term.mkApp (("MaxFuel"), ([])))
in (let _147_2400 = (FStar_ToSMT_Term.n_fuel n)
in ((_147_2401), (_147_2400))))
in (FStar_ToSMT_Term.mkEq _147_2402))
in ((_147_2403), (None)))
in FStar_ToSMT_Term.Assume (_147_2404))
in (let _147_2411 = (let _147_2410 = (let _147_2409 = (let _147_2408 = (let _147_2407 = (let _147_2406 = (FStar_ToSMT_Term.mkApp (("MaxIFuel"), ([])))
in (let _147_2405 = (FStar_ToSMT_Term.n_fuel i)
in ((_147_2406), (_147_2405))))
in (FStar_ToSMT_Term.mkEq _147_2407))
in ((_147_2408), (None)))
in FStar_ToSMT_Term.Assume (_147_2409))
in (_147_2410)::(p)::(FStar_ToSMT_Term.CheckSat)::[])
in (_147_2412)::_147_2411))
in (_147_2414)::_147_2413))
in (FStar_List.append _147_2415 suffix))
end))
in (

let check = (fun p -> (

let initial_config = (let _147_2419 = (FStar_Options.initial_fuel ())
in (let _147_2418 = (FStar_Options.initial_ifuel ())
in ((_147_2419), (_147_2418))))
in (

let alt_configs = (let _147_2438 = (let _147_2437 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _147_2422 = (let _147_2421 = (FStar_Options.initial_fuel ())
in (let _147_2420 = (FStar_Options.max_ifuel ())
in ((_147_2421), (_147_2420))))
in (_147_2422)::[])
end else begin
[]
end
in (let _147_2436 = (let _147_2435 = if (((FStar_Options.max_fuel ()) / (Prims.parse_int "2")) > (FStar_Options.initial_fuel ())) then begin
(let _147_2425 = (let _147_2424 = ((FStar_Options.max_fuel ()) / (Prims.parse_int "2"))
in (let _147_2423 = (FStar_Options.max_ifuel ())
in ((_147_2424), (_147_2423))))
in (_147_2425)::[])
end else begin
[]
end
in (let _147_2434 = (let _147_2433 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _147_2428 = (let _147_2427 = (FStar_Options.max_fuel ())
in (let _147_2426 = (FStar_Options.max_ifuel ())
in ((_147_2427), (_147_2426))))
in (_147_2428)::[])
end else begin
[]
end
in (let _147_2432 = (let _147_2431 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _147_2430 = (let _147_2429 = (FStar_Options.min_fuel ())
in ((_147_2429), ((Prims.parse_int "1"))))
in (_147_2430)::[])
end else begin
[]
end
in (_147_2431)::[])
in (_147_2433)::_147_2432))
in (_147_2435)::_147_2434))
in (_147_2437)::_147_2436))
in (FStar_List.flatten _147_2438))
in (

let report = (fun errs -> (

let errs = (match (errs) with
| [] -> begin
((("Unknown assertion failed"), (FStar_Absyn_Syntax.dummyRange)))::[]
end
| _50_3612 -> begin
errs
end)
in (

let _50_3614 = if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(let _147_2446 = (let _147_2441 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _147_2441))
in (let _147_2445 = (let _147_2442 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _147_2442 FStar_Util.string_of_int))
in (let _147_2444 = (let _147_2443 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _147_2443 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _147_2446 _147_2445 _147_2444))))
end else begin
()
end
in (FStar_Tc_Errors.add_errors tcenv errs))))
in (

let rec try_alt_configs = (fun p errs _50_34 -> (match (_50_34) with
| [] -> begin
(report errs)
end
| (mi)::[] -> begin
(match (errs) with
| [] -> begin
(let _147_2457 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _147_2457 (cb mi p [])))
end
| _50_3626 -> begin
(report errs)
end)
end
| (mi)::tl -> begin
(let _147_2459 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _147_2459 (fun _50_3632 -> (match (_50_3632) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl ((ok), (errs')))
end
| _50_3635 -> begin
(cb mi p tl ((ok), (errs)))
end)
end))))
end))
and cb = (fun _50_3638 p alt _50_3643 -> (match (((_50_3638), (_50_3643))) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(let _147_2467 = (let _147_2464 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _147_2464))
in (let _147_2466 = (FStar_Util.string_of_int prev_fuel)
in (let _147_2465 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _147_2467 _147_2466 _147_2465))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _147_2468 = (with_fuel p initial_config)
in (FStar_ToSMT_Z3.ask fresh labels _147_2468 (cb initial_config p alt_configs))))))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let _50_3648 = (let _147_2474 = (FStar_Options.split_cases ())
in (FStar_ToSMT_SplitQueryCases.can_handle_query _147_2474 q))
in (match (_50_3648) with
| (b, cb) -> begin
if b then begin
(FStar_ToSMT_SplitQueryCases.handle_query cb check)
end else begin
(check q)
end
end))
end else begin
(check q)
end)
in (

let _50_3649 = if (FStar_Options.admit_smt_queries ()) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end)
end)))))


let is_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in (

let _50_3654 = (push "query")
in (

let _50_3661 = (encode_formula_with_labels q env)
in (match (_50_3661) with
| (f, _50_3658, _50_3660) -> begin
(

let _50_3662 = (pop "query")
in (match (f.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _50_3666) -> begin
true
end
| _50_3670 -> begin
false
end))
end)))))


let solver : FStar_Tc_Env.solver_t = {FStar_Tc_Env.init = init; FStar_Tc_Env.push = push; FStar_Tc_Env.pop = pop; FStar_Tc_Env.mark = mark; FStar_Tc_Env.reset_mark = reset_mark; FStar_Tc_Env.commit_mark = commit_mark; FStar_Tc_Env.encode_modul = encode_modul; FStar_Tc_Env.encode_sig = encode_sig; FStar_Tc_Env.solve = solve; FStar_Tc_Env.is_trivial = is_trivial; FStar_Tc_Env.finish = FStar_ToSMT_Z3.finish; FStar_Tc_Env.refresh = FStar_ToSMT_Z3.refresh}


let dummy : FStar_Tc_Env.solver_t = {FStar_Tc_Env.init = (fun _50_3671 -> ()); FStar_Tc_Env.push = (fun _50_3673 -> ()); FStar_Tc_Env.pop = (fun _50_3675 -> ()); FStar_Tc_Env.mark = (fun _50_3677 -> ()); FStar_Tc_Env.reset_mark = (fun _50_3679 -> ()); FStar_Tc_Env.commit_mark = (fun _50_3681 -> ()); FStar_Tc_Env.encode_modul = (fun _50_3683 _50_3685 -> ()); FStar_Tc_Env.encode_sig = (fun _50_3687 _50_3689 -> ()); FStar_Tc_Env.solve = (fun _50_3691 _50_3693 -> ()); FStar_Tc_Env.is_trivial = (fun _50_3695 _50_3697 -> false); FStar_Tc_Env.finish = (fun _50_3699 -> ()); FStar_Tc_Env.refresh = (fun _50_3700 -> ())}





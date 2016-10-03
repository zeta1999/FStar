
open Prims

let exhaustiveness_check : Prims.string = "Patterns are incomplete"


let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (let _151_10 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _151_9 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" _151_10 _151_9))))


let ill_kinded_type : Prims.string = "Ill-kinded type"


let totality_check : Prims.string = "This term may not terminate"


let diag : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> if (FStar_Options.debug_any ()) then begin
(let _151_16 = (let _151_15 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Diagnostic): %s\n" _151_15 msg))
in (FStar_Util.print_string _151_16))
end else begin
()
end)


let warn : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _151_22 = (let _151_21 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Warning): %s\n" _151_21 msg))
in (FStar_Util.print_string _151_22)))


let num_errs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let verification_errs : (FStar_Range.range * Prims.string) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


type error_message_prefix =
{set_prefix : Prims.string  ->  Prims.unit; append_prefix : Prims.string  ->  Prims.string; clear_prefix : Prims.unit  ->  Prims.unit}


let is_Mkerror_message_prefix : error_message_prefix  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkerror_message_prefix"))))


let message_prefix : error_message_prefix = (

let pfx = (FStar_Util.mk_ref None)
in (

let set_prefix = (fun s -> (FStar_ST.op_Colon_Equals pfx (Some (s))))
in (

let clear_prefix = (fun _54_18 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals pfx None)
end))
in (

let append_prefix = (fun s -> (match ((FStar_ST.read pfx)) with
| None -> begin
s
end
| Some (p) -> begin
(Prims.strcat p (Prims.strcat ": " s))
end))
in {set_prefix = set_prefix; append_prefix = append_prefix; clear_prefix = clear_prefix}))))


let add_errors : FStar_TypeChecker_Env.env  ->  (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun env errs -> (

let errs = (FStar_All.pipe_right errs (FStar_List.map (fun _54_28 -> (match (_54_28) with
| (msg, r) -> begin
(

let r = if (r = FStar_Range.dummyRange) then begin
(FStar_TypeChecker_Env.get_range env)
end else begin
r
end
in (let _151_62 = (message_prefix.append_prefix msg)
in ((r), (_151_62))))
end))))
in (

let n_errs = (FStar_List.length errs)
in (FStar_Util.atomically (fun _54_32 -> (match (()) with
| () -> begin
(

let _54_33 = (let _151_65 = (let _151_64 = (FStar_ST.read verification_errs)
in (FStar_List.append errs _151_64))
in (FStar_ST.op_Colon_Equals verification_errs _151_65))
in (let _151_66 = ((FStar_ST.read num_errs) + n_errs)
in (FStar_ST.op_Colon_Equals num_errs _151_66)))
end))))))


let report_all : Prims.unit  ->  Prims.int = (fun _54_35 -> (match (()) with
| () -> begin
(

let all_errs = (FStar_Util.atomically (fun _54_36 -> (match (()) with
| () -> begin
(

let x = (FStar_ST.read verification_errs)
in (

let _54_38 = (FStar_ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (

let all_errs = (FStar_List.sortWith (fun _54_44 _54_48 -> (match (((_54_44), (_54_48))) with
| ((r1, _54_43), (r2, _54_47)) -> begin
(FStar_Range.compare r1 r2)
end)) all_errs)
in (

let _54_53 = (FStar_All.pipe_right all_errs (FStar_List.iter (fun _54_52 -> (match (_54_52) with
| (r, msg) -> begin
(let _151_73 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 "%s: %s\n" _151_73 msg))
end))))
in (FStar_List.length all_errs))))
end))


let handle_err : Prims.bool  ->  Prims.exn  ->  Prims.unit = (fun warning e -> (match (e) with
| FStar_Syntax_Syntax.Error (msg, r) -> begin
(

let msg = (message_prefix.append_prefix msg)
in (let _151_79 = (let _151_78 = (FStar_Range.string_of_range r)
in (_151_78)::(if warning then begin
"Warning"
end else begin
"Error"
end)::(msg)::[])
in (FStar_Util.fprint FStar_Util.stderr "%s : %s\n%s\n" _151_79)))
end
| FStar_Util.NYI (msg) -> begin
(

let msg = (message_prefix.append_prefix msg)
in (FStar_Util.fprint FStar_Util.stderr "Feature not yet implemented: %s" ((msg)::[])))
end
| FStar_Syntax_Syntax.Err (msg) -> begin
(

let msg = (message_prefix.append_prefix msg)
in (FStar_Util.fprint FStar_Util.stderr "Error: %s" ((msg)::[])))
end
| _54_69 -> begin
(Prims.raise e)
end))


let handleable : Prims.exn  ->  Prims.bool = (fun _54_1 -> (match (_54_1) with
| (FStar_Syntax_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Syntax_Syntax.Err (_)) -> begin
true
end
| _54_81 -> begin
false
end))


let report : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (

let _54_84 = (FStar_Util.incr num_errs)
in (

let msg = (message_prefix.append_prefix msg)
in (let _151_87 = (let _151_86 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _151_86 msg))
in (FStar_Util.print_string _151_87)))))


let get_err_count : Prims.unit  ->  Prims.int = (fun _54_87 -> (match (()) with
| () -> begin
(FStar_ST.read num_errs)
end))


let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env m k -> (let _151_96 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => WP a => Effect);\ngot %s" m.FStar_Ident.str _151_96)))


let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env msg t e -> (let _151_106 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _151_105 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)" _151_106 _151_105 msg))))


let unexpected_implicit_argument : Prims.string = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"


let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _151_117 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _151_116 = (FStar_Syntax_Print.term_to_string e)
in (let _151_115 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" _151_117 _151_116 _151_115)))))


let expected_function_with_parameter_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (let _151_129 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _151_128 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _151_129 _151_128))))


let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _151_140 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _151_139 = (FStar_Syntax_Print.term_to_string e)
in (let _151_138 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" _151_140 _151_139 _151_138)))))


let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(let _151_150 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _151_149 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "Expected type \"%s\";\ngot type \"%s\"" _151_150 _151_149)))
end
| Some (e) -> begin
(let _151_153 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _151_152 = (FStar_Syntax_Print.term_to_string e)
in (let _151_151 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _151_153 _151_152 _151_151))))
end))


let occurs_check : Prims.string = "Possibly infinite typ (occurs check failed)"


let unification_well_formedness : Prims.string = "Term or type of an unexpected sort"


let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 k2 -> (let _151_161 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _151_160 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _151_161 _151_160))))


let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env d t t' -> (let _151_172 = (FStar_Syntax_Print.term_to_string d)
in (let _151_171 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _151_170 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _151_172 _151_171 _151_170)))))


let constructor_fails_the_positivity_check = (fun env d l -> (let _151_177 = (FStar_Syntax_Print.term_to_string d)
in (let _151_176 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _151_177 _151_176))))


let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  Prims.string = (fun l -> (let _151_180 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _151_180)))


let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun env t x -> (let _151_188 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _151_187 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _151_188 _151_187))))


let expected_typ_of_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 t k2 -> (let _151_199 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _151_198 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _151_197 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\"" _151_199 _151_198 _151_197)))))


let expected_tcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _151_207 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _151_206 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _151_207 _151_206))))


let expected_dcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _151_215 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _151_214 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _151_215 _151_214))))


let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _151_220 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function;\ngot an expression of type \"%s\"" _151_220)))


let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f t targ -> (let _151_231 = (FStar_Syntax_Print.term_to_string f)
in (let _151_230 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _151_229 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _151_231 _151_230 _151_229)))))


let nonlinear_pattern_variable : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (

let m = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))


let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun v1 v2 -> (

let vars = (fun v -> (let _151_240 = (FStar_All.pipe_right v (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right _151_240 (FStar_String.concat ", "))))
in (let _151_242 = (vars v1)
in (let _151_241 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _151_242 _151_241)))))


let name_and_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _54_152) -> begin
(("Tot"), (t))
end
| FStar_Syntax_Syntax.GTotal (t, _54_157) -> begin
(("GTot"), (t))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _151_244 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in ((_151_244), (ct.FStar_Syntax_Syntax.result_typ)))
end))


let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (

let _54_168 = (name_and_result c)
in (match (_54_168) with
| (f1, r1) -> begin
(

let _54_171 = (name_and_result c')
in (match (_54_171) with
| (f2, r2) -> begin
(let _151_250 = (FStar_TypeChecker_Normalize.term_to_string env r1)
in (let _151_249 = (FStar_TypeChecker_Normalize.term_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _151_250 f1 _151_249 f2)))
end))
end)))


let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f -> (let _151_255 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _151_255)))


let expected_pure_expression = (fun e c -> (let _151_260 = (FStar_Syntax_Print.term_to_string e)
in (let _151_259 = (let _151_258 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _151_258))
in (FStar_Util.format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" _151_260 _151_259))))


let expected_ghost_expression = (fun e c -> (let _151_265 = (FStar_Syntax_Print.term_to_string e)
in (let _151_264 = (let _151_263 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _151_263))
in (FStar_Util.format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" _151_265 _151_264))))


let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.string = (fun c1 c2 -> (let _151_271 = (FStar_Syntax_Print.lid_to_string c1)
in (let _151_270 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s\n" _151_271 _151_270))))


let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  Prims.string = (fun l lbls -> (let _151_277 = (FStar_Syntax_Print.lbname_to_string l)
in (let _151_276 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _151_277 _151_276))))


let failed_to_prove_specification : Prims.string Prims.list  ->  Prims.string = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _54_185 -> begin
(let _151_280 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" _151_280))
end))


let top_level_effect : Prims.string = "Top-level let-bindings must be total; this term may have effects"


let cardinality_constraint_violated = (fun l a -> (let _151_284 = (FStar_Syntax_Print.lid_to_string l)
in (let _151_283 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" _151_284 _151_283))))





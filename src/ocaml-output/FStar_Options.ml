open Prims
let (debug_embedding : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (eager_embedding : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
type debug_level_t =
  | Low 
  | Medium 
  | High 
  | Extreme 
  | Other of Prims.string 
let (uu___is_Low : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | Low  -> true | uu____26 -> false 
let (uu___is_Medium : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Medium  -> true | uu____37 -> false
  
let (uu___is_High : debug_level_t -> Prims.bool) =
  fun projectee  -> match projectee with | High  -> true | uu____48 -> false 
let (uu___is_Extreme : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Extreme  -> true | uu____59 -> false
  
let (uu___is_Other : debug_level_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Other _0 -> true | uu____72 -> false
  
let (__proj__Other__item___0 : debug_level_t -> Prims.string) =
  fun projectee  -> match projectee with | Other _0 -> _0 
type option_val =
  | Bool of Prims.bool 
  | String of Prims.string 
  | Path of Prims.string 
  | Int of Prims.int 
  | List of option_val Prims.list 
  | Unset 
let (uu___is_Bool : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____126 -> false
  
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____149 -> false
  
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Path _0 -> true | uu____172 -> false
  
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee  -> match projectee with | Path _0 -> _0 
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____195 -> false
  
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | List _0 -> true | uu____219 -> false
  
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee  -> match projectee with | List _0 -> _0 
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unset  -> true | uu____243 -> false
  
let (mk_bool : Prims.bool -> option_val) = fun _251  -> Bool _251 
let (mk_string : Prims.string -> option_val) = fun _258  -> String _258 
let (mk_path : Prims.string -> option_val) = fun _265  -> Path _265 
let (mk_int : Prims.int -> option_val) = fun _272  -> Int _272 
let (mk_list : option_val Prims.list -> option_val) = fun _280  -> List _280 
type error_flag =
  | CFatal 
  | CAlwaysError 
  | CError 
  | CWarning 
  | CSilent 
let (uu___is_CFatal : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CFatal  -> true | uu____290 -> false
  
let (uu___is_CAlwaysError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CAlwaysError  -> true | uu____301 -> false
  
let (uu___is_CError : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CError  -> true | uu____312 -> false
  
let (uu___is_CWarning : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CWarning  -> true | uu____323 -> false
  
let (uu___is_CSilent : error_flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CSilent  -> true | uu____334 -> false
  
let (__unit_tests__ : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (__unit_tests : unit -> Prims.bool) =
  fun uu____348  -> FStar_ST.op_Bang __unit_tests__ 
let (__set_unit_tests : unit -> unit) =
  fun uu____375  -> FStar_ST.op_Colon_Equals __unit_tests__ true 
let (__clear_unit_tests : unit -> unit) =
  fun uu____403  -> FStar_ST.op_Colon_Equals __unit_tests__ false 
let (as_bool : option_val -> Prims.bool) =
  fun uu___0_432  ->
    match uu___0_432 with
    | Bool b -> b
    | uu____436 -> failwith "Impos: expected Bool"
  
let (as_int : option_val -> Prims.int) =
  fun uu___1_445  ->
    match uu___1_445 with
    | Int b -> b
    | uu____449 -> failwith "Impos: expected Int"
  
let (as_string : option_val -> Prims.string) =
  fun uu___2_458  ->
    match uu___2_458 with
    | String b -> b
    | Path b -> FStar_Common.try_convert_file_name_to_mixed b
    | uu____464 -> failwith "Impos: expected String"
  
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___3_474  ->
    match uu___3_474 with
    | List ts -> ts
    | uu____480 -> failwith "Impos: expected List"
  
let as_list :
  'Auu____491 .
    (option_val -> 'Auu____491) -> option_val -> 'Auu____491 Prims.list
  =
  fun as_t  ->
    fun x  ->
      let uu____509 = as_list' x  in
      FStar_All.pipe_right uu____509 (FStar_List.map as_t)
  
let as_option :
  'Auu____523 .
    (option_val -> 'Auu____523) ->
      option_val -> 'Auu____523 FStar_Pervasives_Native.option
  =
  fun as_t  ->
    fun uu___4_538  ->
      match uu___4_538 with
      | Unset  -> FStar_Pervasives_Native.None
      | v1 ->
          let uu____542 = as_t v1  in FStar_Pervasives_Native.Some uu____542
  
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___5_551  ->
    match uu___5_551 with
    | List ls ->
        let uu____558 =
          FStar_List.map
            (fun l  ->
               let uu____570 = as_string l  in FStar_Util.split uu____570 ",")
            ls
           in
        FStar_All.pipe_left FStar_List.flatten uu____558
    | uu____582 -> failwith "Impos: expected String (comma list)"
  
type optionstate = option_val FStar_Util.smap
let copy_optionstate :
  'Auu____594 . 'Auu____594 FStar_Util.smap -> 'Auu____594 FStar_Util.smap =
  fun m  -> FStar_Util.smap_copy m 
let (fstar_options : optionstate Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (internal_peek : unit -> optionstate) =
  fun uu____624  ->
    let uu____625 =
      let uu____628 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____628  in
    FStar_List.hd uu____625
  
let (peek : unit -> optionstate) = fun uu____667  -> internal_peek () 
let (pop : unit -> unit) =
  fun uu____673  ->
    let uu____674 = FStar_ST.op_Bang fstar_options  in
    match uu____674 with
    | [] -> failwith "TOO MANY POPS!"
    | uu____709::[] -> failwith "TOO MANY POPS!"
    | uu____717::tl1 -> FStar_ST.op_Colon_Equals fstar_options tl1
  
let (push : unit -> unit) =
  fun uu____759  ->
    let uu____760 =
      let uu____765 =
        let uu____768 =
          let uu____771 = FStar_ST.op_Bang fstar_options  in
          FStar_List.hd uu____771  in
        FStar_List.map copy_optionstate uu____768  in
      let uu____805 = FStar_ST.op_Bang fstar_options  in uu____765 ::
        uu____805
       in
    FStar_ST.op_Colon_Equals fstar_options uu____760
  
let (internal_pop : unit -> Prims.bool) =
  fun uu____872  ->
    let curstack =
      let uu____876 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____876  in
    match curstack with
    | [] -> failwith "impossible: empty current option stack"
    | uu____913::[] -> false
    | uu____915::tl1 ->
        ((let uu____920 =
            let uu____925 =
              let uu____930 = FStar_ST.op_Bang fstar_options  in
              FStar_List.tl uu____930  in
            tl1 :: uu____925  in
          FStar_ST.op_Colon_Equals fstar_options uu____920);
         true)
  
let (internal_push : unit -> unit) =
  fun uu____999  ->
    let curstack =
      let uu____1003 = FStar_ST.op_Bang fstar_options  in
      FStar_List.hd uu____1003  in
    let stack' =
      let uu____1040 =
        let uu____1041 = FStar_List.hd curstack  in
        copy_optionstate uu____1041  in
      uu____1040 :: curstack  in
    let uu____1044 =
      let uu____1049 =
        let uu____1054 = FStar_ST.op_Bang fstar_options  in
        FStar_List.tl uu____1054  in
      stack' :: uu____1049  in
    FStar_ST.op_Colon_Equals fstar_options uu____1044
  
let (set : optionstate -> unit) =
  fun o  ->
    let uu____1123 = FStar_ST.op_Bang fstar_options  in
    match uu____1123 with
    | [] -> failwith "set on empty option stack"
    | []::uu____1158 -> failwith "set on empty current option stack"
    | (uu____1166::tl1)::os ->
        FStar_ST.op_Colon_Equals fstar_options ((o :: tl1) :: os)
  
let (snapshot : unit -> (Prims.int * unit)) =
  fun uu____1216  -> FStar_Common.snapshot push fstar_options () 
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop fstar_options depth 
let (set_option : Prims.string -> option_val -> unit) =
  fun k  ->
    fun v1  ->
      let uu____1246 = peek ()  in FStar_Util.smap_add uu____1246 k v1
  
let (set_option' : (Prims.string * option_val) -> unit) =
  fun uu____1259  -> match uu____1259 with | (k,v1) -> set_option k v1 
let (light_off_files : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (add_light_off_file : Prims.string -> unit) =
  fun filename  ->
    let uu____1287 =
      let uu____1291 = FStar_ST.op_Bang light_off_files  in filename ::
        uu____1291
       in
    FStar_ST.op_Colon_Equals light_off_files uu____1287
  
let (defaults : (Prims.string * option_val) Prims.list) =
  [("__temp_no_proj", (List []));
  ("__temp_fast_implicits", (Bool false));
  ("abort_on", (Int (Prims.parse_int "0")));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
  ("already_cached", Unset);
  ("cache_checked_modules", (Bool false));
  ("cache_dir", Unset);
  ("cache_off", (Bool false));
  ("cmi", (Bool false));
  ("codegen", Unset);
  ("codegen-lib", (List []));
  ("debug", (List []));
  ("debug_level", (List []));
  ("defensive", (String "no"));
  ("dep", Unset);
  ("detail_errors", (Bool false));
  ("detail_hint_replay", (Bool false));
  ("doc", (Bool false));
  ("dump_module", (List []));
  ("eager_inference", (Bool false));
  ("eager_subtyping", (Bool false));
  ("expose_interfaces", (Bool false));
  ("extract", Unset);
  ("extract_all", (Bool false));
  ("extract_module", (List []));
  ("extract_namespace", (List []));
  ("fs_typ_app", (Bool false));
  ("full_context_dependency", (Bool true));
  ("hide_uvar_nums", (Bool false));
  ("hint_info", (Bool false));
  ("hint_file", Unset);
  ("in", (Bool false));
  ("ide", (Bool false));
  ("include", (List []));
  ("print", (Bool false));
  ("print_in_place", (Bool false));
  ("profile", (Bool false));
  ("initial_fuel", (Int (Prims.parse_int "2")));
  ("initial_ifuel", (Int (Prims.parse_int "1")));
  ("keep_query_captions", (Bool true));
  ("lax", (Bool false));
  ("load", (List []));
  ("log_queries", (Bool false));
  ("log_types", (Bool false));
  ("max_fuel", (Int (Prims.parse_int "8")));
  ("max_ifuel", (Int (Prims.parse_int "2")));
  ("min_fuel", (Int (Prims.parse_int "1")));
  ("MLish", (Bool false));
  ("n_cores", (Int (Prims.parse_int "1")));
  ("no_default_includes", (Bool false));
  ("no_extract", (List []));
  ("no_location_info", (Bool false));
  ("no_smt", (Bool false));
  ("no_plugins", (Bool false));
  ("no_tactics", (Bool false));
  ("normalize_pure_terms_for_extraction", (Bool false));
  ("odir", Unset);
  ("prims", Unset);
  ("pretype", (Bool true));
  ("prims_ref", Unset);
  ("print_bound_var_types", (Bool false));
  ("print_effect_args", (Bool false));
  ("print_full_names", (Bool false));
  ("print_implicits", (Bool false));
  ("print_universes", (Bool false));
  ("print_z3_statistics", (Bool false));
  ("prn", (Bool false));
  ("query_stats", (Bool false));
  ("record_hints", (Bool false));
  ("reuse_hint_for", Unset);
  ("silent", (Bool false));
  ("smt", Unset);
  ("smtencoding.elim_box", (Bool false));
  ("smtencoding.nl_arith_repr", (String "boxwrap"));
  ("smtencoding.l_arith_repr", (String "boxwrap"));
  ("smtencoding.valid_intro", (Bool true));
  ("smtencoding.valid_elim", (Bool false));
  ("tactics_failhard", (Bool false));
  ("tactics_info", (Bool false));
  ("tactic_raw_binders", (Bool false));
  ("tactic_trace", (Bool false));
  ("tactic_trace_d", (Int (Prims.parse_int "0")));
  ("tcnorm", (Bool true));
  ("timing", (Bool false));
  ("trace_error", (Bool false));
  ("ugly", (Bool false));
  ("unthrottle_inductives", (Bool false));
  ("unsafe_tactic_exec", (Bool false));
  ("use_native_tactics", Unset);
  ("use_eq_at_higher_order", (Bool false));
  ("use_hints", (Bool false));
  ("use_hint_hashes", (Bool false));
  ("using_facts_from", Unset);
  ("vcgen.optimize_bind_as_seq", Unset);
  ("verify_module", (List []));
  ("warn_default_effects", (Bool false));
  ("z3refresh", (Bool false));
  ("z3rlimit", (Int (Prims.parse_int "5")));
  ("z3rlimit_factor", (Int (Prims.parse_int "1")));
  ("z3seed", (Int (Prims.parse_int "0")));
  ("z3cliopt", (List []));
  ("use_two_phase_tc", (Bool true));
  ("__no_positivity", (Bool false));
  ("__ml_no_eta_expand_coertions", (Bool false));
  ("__tactics_nbe", (Bool false));
  ("warn_error", (List []));
  ("use_extracted_interfaces", (Bool false));
  ("use_nbe", (Bool false))] 
let (parse_warn_error_set_get :
  (((Prims.string -> error_flag Prims.list) -> unit) *
    (unit -> Prims.string -> error_flag Prims.list)))
  =
  let r = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let set1 f =
    let uu____2268 = FStar_ST.op_Bang r  in
    match uu____2268 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some f)
    | uu____2359 -> failwith "Multiple initialization of FStar.Options"  in
  let get1 uu____2380 =
    let uu____2381 = FStar_ST.op_Bang r  in
    match uu____2381 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        failwith "FStar.Options is improperly initialized"
     in
  (set1, get1) 
let (initialize_parse_warn_error :
  (Prims.string -> error_flag Prims.list) -> unit) =
  fun f  -> FStar_Pervasives_Native.fst parse_warn_error_set_get f 
let (parse_warn_error : Prims.string -> error_flag Prims.list) =
  fun s  ->
    let uu____2520 = FStar_Pervasives_Native.snd parse_warn_error_set_get ()
       in
    uu____2520 s
  
let (init : unit -> unit) =
  fun uu____2551  ->
    let o = peek ()  in
    FStar_Util.smap_clear o;
    FStar_All.pipe_right defaults (FStar_List.iter set_option')
  
let (clear : unit -> unit) =
  fun uu____2571  ->
    let o = FStar_Util.smap_create (Prims.parse_int "50")  in
    FStar_ST.op_Colon_Equals fstar_options [[o]];
    FStar_ST.op_Colon_Equals light_off_files [];
    init ()
  
let (_run : unit) = clear () 
let (get_option : Prims.string -> option_val) =
  fun s  ->
    let uu____2644 =
      let uu____2647 = peek ()  in FStar_Util.smap_try_find uu____2647 s  in
    match uu____2644 with
    | FStar_Pervasives_Native.None  ->
        let uu____2650 =
          let uu____2652 = FStar_String.op_Hat s " not found"  in
          FStar_String.op_Hat "Impossible: option " uu____2652  in
        failwith uu____2650
    | FStar_Pervasives_Native.Some s1 -> s1
  
let lookup_opt :
  'Auu____2664 . Prims.string -> (option_val -> 'Auu____2664) -> 'Auu____2664
  = fun s  -> fun c  -> let uu____2682 = get_option s  in c uu____2682 
let (get_abort_on : unit -> Prims.int) =
  fun uu____2689  -> lookup_opt "abort_on" as_int 
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu____2698  -> lookup_opt "admit_smt_queries" as_bool 
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu____2709  -> lookup_opt "admit_except" (as_option as_string) 
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2725  ->
    lookup_opt "already_cached" (as_option (as_list as_string))
  
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu____2742  -> lookup_opt "cache_checked_modules" as_bool 
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2753  -> lookup_opt "cache_dir" (as_option as_string) 
let (get_cache_off : unit -> Prims.bool) =
  fun uu____2765  -> lookup_opt "cache_off" as_bool 
let (get_cmi : unit -> Prims.bool) =
  fun uu____2774  -> lookup_opt "cmi" as_bool 
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2785  -> lookup_opt "codegen" (as_option as_string) 
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu____2799  -> lookup_opt "codegen-lib" (as_list as_string) 
let (get_debug : unit -> Prims.string Prims.list) =
  fun uu____2813  -> lookup_opt "debug" (as_list as_string) 
let (get_debug_level : unit -> Prims.string Prims.list) =
  fun uu____2827  -> lookup_opt "debug_level" as_comma_string_list 
let (get_defensive : unit -> Prims.string) =
  fun uu____2838  -> lookup_opt "defensive" as_string 
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2849  -> lookup_opt "dep" (as_option as_string) 
let (get_detail_errors : unit -> Prims.bool) =
  fun uu____2861  -> lookup_opt "detail_errors" as_bool 
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu____2870  -> lookup_opt "detail_hint_replay" as_bool 
let (get_doc : unit -> Prims.bool) =
  fun uu____2879  -> lookup_opt "doc" as_bool 
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu____2890  -> lookup_opt "dump_module" (as_list as_string) 
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu____2902  -> lookup_opt "eager_subtyping" as_bool 
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu____2911  -> lookup_opt "expose_interfaces" as_bool 
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____2924  -> lookup_opt "extract" (as_option (as_list as_string)) 
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu____2943  -> lookup_opt "extract_module" (as_list as_string) 
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu____2957  -> lookup_opt "extract_namespace" (as_list as_string) 
let (get_fs_typ_app : unit -> Prims.bool) =
  fun uu____2969  -> lookup_opt "fs_typ_app" as_bool 
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu____2978  -> lookup_opt "hide_uvar_nums" as_bool 
let (get_hint_info : unit -> Prims.bool) =
  fun uu____2987  -> lookup_opt "hint_info" as_bool 
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____2998  -> lookup_opt "hint_file" (as_option as_string) 
let (get_in : unit -> Prims.bool) =
  fun uu____3010  -> lookup_opt "in" as_bool 
let (get_ide : unit -> Prims.bool) =
  fun uu____3019  -> lookup_opt "ide" as_bool 
let (get_include : unit -> Prims.string Prims.list) =
  fun uu____3030  -> lookup_opt "include" (as_list as_string) 
let (get_print : unit -> Prims.bool) =
  fun uu____3042  -> lookup_opt "print" as_bool 
let (get_print_in_place : unit -> Prims.bool) =
  fun uu____3051  -> lookup_opt "print_in_place" as_bool 
let (get_profile : unit -> Prims.bool) =
  fun uu____3060  -> lookup_opt "profile" as_bool 
let (get_initial_fuel : unit -> Prims.int) =
  fun uu____3069  -> lookup_opt "initial_fuel" as_int 
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu____3078  -> lookup_opt "initial_ifuel" as_int 
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu____3087  -> lookup_opt "keep_query_captions" as_bool 
let (get_lax : unit -> Prims.bool) =
  fun uu____3096  -> lookup_opt "lax" as_bool 
let (get_load : unit -> Prims.string Prims.list) =
  fun uu____3107  -> lookup_opt "load" (as_list as_string) 
let (get_log_queries : unit -> Prims.bool) =
  fun uu____3119  -> lookup_opt "log_queries" as_bool 
let (get_log_types : unit -> Prims.bool) =
  fun uu____3128  -> lookup_opt "log_types" as_bool 
let (get_max_fuel : unit -> Prims.int) =
  fun uu____3137  -> lookup_opt "max_fuel" as_int 
let (get_max_ifuel : unit -> Prims.int) =
  fun uu____3146  -> lookup_opt "max_ifuel" as_int 
let (get_min_fuel : unit -> Prims.int) =
  fun uu____3155  -> lookup_opt "min_fuel" as_int 
let (get_MLish : unit -> Prims.bool) =
  fun uu____3164  -> lookup_opt "MLish" as_bool 
let (get_n_cores : unit -> Prims.int) =
  fun uu____3173  -> lookup_opt "n_cores" as_int 
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu____3182  -> lookup_opt "no_default_includes" as_bool 
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu____3193  -> lookup_opt "no_extract" (as_list as_string) 
let (get_no_location_info : unit -> Prims.bool) =
  fun uu____3205  -> lookup_opt "no_location_info" as_bool 
let (get_no_plugins : unit -> Prims.bool) =
  fun uu____3214  -> lookup_opt "no_plugins" as_bool 
let (get_no_smt : unit -> Prims.bool) =
  fun uu____3223  -> lookup_opt "no_smt" as_bool 
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____3232  -> lookup_opt "normalize_pure_terms_for_extraction" as_bool 
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3243  -> lookup_opt "odir" (as_option as_string) 
let (get_ugly : unit -> Prims.bool) =
  fun uu____3255  -> lookup_opt "ugly" as_bool 
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3266  -> lookup_opt "prims" (as_option as_string) 
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu____3278  -> lookup_opt "print_bound_var_types" as_bool 
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu____3287  -> lookup_opt "print_effect_args" as_bool 
let (get_print_full_names : unit -> Prims.bool) =
  fun uu____3296  -> lookup_opt "print_full_names" as_bool 
let (get_print_implicits : unit -> Prims.bool) =
  fun uu____3305  -> lookup_opt "print_implicits" as_bool 
let (get_print_universes : unit -> Prims.bool) =
  fun uu____3314  -> lookup_opt "print_universes" as_bool 
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu____3323  -> lookup_opt "print_z3_statistics" as_bool 
let (get_prn : unit -> Prims.bool) =
  fun uu____3332  -> lookup_opt "prn" as_bool 
let (get_query_stats : unit -> Prims.bool) =
  fun uu____3341  -> lookup_opt "query_stats" as_bool 
let (get_record_hints : unit -> Prims.bool) =
  fun uu____3350  -> lookup_opt "record_hints" as_bool 
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3361  -> lookup_opt "reuse_hint_for" (as_option as_string) 
let (get_silent : unit -> Prims.bool) =
  fun uu____3373  -> lookup_opt "silent" as_bool 
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3384  -> lookup_opt "smt" (as_option as_string) 
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____3396  -> lookup_opt "smtencoding.elim_box" as_bool 
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu____3405  -> lookup_opt "smtencoding.nl_arith_repr" as_string 
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu____3414  -> lookup_opt "smtencoding.l_arith_repr" as_string 
let (get_smtencoding_valid_intro : unit -> Prims.bool) =
  fun uu____3423  -> lookup_opt "smtencoding.valid_intro" as_bool 
let (get_smtencoding_valid_elim : unit -> Prims.bool) =
  fun uu____3432  -> lookup_opt "smtencoding.valid_elim" as_bool 
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu____3441  -> lookup_opt "tactic_raw_binders" as_bool 
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu____3450  -> lookup_opt "tactics_failhard" as_bool 
let (get_tactics_info : unit -> Prims.bool) =
  fun uu____3459  -> lookup_opt "tactics_info" as_bool 
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu____3468  -> lookup_opt "tactic_trace" as_bool 
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu____3477  -> lookup_opt "tactic_trace_d" as_int 
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu____3486  -> lookup_opt "__tactics_nbe" as_bool 
let (get_tcnorm : unit -> Prims.bool) =
  fun uu____3495  -> lookup_opt "tcnorm" as_bool 
let (get_timing : unit -> Prims.bool) =
  fun uu____3504  -> lookup_opt "timing" as_bool 
let (get_trace_error : unit -> Prims.bool) =
  fun uu____3513  -> lookup_opt "trace_error" as_bool 
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu____3522  -> lookup_opt "unthrottle_inductives" as_bool 
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____3531  -> lookup_opt "unsafe_tactic_exec" as_bool 
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____3540  -> lookup_opt "use_eq_at_higher_order" as_bool 
let (get_use_hints : unit -> Prims.bool) =
  fun uu____3549  -> lookup_opt "use_hints" as_bool 
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu____3558  -> lookup_opt "use_hint_hashes" as_bool 
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3569  -> lookup_opt "use_native_tactics" (as_option as_string) 
let (get_use_tactics : unit -> Prims.bool) =
  fun uu____3581  ->
    let uu____3582 = lookup_opt "no_tactics" as_bool  in
    Prims.op_Negation uu____3582
  
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu____3596  ->
    lookup_opt "using_facts_from" (as_option (as_list as_string))
  
let (get_vcgen_optimize_bind_as_seq :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____3615  ->
    lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
  
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu____3629  -> lookup_opt "verify_module" (as_list as_string) 
let (get___temp_no_proj : unit -> Prims.string Prims.list) =
  fun uu____3643  -> lookup_opt "__temp_no_proj" (as_list as_string) 
let (get_version : unit -> Prims.bool) =
  fun uu____3655  -> lookup_opt "version" as_bool 
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu____3664  -> lookup_opt "warn_default_effects" as_bool 
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu____3675  -> lookup_opt "z3cliopt" (as_list as_string) 
let (get_z3refresh : unit -> Prims.bool) =
  fun uu____3687  -> lookup_opt "z3refresh" as_bool 
let (get_z3rlimit : unit -> Prims.int) =
  fun uu____3696  -> lookup_opt "z3rlimit" as_int 
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu____3705  -> lookup_opt "z3rlimit_factor" as_int 
let (get_z3seed : unit -> Prims.int) =
  fun uu____3714  -> lookup_opt "z3seed" as_int 
let (get_use_two_phase_tc : unit -> Prims.bool) =
  fun uu____3723  -> lookup_opt "use_two_phase_tc" as_bool 
let (get_no_positivity : unit -> Prims.bool) =
  fun uu____3732  -> lookup_opt "__no_positivity" as_bool 
let (get_ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____3741  -> lookup_opt "__ml_no_eta_expand_coertions" as_bool 
let (get_warn_error : unit -> Prims.string Prims.list) =
  fun uu____3752  -> lookup_opt "warn_error" (as_list as_string) 
let (get_use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____3764  -> lookup_opt "use_extracted_interfaces" as_bool 
let (get_use_nbe : unit -> Prims.bool) =
  fun uu____3773  -> lookup_opt "use_nbe" as_bool 
let (dlevel : Prims.string -> debug_level_t) =
  fun uu___6_3782  ->
    match uu___6_3782 with
    | "Low" -> Low
    | "Medium" -> Medium
    | "High" -> High
    | "Extreme" -> Extreme
    | s -> Other s
  
let (one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool) =
  fun l1  ->
    fun l2  ->
      match l1 with
      | Other uu____3803 -> l1 = l2
      | Low  -> l1 = l2
      | Medium  -> (l2 = Low) || (l2 = Medium)
      | High  -> ((l2 = Low) || (l2 = Medium)) || (l2 = High)
      | Extreme  ->
          (((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme)
  
let (debug_level_geq : debug_level_t -> Prims.bool) =
  fun l2  ->
    let uu____3812 = get_debug_level ()  in
    FStar_All.pipe_right uu____3812
      (FStar_Util.for_some (fun l1  -> one_debug_level_geq (dlevel l1) l2))
  
let (universe_include_path_base_dirs : Prims.string Prims.list) =
  ["/ulib"; "/lib/fstar"] 
let (_version : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_platform : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_compiler : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (_date : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "<not set>" 
let (_commit : Prims.string FStar_ST.ref) = FStar_Util.mk_ref "" 
let (display_version : unit -> unit) =
  fun uu____3868  ->
    let uu____3869 =
      let uu____3871 = FStar_ST.op_Bang _version  in
      let uu____3894 = FStar_ST.op_Bang _platform  in
      let uu____3917 = FStar_ST.op_Bang _compiler  in
      let uu____3940 = FStar_ST.op_Bang _date  in
      let uu____3963 = FStar_ST.op_Bang _commit  in
      FStar_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu____3871
        uu____3894 uu____3917 uu____3940 uu____3963
       in
    FStar_Util.print_string uu____3869
  
let display_usage_aux :
  'Auu____3994 'Auu____3995 .
    ('Auu____3994 * Prims.string * 'Auu____3995 FStar_Getopt.opt_variant *
      Prims.string) Prims.list -> unit
  =
  fun specs  ->
    FStar_Util.print_string "fstar.exe [options] file[s]\n";
    FStar_List.iter
      (fun uu____4050  ->
         match uu____4050 with
         | (uu____4063,flag,p,doc) ->
             (match p with
              | FStar_Getopt.ZeroArgs ig ->
                  if doc = ""
                  then
                    let uu____4082 =
                      let uu____4084 = FStar_Util.colorize_bold flag  in
                      FStar_Util.format1 "  --%s\n" uu____4084  in
                    FStar_Util.print_string uu____4082
                  else
                    (let uu____4089 =
                       let uu____4091 = FStar_Util.colorize_bold flag  in
                       FStar_Util.format2 "  --%s  %s\n" uu____4091 doc  in
                     FStar_Util.print_string uu____4089)
              | FStar_Getopt.OneArg (uu____4094,argname) ->
                  if doc = ""
                  then
                    let uu____4109 =
                      let uu____4111 = FStar_Util.colorize_bold flag  in
                      let uu____4113 = FStar_Util.colorize_bold argname  in
                      FStar_Util.format2 "  --%s %s\n" uu____4111 uu____4113
                       in
                    FStar_Util.print_string uu____4109
                  else
                    (let uu____4118 =
                       let uu____4120 = FStar_Util.colorize_bold flag  in
                       let uu____4122 = FStar_Util.colorize_bold argname  in
                       FStar_Util.format3 "  --%s %s  %s\n" uu____4120
                         uu____4122 doc
                        in
                     FStar_Util.print_string uu____4118))) specs
  
let (mk_spec :
  (FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant
    * Prims.string) -> FStar_Getopt.opt)
  =
  fun o  ->
    let uu____4157 = o  in
    match uu____4157 with
    | (ns,name,arg,desc) ->
        let arg1 =
          match arg with
          | FStar_Getopt.ZeroArgs f ->
              let g uu____4199 =
                let uu____4200 = f ()  in set_option name uu____4200  in
              FStar_Getopt.ZeroArgs g
          | FStar_Getopt.OneArg (f,d) ->
              let g x = let uu____4221 = f x  in set_option name uu____4221
                 in
              FStar_Getopt.OneArg (g, d)
           in
        (ns, name, arg1, desc)
  
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____4248 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____4248  in
      mk_list (value :: prev_values)
  
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name  ->
    fun value  ->
      let prev_values =
        let uu____4277 = lookup_opt name (as_option as_list')  in
        FStar_Util.dflt [] uu____4277  in
      mk_list (FStar_List.append prev_values [value])
  
let accumulate_string :
  'Auu____4299 .
    Prims.string -> ('Auu____4299 -> Prims.string) -> 'Auu____4299 -> unit
  =
  fun name  ->
    fun post_processor  ->
      fun value  ->
        let uu____4324 =
          let uu____4325 =
            let uu____4326 = post_processor value  in mk_string uu____4326
             in
          accumulated_option name uu____4325  in
        set_option name uu____4324
  
let (add_extract_module : Prims.string -> unit) =
  fun s  -> accumulate_string "extract_module" FStar_String.lowercase s 
let (add_extract_namespace : Prims.string -> unit) =
  fun s  -> accumulate_string "extract_namespace" FStar_String.lowercase s 
let (add_verify_module : Prims.string -> unit) =
  fun s  -> accumulate_string "verify_module" FStar_String.lowercase s 
type opt_type =
  | Const of option_val 
  | IntStr of Prims.string 
  | BoolStr 
  | PathStr of Prims.string 
  | SimpleStr of Prims.string 
  | EnumStr of Prims.string Prims.list 
  | OpenEnumStr of (Prims.string Prims.list * Prims.string) 
  | PostProcessed of ((option_val -> option_val) * opt_type) 
  | Accumulated of opt_type 
  | ReverseAccumulated of opt_type 
  | WithSideEffect of ((unit -> unit) * opt_type) 
let (uu___is_Const : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Const _0 -> true | uu____4448 -> false
  
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee  -> match projectee with | Const _0 -> _0 
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | IntStr _0 -> true | uu____4468 -> false
  
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | IntStr _0 -> _0 
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | BoolStr  -> true | uu____4489 -> false
  
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PathStr _0 -> true | uu____4502 -> false
  
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | PathStr _0 -> _0 
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | SimpleStr _0 -> true | uu____4525 -> false
  
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee  -> match projectee with | SimpleStr _0 -> _0 
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | EnumStr _0 -> true | uu____4550 -> false
  
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee  -> match projectee with | EnumStr _0 -> _0 
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | OpenEnumStr _0 -> true | uu____4586 -> false
  
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee  -> match projectee with | OpenEnumStr _0 -> _0 
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | PostProcessed _0 -> true | uu____4636 -> false
  
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee  -> match projectee with | PostProcessed _0 -> _0 
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accumulated _0 -> true | uu____4676 -> false
  
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | Accumulated _0 -> _0 
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ReverseAccumulated _0 -> true
    | uu____4695 -> false
  
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee  -> match projectee with | ReverseAccumulated _0 -> _0 
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | WithSideEffect _0 -> true | uu____4721 -> false
  
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee  -> match projectee with | WithSideEffect _0 -> _0 
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidArgument uu____4764 -> true
    | uu____4767 -> false
  
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidArgument uu____4777 -> uu____4777
  
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name  ->
    fun typ  ->
      fun str_val  ->
        try
          (fun uu___294_4801  ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu____4803 ->
                      let uu____4805 = FStar_Util.safe_int_of_string str_val
                         in
                      (match uu____4805 with
                       | FStar_Pervasives_Native.Some v1 -> mk_int v1
                       | FStar_Pervasives_Native.None  ->
                           FStar_Exn.raise (InvalidArgument opt_name))
                  | BoolStr  ->
                      let uu____4813 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else FStar_Exn.raise (InvalidArgument opt_name)
                         in
                      mk_bool uu____4813
                  | PathStr uu____4830 -> mk_path str_val
                  | SimpleStr uu____4832 -> mk_string str_val
                  | EnumStr strs ->
                      if FStar_List.mem str_val strs
                      then mk_string str_val
                      else FStar_Exn.raise (InvalidArgument opt_name)
                  | OpenEnumStr uu____4842 -> mk_string str_val
                  | PostProcessed (pp,elem_spec) ->
                      let uu____4859 =
                        parse_opt_val opt_name elem_spec str_val  in
                      pp uu____4859
                  | Accumulated elem_spec ->
                      let v1 = parse_opt_val opt_name elem_spec str_val  in
                      accumulated_option opt_name v1
                  | ReverseAccumulated elem_spec ->
                      let v1 = parse_opt_val opt_name elem_spec str_val  in
                      reverse_accumulated_option opt_name v1
                  | WithSideEffect (side_effect,elem_spec) ->
                      (side_effect ();
                       parse_opt_val opt_name elem_spec str_val))) ()
        with
        | InvalidArgument opt_name1 ->
            let uu____4879 =
              FStar_Util.format1 "Invalid argument to --%s" opt_name1  in
            failwith uu____4879
  
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ  ->
    let desc_of_enum cases =
      let uu____4909 =
        let uu____4911 =
          FStar_String.op_Hat (FStar_String.concat "|" cases) "]"  in
        FStar_String.op_Hat "[" uu____4911  in
      FStar_Pervasives_Native.Some uu____4909  in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr  -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs,desc) -> desc_of_enum (FStar_List.append strs [desc])
    | PostProcessed (uu____4953,elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu____4963,elem_spec) -> desc_of_opt_type elem_spec
  
let rec (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant) =
  fun opt_name  ->
    fun typ  ->
      let parser = parse_opt_val opt_name typ  in
      let uu____4994 = desc_of_opt_type typ  in
      match uu____4994 with
      | FStar_Pervasives_Native.None  ->
          FStar_Getopt.ZeroArgs ((fun uu____5002  -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          FStar_Getopt.OneArg (parser, desc)
  
let (pp_validate_dir : option_val -> option_val) =
  fun p  -> let pp = as_string p  in FStar_Util.mkdir false pp; p 
let (pp_lowercase : option_val -> option_val) =
  fun s  ->
    let uu____5028 =
      let uu____5030 = as_string s  in FStar_String.lowercase uu____5030  in
    mk_string uu____5028
  
let (abort_counter : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let rec (specs_with_types :
  unit ->
    (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string)
      Prims.list)
  =
  fun uu____5065  ->
    let uu____5079 =
      let uu____5093 =
        let uu____5107 =
          let uu____5121 =
            let uu____5135 =
              let uu____5147 =
                let uu____5148 = mk_bool true  in Const uu____5148  in
              (FStar_Getopt.noshort, "cache_checked_modules", uu____5147,
                "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying")
               in
            let uu____5155 =
              let uu____5169 =
                let uu____5183 =
                  let uu____5195 =
                    let uu____5196 = mk_bool true  in Const uu____5196  in
                  (FStar_Getopt.noshort, "cache_off", uu____5195,
                    "Do not read or write any .checked files")
                   in
                let uu____5203 =
                  let uu____5217 =
                    let uu____5229 =
                      let uu____5230 = mk_bool true  in Const uu____5230  in
                    (FStar_Getopt.noshort, "cmi", uu____5229,
                      "Inline across module interfaces during extraction (aka. cross-module inlining)")
                     in
                  let uu____5237 =
                    let uu____5251 =
                      let uu____5265 =
                        let uu____5279 =
                          let uu____5293 =
                            let uu____5307 =
                              let uu____5321 =
                                let uu____5335 =
                                  let uu____5347 =
                                    let uu____5348 = mk_bool true  in
                                    Const uu____5348  in
                                  (FStar_Getopt.noshort, "detail_errors",
                                    uu____5347,
                                    "Emit a detailed error report by asking the SMT solver many queries; will take longer;\n         implies n_cores=1")
                                   in
                                let uu____5355 =
                                  let uu____5369 =
                                    let uu____5381 =
                                      let uu____5382 = mk_bool true  in
                                      Const uu____5382  in
                                    (FStar_Getopt.noshort,
                                      "detail_hint_replay", uu____5381,
                                      "Emit a detailed report for proof whose unsat core fails to replay;\n         implies n_cores=1")
                                     in
                                  let uu____5389 =
                                    let uu____5403 =
                                      let uu____5415 =
                                        let uu____5416 = mk_bool true  in
                                        Const uu____5416  in
                                      (FStar_Getopt.noshort, "doc",
                                        uu____5415,
                                        "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.")
                                       in
                                    let uu____5423 =
                                      let uu____5437 =
                                        let uu____5451 =
                                          let uu____5463 =
                                            let uu____5464 = mk_bool true  in
                                            Const uu____5464  in
                                          (FStar_Getopt.noshort,
                                            "eager_inference", uu____5463,
                                            "Deprecated: Solve all type-inference constraints eagerly; more efficient but at the cost of generality")
                                           in
                                        let uu____5471 =
                                          let uu____5485 =
                                            let uu____5497 =
                                              let uu____5498 = mk_bool true
                                                 in
                                              Const uu____5498  in
                                            (FStar_Getopt.noshort,
                                              "eager_subtyping", uu____5497,
                                              "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)")
                                             in
                                          let uu____5505 =
                                            let uu____5519 =
                                              let uu____5533 =
                                                let uu____5547 =
                                                  let uu____5561 =
                                                    let uu____5573 =
                                                      let uu____5574 =
                                                        mk_bool true  in
                                                      Const uu____5574  in
                                                    (FStar_Getopt.noshort,
                                                      "expose_interfaces",
                                                      uu____5573,
                                                      "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)")
                                                     in
                                                  let uu____5581 =
                                                    let uu____5595 =
                                                      let uu____5607 =
                                                        let uu____5608 =
                                                          mk_bool true  in
                                                        Const uu____5608  in
                                                      (FStar_Getopt.noshort,
                                                        "hide_uvar_nums",
                                                        uu____5607,
                                                        "Don't print unification variable numbers")
                                                       in
                                                    let uu____5615 =
                                                      let uu____5629 =
                                                        let uu____5643 =
                                                          let uu____5655 =
                                                            let uu____5656 =
                                                              mk_bool true
                                                               in
                                                            Const uu____5656
                                                             in
                                                          (FStar_Getopt.noshort,
                                                            "hint_info",
                                                            uu____5655,
                                                            "Print information regarding hints (deprecated; use --query_stats instead)")
                                                           in
                                                        let uu____5663 =
                                                          let uu____5677 =
                                                            let uu____5689 =
                                                              let uu____5690
                                                                =
                                                                mk_bool true
                                                                 in
                                                              Const
                                                                uu____5690
                                                               in
                                                            (FStar_Getopt.noshort,
                                                              "in",
                                                              uu____5689,
                                                              "Legacy interactive mode; reads input from stdin")
                                                             in
                                                          let uu____5697 =
                                                            let uu____5711 =
                                                              let uu____5723
                                                                =
                                                                let uu____5724
                                                                  =
                                                                  mk_bool
                                                                    true
                                                                   in
                                                                Const
                                                                  uu____5724
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "ide",
                                                                uu____5723,
                                                                "JSON-based interactive mode for IDEs")
                                                               in
                                                            let uu____5731 =
                                                              let uu____5745
                                                                =
                                                                let uu____5759
                                                                  =
                                                                  let uu____5771
                                                                    =
                                                                    let uu____5772
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5772
                                                                     in
                                                                  (FStar_Getopt.noshort,
                                                                    "print",
                                                                    uu____5771,
                                                                    "Parses and prettyprints the files included on the command line")
                                                                   in
                                                                let uu____5779
                                                                  =
                                                                  let uu____5793
                                                                    =
                                                                    let uu____5805
                                                                    =
                                                                    let uu____5806
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5806
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_in_place",
                                                                    uu____5805,
                                                                    "Parses and prettyprints in place the files included on the command line")
                                                                     in
                                                                  let uu____5813
                                                                    =
                                                                    let uu____5827
                                                                    =
                                                                    let uu____5839
                                                                    =
                                                                    let uu____5840
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5840
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "profile",
                                                                    uu____5839,
                                                                    "Prints timing information for various operations in the compiler")
                                                                     in
                                                                    let uu____5847
                                                                    =
                                                                    let uu____5861
                                                                    =
                                                                    let uu____5875
                                                                    =
                                                                    let uu____5889
                                                                    =
                                                                    let uu____5903
                                                                    =
                                                                    let uu____5915
                                                                    =
                                                                    let uu____5916
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5916
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "lax",
                                                                    uu____5915,
                                                                    "Run the lax-type checker only (admit all verification conditions)")
                                                                     in
                                                                    let uu____5923
                                                                    =
                                                                    let uu____5937
                                                                    =
                                                                    let uu____5951
                                                                    =
                                                                    let uu____5963
                                                                    =
                                                                    let uu____5964
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5964
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_types",
                                                                    uu____5963,
                                                                    "Print types computed for data/val/let-bindings")
                                                                     in
                                                                    let uu____5971
                                                                    =
                                                                    let uu____5985
                                                                    =
                                                                    let uu____5997
                                                                    =
                                                                    let uu____5998
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____5998
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "log_queries",
                                                                    uu____5997,
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go")
                                                                     in
                                                                    let uu____6005
                                                                    =
                                                                    let uu____6019
                                                                    =
                                                                    let uu____6033
                                                                    =
                                                                    let uu____6047
                                                                    =
                                                                    let uu____6061
                                                                    =
                                                                    let uu____6073
                                                                    =
                                                                    let uu____6074
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6074
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "MLish",
                                                                    uu____6073,
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)")
                                                                     in
                                                                    let uu____6081
                                                                    =
                                                                    let uu____6095
                                                                    =
                                                                    let uu____6109
                                                                    =
                                                                    let uu____6121
                                                                    =
                                                                    let uu____6122
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6122
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    uu____6121,
                                                                    "Ignore the default module search paths")
                                                                     in
                                                                    let uu____6129
                                                                    =
                                                                    let uu____6143
                                                                    =
                                                                    let uu____6157
                                                                    =
                                                                    let uu____6169
                                                                    =
                                                                    let uu____6170
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6170
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_location_info",
                                                                    uu____6169,
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)")
                                                                     in
                                                                    let uu____6177
                                                                    =
                                                                    let uu____6191
                                                                    =
                                                                    let uu____6203
                                                                    =
                                                                    let uu____6204
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6204
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_smt",
                                                                    uu____6203,
                                                                    "Do not send any queries to the SMT solver, and fail on them instead")
                                                                     in
                                                                    let uu____6211
                                                                    =
                                                                    let uu____6225
                                                                    =
                                                                    let uu____6237
                                                                    =
                                                                    let uu____6238
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6238
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    uu____6237,
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.")
                                                                     in
                                                                    let uu____6245
                                                                    =
                                                                    let uu____6259
                                                                    =
                                                                    let uu____6273
                                                                    =
                                                                    let uu____6287
                                                                    =
                                                                    let uu____6299
                                                                    =
                                                                    let uu____6300
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6300
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    uu____6299,
                                                                    "Print the types of bound variables")
                                                                     in
                                                                    let uu____6307
                                                                    =
                                                                    let uu____6321
                                                                    =
                                                                    let uu____6333
                                                                    =
                                                                    let uu____6334
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6334
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    uu____6333,
                                                                    "Print inferred predicate transformers for all computation types")
                                                                     in
                                                                    let uu____6341
                                                                    =
                                                                    let uu____6355
                                                                    =
                                                                    let uu____6367
                                                                    =
                                                                    let uu____6368
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6368
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_full_names",
                                                                    uu____6367,
                                                                    "Print full names of variables")
                                                                     in
                                                                    let uu____6375
                                                                    =
                                                                    let uu____6389
                                                                    =
                                                                    let uu____6401
                                                                    =
                                                                    let uu____6402
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6402
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_implicits",
                                                                    uu____6401,
                                                                    "Print implicit arguments")
                                                                     in
                                                                    let uu____6409
                                                                    =
                                                                    let uu____6423
                                                                    =
                                                                    let uu____6435
                                                                    =
                                                                    let uu____6436
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6436
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_universes",
                                                                    uu____6435,
                                                                    "Print universes")
                                                                     in
                                                                    let uu____6443
                                                                    =
                                                                    let uu____6457
                                                                    =
                                                                    let uu____6469
                                                                    =
                                                                    let uu____6470
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6470
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    uu____6469,
                                                                    "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)")
                                                                     in
                                                                    let uu____6477
                                                                    =
                                                                    let uu____6491
                                                                    =
                                                                    let uu____6503
                                                                    =
                                                                    let uu____6504
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6504
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prn",
                                                                    uu____6503,
                                                                    "Print full names (deprecated; use --print_full_names instead)")
                                                                     in
                                                                    let uu____6511
                                                                    =
                                                                    let uu____6525
                                                                    =
                                                                    let uu____6537
                                                                    =
                                                                    let uu____6538
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6538
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "query_stats",
                                                                    uu____6537,
                                                                    "Print SMT query statistics")
                                                                     in
                                                                    let uu____6545
                                                                    =
                                                                    let uu____6559
                                                                    =
                                                                    let uu____6571
                                                                    =
                                                                    let uu____6572
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6572
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "record_hints",
                                                                    uu____6571,
                                                                    "Record a database of hints for efficient proof replay")
                                                                     in
                                                                    let uu____6579
                                                                    =
                                                                    let uu____6593
                                                                    =
                                                                    let uu____6607
                                                                    =
                                                                    let uu____6619
                                                                    =
                                                                    let uu____6620
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6620
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "silent",
                                                                    uu____6619,
                                                                    "Disable all non-critical output")
                                                                     in
                                                                    let uu____6627
                                                                    =
                                                                    let uu____6641
                                                                    =
                                                                    let uu____6655
                                                                    =
                                                                    let uu____6669
                                                                    =
                                                                    let uu____6683
                                                                    =
                                                                    let uu____6697
                                                                    =
                                                                    let uu____6711
                                                                    =
                                                                    let uu____6725
                                                                    =
                                                                    let uu____6737
                                                                    =
                                                                    let uu____6738
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6738
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    uu____6737,
                                                                    "Do not use the lexical scope of tactics to improve binder names")
                                                                     in
                                                                    let uu____6745
                                                                    =
                                                                    let uu____6759
                                                                    =
                                                                    let uu____6771
                                                                    =
                                                                    let uu____6772
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6772
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    uu____6771,
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs")
                                                                     in
                                                                    let uu____6779
                                                                    =
                                                                    let uu____6793
                                                                    =
                                                                    let uu____6805
                                                                    =
                                                                    let uu____6806
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6806
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactics_info",
                                                                    uu____6805,
                                                                    "Print some rough information on tactics, such as the time they take to run")
                                                                     in
                                                                    let uu____6813
                                                                    =
                                                                    let uu____6827
                                                                    =
                                                                    let uu____6839
                                                                    =
                                                                    let uu____6840
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6840
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    uu____6839,
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)")
                                                                     in
                                                                    let uu____6847
                                                                    =
                                                                    let uu____6861
                                                                    =
                                                                    let uu____6875
                                                                    =
                                                                    let uu____6887
                                                                    =
                                                                    let uu____6888
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6888
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    uu____6887,
                                                                    "Use NBE to evaluate metaprograms (experimental)")
                                                                     in
                                                                    let uu____6895
                                                                    =
                                                                    let uu____6909
                                                                    =
                                                                    let uu____6923
                                                                    =
                                                                    let uu____6935
                                                                    =
                                                                    let uu____6936
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6936
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "timing",
                                                                    uu____6935,
                                                                    "Print the time it takes to verify each top-level definition")
                                                                     in
                                                                    let uu____6943
                                                                    =
                                                                    let uu____6957
                                                                    =
                                                                    let uu____6969
                                                                    =
                                                                    let uu____6970
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____6970
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "trace_error",
                                                                    uu____6969,
                                                                    "Don't print an error message; show an exception trace instead")
                                                                     in
                                                                    let uu____6977
                                                                    =
                                                                    let uu____6991
                                                                    =
                                                                    let uu____7003
                                                                    =
                                                                    let uu____7004
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7004
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "ugly",
                                                                    uu____7003,
                                                                    "Emit output formatted for debugging")
                                                                     in
                                                                    let uu____7011
                                                                    =
                                                                    let uu____7025
                                                                    =
                                                                    let uu____7037
                                                                    =
                                                                    let uu____7038
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7038
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    uu____7037,
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)")
                                                                     in
                                                                    let uu____7045
                                                                    =
                                                                    let uu____7059
                                                                    =
                                                                    let uu____7071
                                                                    =
                                                                    let uu____7072
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7072
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    uu____7071,
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects.")
                                                                     in
                                                                    let uu____7079
                                                                    =
                                                                    let uu____7093
                                                                    =
                                                                    let uu____7105
                                                                    =
                                                                    let uu____7106
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7106
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    uu____7105,
                                                                    "Use equality constraints when comparing higher-order types (Temporary)")
                                                                     in
                                                                    let uu____7113
                                                                    =
                                                                    let uu____7127
                                                                    =
                                                                    let uu____7139
                                                                    =
                                                                    let uu____7140
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7140
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hints",
                                                                    uu____7139,
                                                                    "Use a previously recorded hints database for proof replay")
                                                                     in
                                                                    let uu____7147
                                                                    =
                                                                    let uu____7161
                                                                    =
                                                                    let uu____7173
                                                                    =
                                                                    let uu____7174
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7174
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    uu____7173,
                                                                    "Admit queries if their hash matches the hash recorded in the hints database")
                                                                     in
                                                                    let uu____7181
                                                                    =
                                                                    let uu____7195
                                                                    =
                                                                    let uu____7209
                                                                    =
                                                                    let uu____7221
                                                                    =
                                                                    let uu____7222
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7222
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_plugins",
                                                                    uu____7221,
                                                                    "Do not run plugins natively and interpret them as usual instead")
                                                                     in
                                                                    let uu____7229
                                                                    =
                                                                    let uu____7243
                                                                    =
                                                                    let uu____7255
                                                                    =
                                                                    let uu____7256
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7256
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_tactics",
                                                                    uu____7255,
                                                                    "Do not run the tactic engine before discharging a VC")
                                                                     in
                                                                    let uu____7263
                                                                    =
                                                                    let uu____7277
                                                                    =
                                                                    let uu____7291
                                                                    =
                                                                    let uu____7305
                                                                    =
                                                                    let uu____7319
                                                                    =
                                                                    let uu____7331
                                                                    =
                                                                    let uu____7332
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7332
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    uu____7331,
                                                                    "Don't use this option yet")
                                                                     in
                                                                    let uu____7339
                                                                    =
                                                                    let uu____7353
                                                                    =
                                                                    let uu____7365
                                                                    =
                                                                    let uu____7366
                                                                    =
                                                                    let uu____7374
                                                                    =
                                                                    let uu____7375
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7375
                                                                     in
                                                                    ((fun
                                                                    uu____7382
                                                                     ->
                                                                    display_version
                                                                    ();
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7374)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7366
                                                                     in
                                                                    (118,
                                                                    "version",
                                                                    uu____7365,
                                                                    "Display version number")
                                                                     in
                                                                    let uu____7391
                                                                    =
                                                                    let uu____7405
                                                                    =
                                                                    let uu____7417
                                                                    =
                                                                    let uu____7418
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7418
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    uu____7417,
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)")
                                                                     in
                                                                    let uu____7425
                                                                    =
                                                                    let uu____7439
                                                                    =
                                                                    let uu____7453
                                                                    =
                                                                    let uu____7465
                                                                    =
                                                                    let uu____7466
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7466
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3refresh",
                                                                    uu____7465,
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness")
                                                                     in
                                                                    let uu____7473
                                                                    =
                                                                    let uu____7487
                                                                    =
                                                                    let uu____7501
                                                                    =
                                                                    let uu____7515
                                                                    =
                                                                    let uu____7529
                                                                    =
                                                                    let uu____7543
                                                                    =
                                                                    let uu____7555
                                                                    =
                                                                    let uu____7556
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7556
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    uu____7555,
                                                                    "Don't check positivity of inductive types")
                                                                     in
                                                                    let uu____7563
                                                                    =
                                                                    let uu____7577
                                                                    =
                                                                    let uu____7589
                                                                    =
                                                                    let uu____7590
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7590
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__ml_no_eta_expand_coertions",
                                                                    uu____7589,
                                                                    "Do not eta-expand coertions in generated OCaml")
                                                                     in
                                                                    let uu____7597
                                                                    =
                                                                    let uu____7611
                                                                    =
                                                                    let uu____7625
                                                                    =
                                                                    let uu____7639
                                                                    =
                                                                    let uu____7653
                                                                    =
                                                                    let uu____7665
                                                                    =
                                                                    let uu____7666
                                                                    =
                                                                    let uu____7674
                                                                    =
                                                                    let uu____7675
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7675
                                                                     in
                                                                    ((fun
                                                                    uu____7681
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    uu____7674)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7666
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    uu____7665,
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms")
                                                                     in
                                                                    let uu____7709
                                                                    =
                                                                    let uu____7723
                                                                    =
                                                                    let uu____7735
                                                                    =
                                                                    let uu____7736
                                                                    =
                                                                    let uu____7744
                                                                    =
                                                                    let uu____7745
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7745
                                                                     in
                                                                    ((fun
                                                                    uu____7751
                                                                     ->
                                                                    FStar_ST.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    uu____7744)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7736
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    uu____7735,
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking")
                                                                     in
                                                                    let uu____7779
                                                                    =
                                                                    let uu____7793
                                                                    =
                                                                    let uu____7805
                                                                    =
                                                                    let uu____7806
                                                                    =
                                                                    let uu____7814
                                                                    =
                                                                    let uu____7815
                                                                    =
                                                                    mk_bool
                                                                    true  in
                                                                    Const
                                                                    uu____7815
                                                                     in
                                                                    ((fun
                                                                    uu____7822
                                                                     ->
                                                                    (
                                                                    let uu____7824
                                                                    =
                                                                    specs ()
                                                                     in
                                                                    display_usage_aux
                                                                    uu____7824);
                                                                    FStar_All.exit
                                                                    (Prims.parse_int "0")),
                                                                    uu____7814)
                                                                     in
                                                                    WithSideEffect
                                                                    uu____7806
                                                                     in
                                                                    (104,
                                                                    "help",
                                                                    uu____7805,
                                                                    "Display this information")
                                                                     in
                                                                    [uu____7793]
                                                                     in
                                                                    uu____7723
                                                                    ::
                                                                    uu____7779
                                                                     in
                                                                    uu____7653
                                                                    ::
                                                                    uu____7709
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    "Use normalization by evaluation as the default normalization srategy (default 'false')")
                                                                    ::
                                                                    uu____7639
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_extracted_interfaces",
                                                                    BoolStr,
                                                                    "Extract interfaces from the dependencies and use them for verification (default 'false')")
                                                                    ::
                                                                    uu____7625
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "warn_error",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "")),
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t- [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t- [-r] silences range [r]\n\t\t- [+r] enables range [r]\n\t\t- [@r] makes range [r] fatal.")
                                                                    ::
                                                                    uu____7611
                                                                     in
                                                                    uu____7577
                                                                    ::
                                                                    uu____7597
                                                                     in
                                                                    uu____7543
                                                                    ::
                                                                    uu____7563
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_two_phase_tc",
                                                                    BoolStr,
                                                                    "Use the two phase typechecker (default 'true')")
                                                                    ::
                                                                    uu____7529
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 random seed (default 0)")
                                                                    ::
                                                                    uu____7515
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)")
                                                                    ::
                                                                    uu____7501
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)")
                                                                    ::
                                                                    uu____7487
                                                                     in
                                                                    uu____7453
                                                                    ::
                                                                    uu____7473
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    "Z3 command line options")
                                                                    ::
                                                                    uu____7439
                                                                     in
                                                                    uu____7405
                                                                    ::
                                                                    uu____7425
                                                                     in
                                                                    uu____7353
                                                                    ::
                                                                    uu____7391
                                                                     in
                                                                    uu____7319
                                                                    ::
                                                                    uu____7339
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "__temp_no_proj",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "module_name")),
                                                                    "Don't generate projectors for this module")
                                                                    ::
                                                                    uu____7305
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "vcgen.optimize_bind_as_seq",
                                                                    (EnumStr
                                                                    ["off";
                                                                    "without_type";
                                                                    "with_type"]),
                                                                    "\n\t\tOptimize the generation of verification conditions, \n\t\t\tspecifically the construction of monadic `bind`,\n\t\t\tgenerating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\tBy default, this optimization does not apply.\n\t\t\tWhen the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\tto reconstruct type information.\n\t\t\tWhen `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\tbut at the cost of VC bloat, which may often be redundant.")
                                                                    ::
                                                                    uu____7291
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\tFacts can be include or excluded using the [+|-] qualifier. \n\t\t\tFor example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tremove all facts from FStar.List.Tot.*, \n\t\t\t\tretain all remaining facts from FStar.List.*, \n\t\t\t\tremove all facts from FStar.Reflection.*, \n\t\t\t\tand retain all the rest.\n\t\tNote, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\tMultiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.")
                                                                    ::
                                                                    uu____7277
                                                                     in
                                                                    uu____7243
                                                                    ::
                                                                    uu____7263
                                                                     in
                                                                    uu____7209
                                                                    ::
                                                                    uu____7229
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Use compiled tactics from <path>")
                                                                    ::
                                                                    uu____7195
                                                                     in
                                                                    uu____7161
                                                                    ::
                                                                    uu____7181
                                                                     in
                                                                    uu____7127
                                                                    ::
                                                                    uu____7147
                                                                     in
                                                                    uu____7093
                                                                    ::
                                                                    uu____7113
                                                                     in
                                                                    uu____7059
                                                                    ::
                                                                    uu____7079
                                                                     in
                                                                    uu____7025
                                                                    ::
                                                                    uu____7045
                                                                     in
                                                                    uu____6991
                                                                    ::
                                                                    uu____7011
                                                                     in
                                                                    uu____6957
                                                                    ::
                                                                    uu____6977
                                                                     in
                                                                    uu____6923
                                                                    ::
                                                                    uu____6943
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')")
                                                                    ::
                                                                    uu____6909
                                                                     in
                                                                    uu____6875
                                                                    ::
                                                                    uu____6895
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Trace tactics up to a certain binding depth")
                                                                    ::
                                                                    uu____6861
                                                                     in
                                                                    uu____6827
                                                                    ::
                                                                    uu____6847
                                                                     in
                                                                    uu____6793
                                                                    ::
                                                                    uu____6813
                                                                     in
                                                                    uu____6759
                                                                    ::
                                                                    uu____6779
                                                                     in
                                                                    uu____6725
                                                                    ::
                                                                    uu____6745
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.valid_elim",
                                                                    BoolStr,
                                                                    "Include an axiom in the SMT encoding to eliminate proof-irrelevance into the existence of a proof witness")
                                                                    ::
                                                                    uu____6711
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.valid_intro",
                                                                    BoolStr,
                                                                    "Include an axiom in the SMT encoding to introduce proof-irrelevance from a constructive proof")
                                                                    ::
                                                                    uu____6697
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\tif 'native', use '+, -, -'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6683
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\ti.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\tif 'native' use '*, div, mod';\n\t\tif 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t(default 'boxwrap')")
                                                                    ::
                                                                    uu____6669
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')")
                                                                    ::
                                                                    uu____6655
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)")
                                                                    ::
                                                                    uu____6641
                                                                     in
                                                                    uu____6607
                                                                    ::
                                                                    uu____6627
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'")
                                                                    ::
                                                                    uu____6593
                                                                     in
                                                                    uu____6559
                                                                    ::
                                                                    uu____6579
                                                                     in
                                                                    uu____6525
                                                                    ::
                                                                    uu____6545
                                                                     in
                                                                    uu____6491
                                                                    ::
                                                                    uu____6511
                                                                     in
                                                                    uu____6457
                                                                    ::
                                                                    uu____6477
                                                                     in
                                                                    uu____6423
                                                                    ::
                                                                    uu____6443
                                                                     in
                                                                    uu____6389
                                                                    ::
                                                                    uu____6409
                                                                     in
                                                                    uu____6355
                                                                    ::
                                                                    uu____6375
                                                                     in
                                                                    uu____6321
                                                                    ::
                                                                    uu____6341
                                                                     in
                                                                    uu____6287
                                                                    ::
                                                                    uu____6307
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    "") ::
                                                                    uu____6273
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    "Place output in directory <dir>")
                                                                    ::
                                                                    uu____6259
                                                                     in
                                                                    uu____6225
                                                                    ::
                                                                    uu____6245
                                                                     in
                                                                    uu____6191
                                                                    ::
                                                                    uu____6211
                                                                     in
                                                                    uu____6157
                                                                    ::
                                                                    uu____6177
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    "Deprecated: use --extract instead; Do not extract code from this module")
                                                                    ::
                                                                    uu____6143
                                                                     in
                                                                    uu____6109
                                                                    ::
                                                                    uu____6129
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "n_cores",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)")
                                                                    ::
                                                                    uu____6095
                                                                     in
                                                                    uu____6061
                                                                    ::
                                                                    uu____6081
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "min_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Minimum number of unrolling of recursive functions to try (default 1)")
                                                                    ::
                                                                    uu____6047
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)")
                                                                    ::
                                                                    uu____6033
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try at most (default 8)")
                                                                    ::
                                                                    uu____6019
                                                                     in
                                                                    uu____5985
                                                                    ::
                                                                    uu____6005
                                                                     in
                                                                    uu____5951
                                                                    ::
                                                                    uu____5971
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    "Load compiled module")
                                                                    ::
                                                                    uu____5937
                                                                     in
                                                                    uu____5903
                                                                    ::
                                                                    uu____5923
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    "Retain comments in the logged SMT queries (requires --log_queries; default true)")
                                                                    ::
                                                                    uu____5889
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)")
                                                                    ::
                                                                    uu____5875
                                                                     in
                                                                    (FStar_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    "Number of unrolling of recursive functions to try initially (default 2)")
                                                                    ::
                                                                    uu____5861
                                                                     in
                                                                    uu____5827
                                                                    ::
                                                                    uu____5847
                                                                     in
                                                                  uu____5793
                                                                    ::
                                                                    uu____5813
                                                                   in
                                                                uu____5759 ::
                                                                  uu____5779
                                                                 in
                                                              (FStar_Getopt.noshort,
                                                                "include",
                                                                (ReverseAccumulated
                                                                   (PathStr
                                                                    "path")),
                                                                "A directory in which to search for files included on the command line")
                                                                :: uu____5745
                                                               in
                                                            uu____5711 ::
                                                              uu____5731
                                                             in
                                                          uu____5677 ::
                                                            uu____5697
                                                           in
                                                        uu____5643 ::
                                                          uu____5663
                                                         in
                                                      (FStar_Getopt.noshort,
                                                        "hint_file",
                                                        (PathStr "path"),
                                                        "Read/write hints to <path> (instead of module-specific hints files)")
                                                        :: uu____5629
                                                       in
                                                    uu____5595 :: uu____5615
                                                     in
                                                  uu____5561 :: uu____5581
                                                   in
                                                (FStar_Getopt.noshort,
                                                  "extract_namespace",
                                                  (Accumulated
                                                     (PostProcessed
                                                        (pp_lowercase,
                                                          (SimpleStr
                                                             "namespace name")))),
                                                  "Deprecated: use --extract instead; Only extract modules in the specified namespace")
                                                  :: uu____5547
                                                 in
                                              (FStar_Getopt.noshort,
                                                "extract_module",
                                                (Accumulated
                                                   (PostProcessed
                                                      (pp_lowercase,
                                                        (SimpleStr
                                                           "module_name")))),
                                                "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)")
                                                :: uu____5533
                                               in
                                            (FStar_Getopt.noshort, "extract",
                                              (Accumulated
                                                 (SimpleStr
                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                              "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\tModules can be extracted or not using the [+|-] qualifier. \n\t\t\tFor example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\tnot extract FStar.List.Tot.*, \n\t\t\t\textract remaining modules from FStar.List.*, \n\t\t\t\tnot extract FStar.Reflection.*, \n\t\t\t\tand extract all the rest.\n\t\tNote, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\tMultiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.")
                                              :: uu____5519
                                             in
                                          uu____5485 :: uu____5505  in
                                        uu____5451 :: uu____5471  in
                                      (FStar_Getopt.noshort, "dump_module",
                                        (Accumulated
                                           (SimpleStr "module_name")), "")
                                        :: uu____5437
                                       in
                                    uu____5403 :: uu____5423  in
                                  uu____5369 :: uu____5389  in
                                uu____5335 :: uu____5355  in
                              (FStar_Getopt.noshort, "dep",
                                (EnumStr ["make"; "graph"; "full"; "raw"]),
                                "Output the transitive closure of the full dependency graph in three formats:\n\t 'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t 'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t 'make': (deprecated) a format suitable for 'make', including only dependences among source files")
                                :: uu____5321
                               in
                            (FStar_Getopt.noshort, "defensive",
                              (EnumStr ["no"; "warn"; "fail"]),
                              "Enable several internal sanity checks, useful to track bugs and report issues.\n\t\tif 'no', no checks are performed\n\t\tif 'warn', checks are performed and raise a warning when they fail\n\t\tif 'fail', like 'warn', but the compiler aborts instead of issuing a warning\n\t\t(default 'no')")
                              :: uu____5307
                             in
                          (FStar_Getopt.noshort, "debug_level",
                            (Accumulated
                               (OpenEnumStr
                                  (["Low"; "Medium"; "High"; "Extreme"],
                                    "..."))),
                            "Control the verbosity of debugging info") ::
                            uu____5293
                           in
                        (FStar_Getopt.noshort, "debug",
                          (Accumulated (SimpleStr "module_name")),
                          "Print lots of debugging information while checking module")
                          :: uu____5279
                         in
                      (FStar_Getopt.noshort, "codegen-lib",
                        (Accumulated (SimpleStr "namespace")),
                        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)")
                        :: uu____5265
                       in
                    (FStar_Getopt.noshort, "codegen",
                      (EnumStr ["OCaml"; "FSharp"; "Kremlin"; "Plugin"]),
                      "Generate code for further compilation to executable code, or build a compiler plugin")
                      :: uu____5251
                     in
                  uu____5217 :: uu____5237  in
                uu____5183 :: uu____5203  in
              (FStar_Getopt.noshort, "cache_dir",
                (PostProcessed (pp_validate_dir, (PathStr "dir"))),
                "Read and write .checked and .checked.lax in directory <dir>")
                :: uu____5169
               in
            uu____5135 :: uu____5155  in
          (FStar_Getopt.noshort, "already_cached",
            (Accumulated
               (SimpleStr
                  "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
            "\n\t\tExpects all modules whose names or namespaces match the provided options \n\t\t\tto already have valid .checked files in the include path")
            :: uu____5121
           in
        (FStar_Getopt.noshort, "admit_except",
          (SimpleStr "[symbol|(symbol, id)]"),
          "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)")
          :: uu____5107
         in
      (FStar_Getopt.noshort, "admit_smt_queries", BoolStr,
        "Admit SMT queries, unsafe! (default 'false')") :: uu____5093
       in
    (FStar_Getopt.noshort, "abort_on",
      (PostProcessed
         ((fun uu___7_9388  ->
             match uu___7_9388 with
             | Int x -> (FStar_ST.op_Colon_Equals abort_counter x; Int x)
             | x -> failwith "?"), (IntStr "non-negative integer"))),
      "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)")
      :: uu____5079

and (specs : unit -> FStar_Getopt.opt Prims.list) =
  fun uu____9417  ->
    let uu____9420 = specs_with_types ()  in
    FStar_List.map
      (fun uu____9451  ->
         match uu____9451 with
         | (short,long,typ,doc) ->
             let uu____9473 =
               let uu____9487 = arg_spec_of_opt_type long typ  in
               (short, long, uu____9487, doc)  in
             mk_spec uu____9473) uu____9420

let (settable : Prims.string -> Prims.bool) =
  fun uu___8_9502  ->
    match uu___8_9502 with
    | "abort_on" -> true
    | "admit_except" -> true
    | "admit_smt_queries" -> true
    | "debug" -> true
    | "debug_level" -> true
    | "defensive" -> true
    | "detail_errors" -> true
    | "detail_hint_replay" -> true
    | "eager_inference" -> true
    | "eager_subtyping" -> true
    | "hide_uvar_nums" -> true
    | "hint_file" -> true
    | "hint_info" -> true
    | "initial_fuel" -> true
    | "initial_ifuel" -> true
    | "lax" -> true
    | "load" -> true
    | "log_queries" -> true
    | "log_types" -> true
    | "max_fuel" -> true
    | "max_ifuel" -> true
    | "min_fuel" -> true
    | "no_plugins" -> true
    | "__no_positivity" -> true
    | "normalize_pure_terms_for_extraction" -> true
    | "no_smt" -> true
    | "no_tactics" -> true
    | "print_bound_var_types" -> true
    | "print_effect_args" -> true
    | "print_full_names" -> true
    | "print_implicits" -> true
    | "print_universes" -> true
    | "print_z3_statistics" -> true
    | "prn" -> true
    | "query_stats" -> true
    | "reuse_hint_for" -> true
    | "silent" -> true
    | "smtencoding.elim_box" -> true
    | "smtencoding.l_arith_repr" -> true
    | "smtencoding.nl_arith_repr" -> true
    | "tactic_raw_binders" -> true
    | "tactics_failhard" -> true
    | "tactics_info" -> true
    | "__tactics_nbe" -> true
    | "tactic_trace" -> true
    | "tactic_trace_d" -> true
    | "tcnorm" -> true
    | "__temp_fast_implicits" -> true
    | "__temp_no_proj" -> true
    | "timing" -> true
    | "trace_error" -> true
    | "ugly" -> true
    | "unthrottle_inductives" -> true
    | "use_eq_at_higher_order" -> true
    | "use_two_phase_tc" -> true
    | "using_facts_from" -> true
    | "vcgen.optimize_bind_as_seq" -> true
    | "warn_error" -> true
    | "z3cliopt" -> true
    | "z3refresh" -> true
    | "z3rlimit" -> true
    | "z3rlimit_factor" -> true
    | "z3seed" -> true
    | uu____9631 -> false
  
let (all_specs : FStar_Getopt.opt Prims.list) = specs () 
let (all_specs_with_types :
  (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list)
  = specs_with_types () 
let (settable_specs :
  (FStar_BaseTypes.char * Prims.string * unit FStar_Getopt.opt_variant *
    Prims.string) Prims.list)
  =
  FStar_All.pipe_right all_specs
    (FStar_List.filter
       (fun uu____9715  ->
          match uu____9715 with
          | (uu____9730,x,uu____9732,uu____9733) -> settable x))
  
let (display_usage : unit -> unit) =
  fun uu____9749  ->
    let uu____9750 = specs ()  in display_usage_aux uu____9750
  
let (fstar_bin_directory : Prims.string) = FStar_Util.get_exec_dir () 
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | File_argument uu____9782 -> true
    | uu____9785 -> false
  
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | File_argument uu____9795 -> uu____9795
  
let (set_options : Prims.string -> FStar_Getopt.parse_cmdline_res) =
  fun s  ->
    try
      (fun uu___464_9806  ->
         match () with
         | () ->
             if s = ""
             then FStar_Getopt.Success
             else
               FStar_Getopt.parse_string settable_specs
                 (fun s1  -> FStar_Exn.raise (File_argument s1)) s) ()
    with
    | File_argument s1 ->
        let uu____9823 =
          FStar_Util.format1 "File %s is not a valid option" s1  in
        FStar_Getopt.Error uu____9823
  
let (file_list_ : Prims.string Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (parse_cmd_line :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____9848  ->
    let res =
      FStar_Getopt.parse_cmdline all_specs
        (fun i  ->
           let uu____9854 =
             let uu____9858 = FStar_ST.op_Bang file_list_  in
             FStar_List.append uu____9858 [i]  in
           FStar_ST.op_Colon_Equals file_list_ uu____9854)
       in
    let uu____9915 =
      let uu____9919 = FStar_ST.op_Bang file_list_  in
      FStar_List.map FStar_Common.try_convert_file_name_to_mixed uu____9919
       in
    (res, uu____9915)
  
let (file_list : unit -> Prims.string Prims.list) =
  fun uu____9961  -> FStar_ST.op_Bang file_list_ 
let (restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res)
  =
  fun should_clear  ->
    let old_verify_module = get_verify_module ()  in
    if should_clear then clear () else init ();
    (let r =
       let uu____10004 = specs ()  in
       FStar_Getopt.parse_cmdline uu____10004 (fun x  -> ())  in
     (let uu____10011 =
        let uu____10017 =
          let uu____10018 = FStar_List.map mk_string old_verify_module  in
          List uu____10018  in
        ("verify_module", uu____10017)  in
      set_option' uu____10011);
     r)
  
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f  ->
    let f1 = FStar_Util.basename f  in
    let f2 =
      let uu____10037 =
        let uu____10039 =
          let uu____10041 =
            let uu____10043 = FStar_Util.get_file_extension f1  in
            FStar_String.length uu____10043  in
          (FStar_String.length f1) - uu____10041  in
        uu____10039 - (Prims.parse_int "1")  in
      FStar_String.substring f1 (Prims.parse_int "0") uu____10037  in
    FStar_String.lowercase f2
  
let (should_verify : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____10056 = get_lax ()  in
    if uu____10056
    then false
    else
      (let l = get_verify_module ()  in
       FStar_List.contains (FStar_String.lowercase m) l)
  
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn  ->
    let uu____10077 = module_name_of_file_name fn  in
    should_verify uu____10077
  
let (module_name_eq : Prims.string -> Prims.string -> Prims.bool) =
  fun m1  ->
    fun m2  -> (FStar_String.lowercase m1) = (FStar_String.lowercase m2)
  
let (dont_gen_projectors : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____10105 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____10105 (FStar_List.existsb (module_name_eq m))
  
let (should_print_message : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____10123 = should_verify m  in
    if uu____10123 then m <> "Prims" else false
  
let (include_path : unit -> Prims.string Prims.list) =
  fun uu____10140  ->
    let cache_dir =
      let uu____10145 = get_cache_dir ()  in
      match uu____10145 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some c -> [c]  in
    let uu____10159 = get_no_default_includes ()  in
    if uu____10159
    then
      let uu____10165 = get_include ()  in
      FStar_List.append cache_dir uu____10165
    else
      (let lib_paths =
         let uu____10176 = FStar_Util.expand_environment_variable "FSTAR_LIB"
            in
         match uu____10176 with
         | FStar_Pervasives_Native.None  ->
             let fstar_home = FStar_String.op_Hat fstar_bin_directory "/.."
                in
             let defs = universe_include_path_base_dirs  in
             let uu____10192 =
               FStar_All.pipe_right defs
                 (FStar_List.map (fun x  -> FStar_String.op_Hat fstar_home x))
                in
             FStar_All.pipe_right uu____10192
               (FStar_List.filter FStar_Util.file_exists)
         | FStar_Pervasives_Native.Some s -> [s]  in
       let uu____10219 =
         let uu____10223 =
           let uu____10227 = get_include ()  in
           FStar_List.append uu____10227 ["."]  in
         FStar_List.append lib_paths uu____10223  in
       FStar_List.append cache_dir uu____10219)
  
let (find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option)
  =
  let file_map = FStar_Util.smap_create (Prims.parse_int "100")  in
  fun filename  ->
    let uu____10258 = FStar_Util.smap_try_find file_map filename  in
    match uu____10258 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let result =
          try
            (fun uu___515_10289  ->
               match () with
               | () ->
                   let uu____10293 = FStar_Util.is_path_absolute filename  in
                   if uu____10293
                   then
                     (if FStar_Util.file_exists filename
                      then FStar_Pervasives_Native.Some filename
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____10309 =
                        let uu____10313 = include_path ()  in
                        FStar_List.rev uu____10313  in
                      FStar_Util.find_map uu____10309
                        (fun p  ->
                           let path =
                             if p = "."
                             then filename
                             else FStar_Util.join_paths p filename  in
                           if FStar_Util.file_exists path
                           then FStar_Pervasives_Native.Some path
                           else FStar_Pervasives_Native.None))) ()
          with | uu___514_10341 -> FStar_Pervasives_Native.None  in
        (if FStar_Option.isSome result
         then FStar_Util.smap_add file_map filename result
         else ();
         result)
  
let (prims : unit -> Prims.string) =
  fun uu____10360  ->
    let uu____10361 = get_prims ()  in
    match uu____10361 with
    | FStar_Pervasives_Native.None  ->
        let filename = "prims.fst"  in
        let uu____10370 = find_file filename  in
        (match uu____10370 with
         | FStar_Pervasives_Native.Some result -> result
         | FStar_Pervasives_Native.None  ->
             let uu____10379 =
               FStar_Util.format1
                 "unable to find required file \"%s\" in the module search path.\n"
                 filename
                in
             failwith uu____10379)
    | FStar_Pervasives_Native.Some x -> x
  
let (prims_basename : unit -> Prims.string) =
  fun uu____10392  ->
    let uu____10393 = prims ()  in FStar_Util.basename uu____10393
  
let (pervasives : unit -> Prims.string) =
  fun uu____10401  ->
    let filename = "FStar.Pervasives.fst"  in
    let uu____10405 = find_file filename  in
    match uu____10405 with
    | FStar_Pervasives_Native.Some result -> result
    | FStar_Pervasives_Native.None  ->
        let uu____10414 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10414
  
let (pervasives_basename : unit -> Prims.string) =
  fun uu____10424  ->
    let uu____10425 = pervasives ()  in FStar_Util.basename uu____10425
  
let (pervasives_native_basename : unit -> Prims.string) =
  fun uu____10433  ->
    let filename = "FStar.Pervasives.Native.fst"  in
    let uu____10437 = find_file filename  in
    match uu____10437 with
    | FStar_Pervasives_Native.Some result -> FStar_Util.basename result
    | FStar_Pervasives_Native.None  ->
        let uu____10446 =
          FStar_Util.format1
            "unable to find required file \"%s\" in the module search path.\n"
            filename
           in
        failwith uu____10446
  
let (prepend_output_dir : Prims.string -> Prims.string) =
  fun fname  ->
    let uu____10459 = get_odir ()  in
    match uu____10459 with
    | FStar_Pervasives_Native.None  -> fname
    | FStar_Pervasives_Native.Some x -> FStar_Util.join_paths x fname
  
let (prepend_cache_dir : Prims.string -> Prims.string) =
  fun fpath  ->
    let uu____10477 = get_cache_dir ()  in
    match uu____10477 with
    | FStar_Pervasives_Native.None  -> fpath
    | FStar_Pervasives_Native.Some x ->
        let uu____10486 = FStar_Util.basename fpath  in
        FStar_Util.join_paths x uu____10486
  
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text  -> FStar_String.split [46] text 
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns  ->
    let cache = FStar_Util.smap_create (Prims.parse_int "31")  in
    let with_cache f s =
      let uu____10608 = FStar_Util.smap_try_find cache s  in
      match uu____10608 with
      | FStar_Pervasives_Native.Some s1 -> s1
      | FStar_Pervasives_Native.None  ->
          let res = f s  in (FStar_Util.smap_add cache s res; res)
       in
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if s = "-*"
        then ([], false)
        else
          if FStar_Util.starts_with s "-"
          then
            (let path =
               let uu____10762 =
                 FStar_Util.substring_from s (Prims.parse_int "1")  in
               path_of_text uu____10762  in
             (path, false))
          else
            (let s1 =
               if FStar_Util.starts_with s "+"
               then FStar_Util.substring_from s (Prims.parse_int "1")
               else s  in
             ((path_of_text s1), true))
       in
    let uu____10785 =
      FStar_All.pipe_right ns
        (FStar_List.collect
           (fun s  ->
              let s1 = FStar_Util.trim_string s  in
              if s1 = ""
              then []
              else
                with_cache
                  (fun s2  ->
                     let uu____10853 =
                       let uu____10857 =
                         FStar_All.pipe_right (FStar_Util.splitlines s2)
                           (FStar_List.concatMap
                              (fun s3  -> FStar_Util.split s3 " "))
                          in
                       FStar_All.pipe_right uu____10857
                         (FStar_List.filter (fun s3  -> s3 <> ""))
                        in
                     FStar_All.pipe_right uu____10853
                       (FStar_List.map parse_one_setting)) s1))
       in
    FStar_All.pipe_right uu____10785 FStar_List.rev
  
let (__temp_no_proj : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____10944 = get___temp_no_proj ()  in
    FStar_All.pipe_right uu____10944 (FStar_List.contains s)
  
let (__temp_fast_implicits : unit -> Prims.bool) =
  fun uu____10959  -> lookup_opt "__temp_fast_implicits" as_bool 
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu____10968  -> get_admit_smt_queries () 
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____10977  -> get_admit_except () 
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu____10984  -> get_cache_checked_modules () 
let (cache_off : unit -> Prims.bool) = fun uu____10991  -> get_cache_off () 
let (cmi : unit -> Prims.bool) = fun uu____10998  -> get_cmi () 
type codegen_t =
  | OCaml 
  | FSharp 
  | Kremlin 
  | Plugin 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | OCaml  -> true | uu____11008 -> false
  
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FSharp  -> true | uu____11019 -> false
  
let (uu___is_Kremlin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Kremlin  -> true | uu____11030 -> false
  
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Plugin  -> true | uu____11041 -> false
  
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu____11050  ->
    let uu____11051 = get_codegen ()  in
    FStar_Util.map_opt uu____11051
      (fun uu___9_11057  ->
         match uu___9_11057 with
         | "OCaml" -> OCaml
         | "FSharp" -> FSharp
         | "Kremlin" -> Kremlin
         | "Plugin" -> Plugin
         | uu____11063 -> failwith "Impossible")
  
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu____11076  ->
    let uu____11077 = get_codegen_lib ()  in
    FStar_All.pipe_right uu____11077
      (FStar_List.map (fun x  -> FStar_Util.split x "."))
  
let (debug_any : unit -> Prims.bool) =
  fun uu____11103  -> let uu____11104 = get_debug ()  in uu____11104 <> [] 
let (debug_module : Prims.string -> Prims.bool) =
  fun modul  ->
    let uu____11121 = get_debug ()  in
    FStar_All.pipe_right uu____11121
      (FStar_List.existsb (module_name_eq modul))
  
let (debug_at_level : Prims.string -> debug_level_t -> Prims.bool) =
  fun modul  ->
    fun level  ->
      (let uu____11146 = get_debug ()  in
       FStar_All.pipe_right uu____11146
         (FStar_List.existsb (module_name_eq modul)))
        && (debug_level_geq level)
  
let (defensive : unit -> Prims.bool) =
  fun uu____11161  ->
    let uu____11162 = get_defensive ()  in uu____11162 <> "no"
  
let (defensive_fail : unit -> Prims.bool) =
  fun uu____11172  ->
    let uu____11173 = get_defensive ()  in uu____11173 = "fail"
  
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11185  -> get_dep () 
let (detail_errors : unit -> Prims.bool) =
  fun uu____11192  -> get_detail_errors () 
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu____11199  -> get_detail_hint_replay () 
let (doc : unit -> Prims.bool) = fun uu____11206  -> get_doc () 
let (dump_module : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____11216 = get_dump_module ()  in
    FStar_All.pipe_right uu____11216 (FStar_List.existsb (module_name_eq s))
  
let (eager_subtyping : unit -> Prims.bool) =
  fun uu____11231  -> get_eager_subtyping () 
let (expose_interfaces : unit -> Prims.bool) =
  fun uu____11238  -> get_expose_interfaces () 
let (fs_typ_app : Prims.string -> Prims.bool) =
  fun filename  ->
    let uu____11248 = FStar_ST.op_Bang light_off_files  in
    FStar_List.contains filename uu____11248
  
let (full_context_dependency : unit -> Prims.bool) = fun uu____11284  -> true 
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu____11292  -> get_hide_uvar_nums () 
let (hint_info : unit -> Prims.bool) =
  fun uu____11299  -> (get_hint_info ()) || (get_query_stats ()) 
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11308  -> get_hint_file () 
let (ide : unit -> Prims.bool) = fun uu____11315  -> get_ide () 
let (print : unit -> Prims.bool) = fun uu____11322  -> get_print () 
let (print_in_place : unit -> Prims.bool) =
  fun uu____11329  -> get_print_in_place () 
let profile : 'a . (unit -> 'a) -> ('a -> Prims.string) -> 'a =
  fun f  ->
    fun msg  ->
      let uu____11360 = get_profile ()  in
      if uu____11360
      then
        let uu____11363 = FStar_Util.record_time f  in
        match uu____11363 with
        | (a,time) ->
            ((let uu____11374 = FStar_Util.string_of_int time  in
              let uu____11376 = msg a  in
              FStar_Util.print2 "Elapsed time %s ms: %s\n" uu____11374
                uu____11376);
             a)
      else f ()
  
let (initial_fuel : unit -> Prims.int) =
  fun uu____11387  ->
    let uu____11388 = get_initial_fuel ()  in
    let uu____11390 = get_max_fuel ()  in Prims.min uu____11388 uu____11390
  
let (initial_ifuel : unit -> Prims.int) =
  fun uu____11398  ->
    let uu____11399 = get_initial_ifuel ()  in
    let uu____11401 = get_max_ifuel ()  in Prims.min uu____11399 uu____11401
  
let (interactive : unit -> Prims.bool) =
  fun uu____11409  -> (get_in ()) || (get_ide ()) 
let (lax : unit -> Prims.bool) = fun uu____11416  -> get_lax () 
let (load : unit -> Prims.string Prims.list) =
  fun uu____11425  -> get_load () 
let (legacy_interactive : unit -> Prims.bool) = fun uu____11432  -> get_in () 
let (log_queries : unit -> Prims.bool) =
  fun uu____11439  -> get_log_queries () 
let (keep_query_captions : unit -> Prims.bool) =
  fun uu____11446  -> (log_queries ()) && (get_keep_query_captions ()) 
let (log_types : unit -> Prims.bool) = fun uu____11453  -> get_log_types () 
let (max_fuel : unit -> Prims.int) = fun uu____11460  -> get_max_fuel () 
let (max_ifuel : unit -> Prims.int) = fun uu____11467  -> get_max_ifuel () 
let (min_fuel : unit -> Prims.int) = fun uu____11474  -> get_min_fuel () 
let (ml_ish : unit -> Prims.bool) = fun uu____11481  -> get_MLish () 
let (set_ml_ish : unit -> unit) =
  fun uu____11487  -> set_option "MLish" (Bool true) 
let (n_cores : unit -> Prims.int) = fun uu____11496  -> get_n_cores () 
let (no_default_includes : unit -> Prims.bool) =
  fun uu____11503  -> get_no_default_includes () 
let (no_extract : Prims.string -> Prims.bool) =
  fun s  ->
    let uu____11513 = get_no_extract ()  in
    FStar_All.pipe_right uu____11513 (FStar_List.existsb (module_name_eq s))
  
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu____11528  -> get_normalize_pure_terms_for_extraction () 
let (no_location_info : unit -> Prims.bool) =
  fun uu____11535  -> get_no_location_info () 
let (no_plugins : unit -> Prims.bool) = fun uu____11542  -> get_no_plugins () 
let (no_smt : unit -> Prims.bool) = fun uu____11549  -> get_no_smt () 
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11558  -> get_odir () 
let (ugly : unit -> Prims.bool) = fun uu____11565  -> get_ugly () 
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu____11572  -> get_print_bound_var_types () 
let (print_effect_args : unit -> Prims.bool) =
  fun uu____11579  -> get_print_effect_args () 
let (print_implicits : unit -> Prims.bool) =
  fun uu____11586  -> get_print_implicits () 
let (print_real_names : unit -> Prims.bool) =
  fun uu____11593  -> (get_prn ()) || (get_print_full_names ()) 
let (print_universes : unit -> Prims.bool) =
  fun uu____11600  -> get_print_universes () 
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu____11607  -> get_print_z3_statistics () 
let (query_stats : unit -> Prims.bool) =
  fun uu____11614  -> get_query_stats () 
let (record_hints : unit -> Prims.bool) =
  fun uu____11621  -> get_record_hints () 
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11630  -> get_reuse_hint_for () 
let (silent : unit -> Prims.bool) = fun uu____11637  -> get_silent () 
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu____11644  -> get_smtencoding_elim_box () 
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu____11651  ->
    let uu____11652 = get_smtencoding_nl_arith_repr ()  in
    uu____11652 = "native"
  
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu____11662  ->
    let uu____11663 = get_smtencoding_nl_arith_repr ()  in
    uu____11663 = "wrapped"
  
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu____11673  ->
    let uu____11674 = get_smtencoding_nl_arith_repr ()  in
    uu____11674 = "boxwrap"
  
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu____11684  ->
    let uu____11685 = get_smtencoding_l_arith_repr ()  in
    uu____11685 = "native"
  
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu____11695  ->
    let uu____11696 = get_smtencoding_l_arith_repr ()  in
    uu____11696 = "boxwrap"
  
let (smtencoding_valid_intro : unit -> Prims.bool) =
  fun uu____11706  -> get_smtencoding_valid_intro () 
let (smtencoding_valid_elim : unit -> Prims.bool) =
  fun uu____11713  -> get_smtencoding_valid_elim () 
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu____11720  -> get_tactic_raw_binders () 
let (tactics_failhard : unit -> Prims.bool) =
  fun uu____11727  -> get_tactics_failhard () 
let (tactics_info : unit -> Prims.bool) =
  fun uu____11734  -> get_tactics_info () 
let (tactic_trace : unit -> Prims.bool) =
  fun uu____11741  -> get_tactic_trace () 
let (tactic_trace_d : unit -> Prims.int) =
  fun uu____11748  -> get_tactic_trace_d () 
let (tactics_nbe : unit -> Prims.bool) =
  fun uu____11755  -> get_tactics_nbe () 
let (tcnorm : unit -> Prims.bool) = fun uu____11762  -> get_tcnorm () 
let (timing : unit -> Prims.bool) = fun uu____11769  -> get_timing () 
let (trace_error : unit -> Prims.bool) =
  fun uu____11776  -> get_trace_error () 
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu____11783  -> get_unthrottle_inductives () 
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu____11790  -> get_unsafe_tactic_exec () 
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu____11797  -> get_use_eq_at_higher_order () 
let (use_hints : unit -> Prims.bool) = fun uu____11804  -> get_use_hints () 
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu____11811  -> get_use_hint_hashes () 
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu____11820  -> get_use_native_tactics () 
let (use_tactics : unit -> Prims.bool) =
  fun uu____11827  -> get_use_tactics () 
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu____11843  ->
    let uu____11844 = get_using_facts_from ()  in
    match uu____11844 with
    | FStar_Pervasives_Native.None  -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
  
let (vcgen_optimize_bind_as_seq : unit -> Prims.bool) =
  fun uu____11898  ->
    let uu____11899 = get_vcgen_optimize_bind_as_seq ()  in
    FStar_Option.isSome uu____11899
  
let (vcgen_decorate_with_type : unit -> Prims.bool) =
  fun uu____11910  ->
    let uu____11911 = get_vcgen_optimize_bind_as_seq ()  in
    match uu____11911 with
    | FStar_Pervasives_Native.Some "with_type" -> true
    | uu____11919 -> false
  
let (warn_default_effects : unit -> Prims.bool) =
  fun uu____11930  -> get_warn_default_effects () 
let (z3_exe : unit -> Prims.string) =
  fun uu____11937  ->
    let uu____11938 = get_smt ()  in
    match uu____11938 with
    | FStar_Pervasives_Native.None  -> FStar_Platform.exe "z3"
    | FStar_Pervasives_Native.Some s -> s
  
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu____11956  -> get_z3cliopt () 
let (z3_refresh : unit -> Prims.bool) = fun uu____11963  -> get_z3refresh () 
let (z3_rlimit : unit -> Prims.int) = fun uu____11970  -> get_z3rlimit () 
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu____11977  -> get_z3rlimit_factor () 
let (z3_seed : unit -> Prims.int) = fun uu____11984  -> get_z3seed () 
let (use_two_phase_tc : unit -> Prims.bool) =
  fun uu____11991  ->
    (get_use_two_phase_tc ()) &&
      (let uu____11993 = lax ()  in Prims.op_Negation uu____11993)
  
let (no_positivity : unit -> Prims.bool) =
  fun uu____12001  -> get_no_positivity () 
let (ml_no_eta_expand_coertions : unit -> Prims.bool) =
  fun uu____12008  -> get_ml_no_eta_expand_coertions () 
let (warn_error : unit -> Prims.string) =
  fun uu____12015  ->
    let uu____12016 = get_warn_error ()  in
    FStar_String.concat "" uu____12016
  
let (use_extracted_interfaces : unit -> Prims.bool) =
  fun uu____12027  -> get_use_extracted_interfaces () 
let (use_nbe : unit -> Prims.bool) = fun uu____12034  -> get_use_nbe () 
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let uu____12051 =
      let uu____12053 = trace_error ()  in Prims.op_Negation uu____12053  in
    if uu____12051
    then
      (push ();
       (let r =
          try
            (fun uu___715_12068  ->
               match () with
               | () -> let uu____12073 = f ()  in FStar_Util.Inr uu____12073)
              ()
          with | uu___714_12075 -> FStar_Util.Inl uu___714_12075  in
        pop ();
        (match r with
         | FStar_Util.Inr v1 -> v1
         | FStar_Util.Inl ex -> FStar_Exn.raise ex)))
    else (push (); (let retv = f ()  in pop (); retv))
  
let (module_matches_namespace_filter :
  Prims.string -> Prims.string Prims.list -> Prims.bool) =
  fun m  ->
    fun filter1  ->
      let m1 = FStar_String.lowercase m  in
      let setting = parse_settings filter1  in
      let m_components = path_of_text m1  in
      let rec matches_path m_components1 path =
        match (m_components1, path) with
        | (uu____12156,[]) -> true
        | (m2::ms,p::ps) ->
            (m2 = (FStar_String.lowercase p)) && (matches_path ms ps)
        | uu____12189 -> false  in
      let uu____12201 =
        FStar_All.pipe_right setting
          (FStar_Util.try_find
             (fun uu____12243  ->
                match uu____12243 with
                | (path,uu____12254) -> matches_path m_components path))
         in
      match uu____12201 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____12273,flag) -> flag
  
let (should_extract : Prims.string -> Prims.bool) =
  fun m  ->
    let m1 = FStar_String.lowercase m  in
    let uu____12302 = get_extract ()  in
    match uu____12302 with
    | FStar_Pervasives_Native.Some extract_setting ->
        ((let uu____12317 =
            let uu____12333 = get_no_extract ()  in
            let uu____12337 = get_extract_namespace ()  in
            let uu____12341 = get_extract_module ()  in
            (uu____12333, uu____12337, uu____12341)  in
          match uu____12317 with
          | ([],[],[]) -> ()
          | uu____12366 ->
              failwith
                "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
         module_matches_namespace_filter m1 extract_setting)
    | FStar_Pervasives_Native.None  ->
        let should_extract_namespace m2 =
          let uu____12395 = get_extract_namespace ()  in
          match uu____12395 with
          | [] -> false
          | ns ->
              FStar_All.pipe_right ns
                (FStar_Util.for_some
                   (fun n1  ->
                      FStar_Util.starts_with m2 (FStar_String.lowercase n1)))
           in
        let should_extract_module m2 =
          let uu____12423 = get_extract_module ()  in
          match uu____12423 with
          | [] -> false
          | l ->
              FStar_All.pipe_right l
                (FStar_Util.for_some
                   (fun n1  -> (FStar_String.lowercase n1) = m2))
           in
        (let uu____12445 = no_extract m1  in Prims.op_Negation uu____12445)
          &&
          (let uu____12448 =
             let uu____12459 = get_extract_namespace ()  in
             let uu____12463 = get_extract_module ()  in
             (uu____12459, uu____12463)  in
           (match uu____12448 with
            | ([],[]) -> true
            | uu____12483 ->
                (should_extract_namespace m1) || (should_extract_module m1)))
  
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m  ->
    let uu____12503 = get_already_cached ()  in
    match uu____12503 with
    | FStar_Pervasives_Native.None  -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
  
let (error_flags : unit -> error_flag Prims.list) =
  let cache = FStar_Util.smap_create (Prims.parse_int "10")  in
  fun uu____12536  ->
    let we = warn_error ()  in
    let uu____12539 = FStar_Util.smap_try_find cache we  in
    match uu____12539 with
    | FStar_Pervasives_Native.None  ->
        let r = parse_warn_error we  in (FStar_Util.smap_add cache we r; r)
    | FStar_Pervasives_Native.Some r -> r
  
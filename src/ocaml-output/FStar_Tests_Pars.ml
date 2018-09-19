open Prims
let (test_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Test"] FStar_Range.dummyRange 
let (tcenv_ref :
  FStar_TypeChecker_Env.env FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (test_mod_ref :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref
    (FStar_Pervasives_Native.Some
       {
         FStar_Syntax_Syntax.name = test_lid;
         FStar_Syntax_Syntax.declarations = [];
         FStar_Syntax_Syntax.exports = [];
         FStar_Syntax_Syntax.is_interface = false
       })
  
let (parse_mod :
  Prims.string ->
    FStar_Syntax_DsEnv.env ->
      (FStar_Syntax_DsEnv.env,FStar_Syntax_Syntax.modul)
        FStar_Pervasives_Native.tuple2)
  =
  fun mod_name1  ->
    fun dsenv1  ->
      let uu____49 =
        FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename mod_name1)
         in
      match uu____49 with
      | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl m,uu____55) ->
          let uu____70 =
            let uu____75 = FStar_ToSyntax_ToSyntax.ast_modul_to_modul m  in
            uu____75 dsenv1  in
          (match uu____70 with
           | (m1,env') ->
               let uu____88 =
                 let uu____93 =
                   FStar_Ident.lid_of_path ["Test"] FStar_Range.dummyRange
                    in
                 FStar_Syntax_DsEnv.prepare_module_or_interface false false
                   env' uu____93 FStar_Syntax_DsEnv.default_mii
                  in
               (match uu____88 with | (env'1,uu____99) -> (env'1, m1)))
      | FStar_Parser_ParseIt.ParseError (err,msg,r) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, r))
      | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr uu____107,uu____108)
          ->
          let msg = FStar_Util.format1 "%s: expected a module\n" mod_name1
             in
          FStar_Errors.raise_error (FStar_Errors.Fatal_ModuleExpected, msg)
            FStar_Range.dummyRange
      | FStar_Parser_ParseIt.Term uu____130 ->
          failwith
            "Impossible: parsing a Filename always results in an ASTFragment"
  
let (add_mods :
  Prims.string Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_TypeChecker_Env.env ->
        (FStar_Syntax_DsEnv.env,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple2)
  =
  fun mod_names  ->
    fun dsenv1  ->
      fun env  ->
        FStar_List.fold_left
          (fun uu____173  ->
             fun mod_name1  ->
               match uu____173 with
               | (dsenv2,env1) ->
                   let uu____185 = parse_mod mod_name1 dsenv2  in
                   (match uu____185 with
                    | (dsenv3,string_mod) ->
                        let uu____196 =
                          FStar_TypeChecker_Tc.check_module env1 string_mod
                            false
                           in
                        (match uu____196 with
                         | ((_mod,uu____212),env2) -> (dsenv3, env2))))
          (dsenv1, env) mod_names
  
let (init_once : unit -> unit) =
  fun uu____228  ->
    let solver1 = FStar_SMTEncoding_Solver.dummy  in
    let env =
      FStar_TypeChecker_Env.initial_env FStar_Parser_Dep.empty_deps
        FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1
        FStar_Parser_Const.prims_lid
        FStar_TypeChecker_NBE.normalize_for_unit_test
       in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env;
    (let uu____232 =
       let uu____237 = FStar_Options.prims ()  in
       let uu____238 =
         FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps  in
       parse_mod uu____237 uu____238  in
     match uu____232 with
     | (dsenv1,prims_mod) ->
         let env1 =
           let uu___450_242 = env  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___450_242.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___450_242.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___450_242.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___450_242.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___450_242.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___450_242.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___450_242.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___450_242.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___450_242.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___450_242.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___450_242.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___450_242.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___450_242.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___450_242.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___450_242.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___450_242.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___450_242.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___450_242.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___450_242.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___450_242.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___450_242.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___450_242.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___450_242.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___450_242.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___450_242.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___450_242.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___450_242.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___450_242.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___450_242.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___450_242.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___450_242.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___450_242.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___450_242.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___450_242.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___450_242.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___450_242.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___450_242.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___450_242.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___450_242.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___450_242.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___450_242.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv = dsenv1;
             FStar_TypeChecker_Env.nbe =
               (uu___450_242.FStar_TypeChecker_Env.nbe)
           }  in
         let uu____243 =
           FStar_TypeChecker_Tc.check_module env1 prims_mod false  in
         (match uu____243 with
          | ((_prims_mod,uu____255),env2) ->
              let env3 =
                let uu___451_268 = env2  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___451_268.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___451_268.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___451_268.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___451_268.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___451_268.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___451_268.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___451_268.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___451_268.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___451_268.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___451_268.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___451_268.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___451_268.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___451_268.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___451_268.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___451_268.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___451_268.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___451_268.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___451_268.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___451_268.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___451_268.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___451_268.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___451_268.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___451_268.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___451_268.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___451_268.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___451_268.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___451_268.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___451_268.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___451_268.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___451_268.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___451_268.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___451_268.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___451_268.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___451_268.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___451_268.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___451_268.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___451_268.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___451_268.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___451_268.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___451_268.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___451_268.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv = dsenv1;
                  FStar_TypeChecker_Env.nbe =
                    (uu___451_268.FStar_TypeChecker_Env.nbe)
                }  in
              let env4 =
                FStar_TypeChecker_Env.set_current_module env3 test_lid  in
              FStar_ST.op_Colon_Equals tcenv_ref
                (FStar_Pervasives_Native.Some env4)))
  
let rec (init : unit -> FStar_TypeChecker_Env.env) =
  fun uu____297  ->
    let uu____298 = FStar_ST.op_Bang tcenv_ref  in
    match uu____298 with
    | FStar_Pervasives_Native.Some f -> f
    | uu____325 -> (init_once (); init ())
  
let (frag_of_text : Prims.string -> FStar_Parser_ParseIt.input_frag) =
  fun s  ->
    {
      FStar_Parser_ParseIt.frag_text = s;
      FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1");
      FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
    }
  
let (pars : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    try
      (fun uu___453_343  ->
         match () with
         | () ->
             let tcenv = init ()  in
             let uu____345 =
               let uu____346 =
                 FStar_All.pipe_left
                   (fun _0_1  -> FStar_Parser_ParseIt.Fragment _0_1)
                   (frag_of_text s)
                  in
               FStar_Parser_ParseIt.parse uu____346  in
             (match uu____345 with
              | FStar_Parser_ParseIt.Term t ->
                  FStar_ToSyntax_ToSyntax.desugar_term
                    tcenv.FStar_TypeChecker_Env.dsenv t
              | FStar_Parser_ParseIt.ParseError (e,msg,r) ->
                  FStar_Errors.raise_error (e, msg) r
              | FStar_Parser_ParseIt.ASTFragment uu____351 ->
                  failwith
                    "Impossible: parsing a Fragment always results in a Term"))
        ()
    with
    | uu___452_363 ->
        Obj.magic
          (if
             let uu____364 = FStar_Options.trace_error ()  in
             Prims.op_Negation uu____364
           then Obj.repr (FStar_Exn.raise uu___452_363)
           else Obj.repr (failwith "unreachable"))
  
let (tc' :
  Prims.string ->
    (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple3)
  =
  fun s  ->
    let tm = pars s  in
    let tcenv = init ()  in
    let tcenv1 =
      let uu___454_379 = tcenv  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___454_379.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___454_379.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___454_379.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___454_379.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___454_379.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___454_379.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___454_379.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___454_379.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___454_379.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___454_379.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___454_379.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___454_379.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___454_379.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___454_379.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___454_379.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level = false;
        FStar_TypeChecker_Env.check_uvars =
          (uu___454_379.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___454_379.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___454_379.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___454_379.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___454_379.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___454_379.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___454_379.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___454_379.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___454_379.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___454_379.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___454_379.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___454_379.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___454_379.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___454_379.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___454_379.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___454_379.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___454_379.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___454_379.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___454_379.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___454_379.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___454_379.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___454_379.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___454_379.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___454_379.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___454_379.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___454_379.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___454_379.FStar_TypeChecker_Env.nbe)
      }  in
    let uu____380 = FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm
       in
    match uu____380 with | (tm1,uu____394,g) -> (tm1, g, tcenv1)
  
let (tc : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____401 = tc' s  in
    match uu____401 with | (tm,uu____409,uu____410) -> tm
  
let (tc_nbe : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____416 = tc' s  in
    match uu____416 with
    | (tm,g,tcenv) -> (FStar_TypeChecker_Rel.force_trivial_guard tcenv g; tm)
  
let (tc_nbe_term : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun tm  ->
    let tcenv = init ()  in
    let tcenv1 =
      let uu___455_434 = tcenv  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___455_434.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___455_434.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___455_434.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___455_434.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___455_434.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___455_434.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___455_434.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___455_434.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___455_434.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___455_434.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___455_434.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___455_434.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___455_434.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___455_434.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___455_434.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level = false;
        FStar_TypeChecker_Env.check_uvars =
          (uu___455_434.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___455_434.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___455_434.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___455_434.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___455_434.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___455_434.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___455_434.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___455_434.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___455_434.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___455_434.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___455_434.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___455_434.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___455_434.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___455_434.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___455_434.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___455_434.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___455_434.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___455_434.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___455_434.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___455_434.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___455_434.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___455_434.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___455_434.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___455_434.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___455_434.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___455_434.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___455_434.FStar_TypeChecker_Env.nbe)
      }  in
    let uu____435 = FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm
       in
    match uu____435 with
    | (tm1,uu____443,g) ->
        (FStar_TypeChecker_Rel.force_trivial_guard tcenv1 g; tm1)
  
let (pars_and_tc_fragment : Prims.string -> unit) =
  fun s  ->
    FStar_Options.set_option "trace_error" (FStar_Options.Bool true);
    (let report uu____457 =
       let uu____458 = FStar_Errors.report_all ()  in
       FStar_All.pipe_right uu____458 (fun a1  -> ())  in
     try
       (fun uu___457_466  ->
          match () with
          | () ->
              let tcenv = init ()  in
              let frag = frag_of_text s  in
              (try
                 (fun uu___459_478  ->
                    match () with
                    | () ->
                        let uu____479 =
                          let uu____486 = FStar_ST.op_Bang test_mod_ref  in
                          FStar_Universal.tc_one_fragment uu____486 tcenv
                            frag
                           in
                        (match uu____479 with
                         | (test_mod',tcenv') ->
                             (FStar_ST.op_Colon_Equals test_mod_ref test_mod';
                              FStar_ST.op_Colon_Equals tcenv_ref
                                (FStar_Pervasives_Native.Some tcenv');
                              (let n1 = FStar_Errors.get_err_count ()  in
                               if n1 <> (Prims.parse_int "0")
                               then
                                 (report ();
                                  (let uu____568 =
                                     let uu____573 =
                                       let uu____574 =
                                         FStar_Util.string_of_int n1  in
                                       FStar_Util.format1
                                         "%s errors were reported" uu____574
                                        in
                                     (FStar_Errors.Fatal_ErrorsReported,
                                       uu____573)
                                      in
                                   FStar_Errors.raise_err uu____568))
                               else ())))) ()
               with
               | uu___458_578 ->
                   (report ();
                    FStar_Errors.raise_err
                      (FStar_Errors.Fatal_TcOneFragmentFailed,
                        (Prims.strcat "tc_one_fragment failed: " s))))) ()
     with
     | uu___456_581 ->
         Obj.magic
           (if
              let uu____582 = FStar_Options.trace_error ()  in
              Prims.op_Negation uu____582
            then Obj.repr (FStar_Exn.raise uu___456_581)
            else Obj.repr (failwith "unreachable")))
  
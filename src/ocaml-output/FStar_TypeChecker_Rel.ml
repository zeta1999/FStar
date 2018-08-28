open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____34 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____64 -> false
  
let (__proj__UNIV__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list
    ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  umax_heuristic_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env ;
  wl_implicits: FStar_TypeChecker_Env.implicits }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__wl_deferred
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__smt_ok
  
let (__proj__Mkworklist__item__umax_heuristic_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__umax_heuristic_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__tcenv
  
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Env.implicits) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok;
        umax_heuristic_ok = __fname__umax_heuristic_ok;
        tcenv = __fname__tcenv; wl_implicits = __fname__wl_implicits;_} ->
        __fname__wl_implicits
  
let (new_uvar :
  Prims.string ->
    worklist ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.binding Prims.list ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                    FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              FStar_Syntax_Syntax.should_check_uvar ->
                (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term,
                  worklist) FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun wl  ->
      fun r  ->
        fun gamma  ->
          fun binders  ->
            fun k  ->
              fun should_check  ->
                let ctx_uvar =
                  let uu____388 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____388;
                    FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                    FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                    FStar_Syntax_Syntax.ctx_uvar_typ = k;
                    FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                    FStar_Syntax_Syntax.ctx_uvar_should_check = should_check;
                    FStar_Syntax_Syntax.ctx_uvar_range = r
                  }  in
                FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                  true gamma binders;
                (let t =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_uvar
                        (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange)))
                     FStar_Pervasives_Native.None r
                    in
                 let imp =
                   {
                     FStar_TypeChecker_Env.imp_reason = reason;
                     FStar_TypeChecker_Env.imp_uvar = ctx_uvar;
                     FStar_TypeChecker_Env.imp_tm = t;
                     FStar_TypeChecker_Env.imp_range = r;
                     FStar_TypeChecker_Env.imp_meta =
                       FStar_Pervasives_Native.None
                   }  in
                 (ctx_uvar, t,
                   (let uu___346_423 = wl  in
                    {
                      attempting = (uu___346_423.attempting);
                      wl_deferred = (uu___346_423.wl_deferred);
                      ctr = (uu___346_423.ctr);
                      defer_ok = (uu___346_423.defer_ok);
                      smt_ok = (uu___346_423.smt_ok);
                      umax_heuristic_ok = (uu___346_423.umax_heuristic_ok);
                      tcenv = (uu___346_423.tcenv);
                      wl_implicits = (imp :: (wl.wl_implicits))
                    })))
  
let (copy_uvar :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        worklist ->
          (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term,worklist)
            FStar_Pervasives_Native.tuple3)
  =
  fun u  ->
    fun bs  ->
      fun t  ->
        fun wl  ->
          let env =
            let uu___347_455 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___347_455.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___347_455.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___347_455.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___347_455.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___347_455.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___347_455.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___347_455.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___347_455.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___347_455.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___347_455.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___347_455.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___347_455.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___347_455.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___347_455.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___347_455.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___347_455.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___347_455.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___347_455.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___347_455.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___347_455.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___347_455.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___347_455.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___347_455.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___347_455.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___347_455.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___347_455.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___347_455.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___347_455.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___347_455.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___347_455.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___347_455.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___347_455.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___347_455.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___347_455.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___347_455.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___347_455.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___347_455.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___347_455.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___347_455.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___347_455.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___347_455.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___347_455.FStar_TypeChecker_Env.nbe)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____457 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar u.FStar_Syntax_Syntax.ctx_uvar_reason wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____457 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
  
type solution =
  | Success of
  (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
  FStar_Pervasives_Native.tuple2 
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____494 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____524 -> false
  
let (__proj__Failed__item___0 :
  solution ->
    (FStar_TypeChecker_Common.prob,Prims.string)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____549 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____555 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____561 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___314_576  ->
    match uu___314_576 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____582 = FStar_Syntax_Util.head_and_args t  in
    match uu____582 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____643 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____644 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____656 =
                     let uu____657 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____657  in
                   FStar_Util.format1 "@<%s>" uu____656
                in
             let uu____660 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____643 uu____644 uu____660
         | uu____661 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___315_671  ->
      match uu___315_671 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____675 =
            let uu____678 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____679 =
              let uu____682 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____683 =
                let uu____686 =
                  let uu____689 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____689]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____686
                 in
              uu____682 :: uu____683  in
            uu____678 :: uu____679  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____675
      | FStar_TypeChecker_Common.CProb p ->
          let uu____693 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____694 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____695 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____693 uu____694
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____695
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___316_705  ->
      match uu___316_705 with
      | UNIV (u,t) ->
          let x =
            let uu____709 = FStar_Options.hide_uvar_nums ()  in
            if uu____709
            then "?"
            else
              (let uu____711 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____711 FStar_Util.string_of_int)
             in
          let uu____712 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____712
      | TERM (u,t) ->
          let x =
            let uu____716 = FStar_Options.hide_uvar_nums ()  in
            if uu____716
            then "?"
            else
              (let uu____718 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____718 FStar_Util.string_of_int)
             in
          let uu____719 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____719
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____734 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____734 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____748 =
      let uu____751 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____751
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____748 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____764 .
    (FStar_Syntax_Syntax.term,'Auu____764) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____782 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____800  ->
              match uu____800 with
              | (x,uu____806) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____782 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = true;
      smt_ok = true;
      umax_heuristic_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____836 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____836
         then
           let uu____837 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____837
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___317_843  ->
    match uu___317_843 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____848 .
    'Auu____848 FStar_TypeChecker_Common.problem ->
      'Auu____848 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___348_860 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___348_860.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___348_860.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___348_860.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___348_860.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___348_860.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___348_860.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___348_860.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____867 .
    'Auu____867 FStar_TypeChecker_Common.problem ->
      'Auu____867 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___318_884  ->
    match uu___318_884 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_16  -> FStar_TypeChecker_Common.TProb _0_16)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_17  -> FStar_TypeChecker_Common.CProb _0_17)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___319_899  ->
    match uu___319_899 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___349_905 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___349_905.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___349_905.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___349_905.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___349_905.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___349_905.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___349_905.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___349_905.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___349_905.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___349_905.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___350_913 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___350_913.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___350_913.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___350_913.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___350_913.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___350_913.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___350_913.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___350_913.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___350_913.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___350_913.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___320_925  ->
      match uu___320_925 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___321_930  ->
    match uu___321_930 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___322_941  ->
    match uu___322_941 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___323_954  ->
    match uu___323_954 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___324_967  ->
    match uu___324_967 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___325_980  ->
    match uu___325_980 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___326_993  ->
    match uu___326_993 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___327_1004  ->
    match uu___327_1004 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1019 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1019) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1047 =
          let uu____1048 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1048  in
        if uu____1047
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1082)::bs ->
                 (FStar_TypeChecker_Env.def_check_closed_in rng msg prev
                    bv.FStar_Syntax_Syntax.sort;
                  aux (FStar_List.append prev [bv]) bs)
              in
           aux [] r)
  
let (p_scope :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun prob  ->
    let r =
      match prob with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1128 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1152 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1152]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1128
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1180 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1204 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1204]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1180
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1247 =
          let uu____1248 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1248  in
        if uu____1247
        then ()
        else
          (let uu____1250 =
             let uu____1253 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1253
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1250 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1299 =
          let uu____1300 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1300  in
        if uu____1299
        then ()
        else
          (let uu____1302 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1302)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1319 =
        let uu____1320 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1320  in
      if uu____1319
      then ()
      else
        (let msgf m =
           let uu____1328 =
             let uu____1329 =
               let uu____1330 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.strcat uu____1330 (Prims.strcat "." m)  in
             Prims.strcat "." uu____1329  in
           Prims.strcat msg uu____1328  in
         (let uu____1332 = msgf "scope"  in
          let uu____1333 = p_scope prob  in
          def_scope_wf uu____1332 (p_loc prob) uu____1333);
         (let uu____1345 = msgf "guard"  in
          def_check_scoped uu____1345 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1350 = msgf "lhs"  in
                def_check_scoped uu____1350 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1351 = msgf "rhs"  in
                def_check_scoped uu____1351 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1356 = msgf "lhs"  in
                def_check_scoped_comp uu____1356 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1357 = msgf "rhs"  in
                def_check_scoped_comp uu____1357 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___351_1373 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___351_1373.wl_deferred);
          ctr = (uu___351_1373.ctr);
          defer_ok = (uu___351_1373.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___351_1373.umax_heuristic_ok);
          tcenv = (uu___351_1373.tcenv);
          wl_implicits = (uu___351_1373.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1380 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1380,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___352_1403 = empty_worklist env  in
      let uu____1404 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1404;
        wl_deferred = (uu___352_1403.wl_deferred);
        ctr = (uu___352_1403.ctr);
        defer_ok = (uu___352_1403.defer_ok);
        smt_ok = (uu___352_1403.smt_ok);
        umax_heuristic_ok = (uu___352_1403.umax_heuristic_ok);
        tcenv = (uu___352_1403.tcenv);
        wl_implicits = (uu___352_1403.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___353_1424 = wl  in
        {
          attempting = (uu___353_1424.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___353_1424.ctr);
          defer_ok = (uu___353_1424.defer_ok);
          smt_ok = (uu___353_1424.smt_ok);
          umax_heuristic_ok = (uu___353_1424.umax_heuristic_ok);
          tcenv = (uu___353_1424.tcenv);
          wl_implicits = (uu___353_1424.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___354_1446 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___354_1446.wl_deferred);
         ctr = (uu___354_1446.ctr);
         defer_ok = (uu___354_1446.defer_ok);
         smt_ok = (uu___354_1446.smt_ok);
         umax_heuristic_ok = (uu___354_1446.umax_heuristic_ok);
         tcenv = (uu___354_1446.tcenv);
         wl_implicits = (uu___354_1446.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1457 .
    worklist ->
      'Auu____1457 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1486 = FStar_Syntax_Util.type_u ()  in
          match uu____1486 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____1498 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type
                  FStar_Syntax_Syntax.Allow_unresolved
                 in
              (match uu____1498 with
               | (uu____1509,tt,wl1) ->
                   let uu____1512 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1512, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___328_1517  ->
    match uu___328_1517 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_18  -> FStar_TypeChecker_Common.TProb _0_18) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_19  -> FStar_TypeChecker_Common.CProb _0_19) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1533 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1533 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1543  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1637 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____1637 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____1637 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____1637 FStar_TypeChecker_Common.problem,worklist)
                      FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  let scope1 =
                    match elt with
                    | FStar_Pervasives_Native.None  -> scope
                    | FStar_Pervasives_Native.Some x ->
                        let uu____1722 =
                          let uu____1731 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____1731]  in
                        FStar_List.append scope uu____1722
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____1774 =
                      let uu____1777 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____1777  in
                    FStar_List.append uu____1774
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____1796 =
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____1796 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____1815 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____1815;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = elt;
                          FStar_TypeChecker_Common.logical_guard = lg;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStar_TypeChecker_Common.reason = (reason ::
                            (p_reason orig));
                          FStar_TypeChecker_Common.loc = (p_loc orig);
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        }  in
                      (prob, wl1)
  
let (mk_t_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.typ ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string ->
                  (FStar_TypeChecker_Common.prob,worklist)
                    FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  def_check_prob (Prims.strcat reason ".mk_t.arg") orig;
                  (let uu____1883 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____1883 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_t")
                          (FStar_TypeChecker_Common.TProb p);
                        ((FStar_TypeChecker_Common.TProb p), wl1)))
  
let (mk_c_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.comp ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.comp ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string ->
                  (FStar_TypeChecker_Common.prob,worklist)
                    FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  def_check_prob (Prims.strcat reason ".mk_c.arg") orig;
                  (let uu____1966 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____1966 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.strcat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2002 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2002 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2002 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2002 FStar_TypeChecker_Common.problem,worklist)
                      FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun env  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun subject  ->
              fun loc  ->
                fun reason  ->
                  let lg_ty =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Syntax_Util.ktype0
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2068 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2068]  in
                        let uu____2087 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2087
                     in
                  let uu____2090 =
                    let uu____2097 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.strcat "new_problem: logical guard for " reason)
                      (let uu___355_2107 = wl  in
                       {
                         attempting = (uu___355_2107.attempting);
                         wl_deferred = (uu___355_2107.wl_deferred);
                         ctr = (uu___355_2107.ctr);
                         defer_ok = (uu___355_2107.defer_ok);
                         smt_ok = (uu___355_2107.smt_ok);
                         umax_heuristic_ok =
                           (uu___355_2107.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___355_2107.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2097
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                     in
                  match uu____2090 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2119 =
                              let uu____2124 =
                                let uu____2125 =
                                  let uu____2134 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2134
                                   in
                                [uu____2125]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2124  in
                            uu____2119 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2164 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2164;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = subject;
                          FStar_TypeChecker_Common.logical_guard = lg1;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStar_TypeChecker_Common.reason = [reason];
                          FStar_TypeChecker_Common.loc = loc;
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        }  in
                      (prob, wl1)
  
let (problem_using_guard :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
            Prims.string ->
              FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem)
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let p =
                let uu____2206 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2206;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                  FStar_TypeChecker_Common.logical_guard_uvar =
                    (p_guard_uvar orig);
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }  in
              def_check_prob reason (FStar_TypeChecker_Common.TProb p); p
  
let guard_on_element :
  'Auu____2218 .
    worklist ->
      'Auu____2218 FStar_TypeChecker_Common.problem ->
        FStar_Syntax_Syntax.bv ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun wl  ->
    fun problem  ->
      fun x  ->
        fun phi  ->
          match problem.FStar_TypeChecker_Common.element with
          | FStar_Pervasives_Native.None  ->
              let u =
                (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
                  x.FStar_Syntax_Syntax.sort
                 in
              FStar_Syntax_Util.mk_forall u x phi
          | FStar_Pervasives_Native.Some e ->
              let uu____2251 =
                let uu____2254 =
                  let uu____2255 =
                    let uu____2262 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2262)  in
                  FStar_Syntax_Syntax.NT uu____2255  in
                [uu____2254]  in
              FStar_Syntax_Subst.subst uu____2251 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2282 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2282
        then
          let uu____2283 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2284 = prob_to_string env d  in
          let uu____2285 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2283 uu____2284 uu____2285 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2291 -> failwith "impossible"  in
           let uu____2292 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2304 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2305 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2304, uu____2305)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2309 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2310 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2309, uu____2310)
              in
           match uu____2292 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___329_2328  ->
            match uu___329_2328 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2340 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2344 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2344 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___330_2373  ->
           match uu___330_2373 with
           | UNIV uu____2376 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2383 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2383
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
  
let (find_univ_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___331_2407  ->
           match uu___331_2407 with
           | UNIV (u',t) ->
               let uu____2412 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2412
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2416 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2427 =
        let uu____2428 =
          let uu____2429 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2429
           in
        FStar_Syntax_Subst.compress uu____2428  in
      FStar_All.pipe_right uu____2427 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2440 =
        let uu____2441 =
          FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Env.Beta]
            env t
           in
        FStar_Syntax_Subst.compress uu____2441  in
      FStar_All.pipe_right uu____2440 FStar_Syntax_Util.unlazy_emb
  
let norm_arg :
  'Auu____2448 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2448) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2448)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2471 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2471, (FStar_Pervasives_Native.snd t))
  
let (sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____2522  ->
              match uu____2522 with
              | (x,imp) ->
                  let uu____2541 =
                    let uu___356_2542 = x  in
                    let uu____2543 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___356_2542.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___356_2542.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2543
                    }  in
                  (uu____2541, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2566 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2566
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2570 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2570
        | uu____2573 -> u2  in
      let uu____2574 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2574
  
let (base_and_refinement_maybe_delta :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                    FStar_Pervasives_Native.tuple2
                                    FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2)
  =
  fun should_delta  ->
    fun env  ->
      fun t1  ->
        let norm_refinement env1 t =
          let steps =
            if should_delta
            then
              [FStar_TypeChecker_Env.Weak;
              FStar_TypeChecker_Env.HNF;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
            else [FStar_TypeChecker_Env.Weak; FStar_TypeChecker_Env.HNF]  in
          FStar_TypeChecker_Normalize.normalize_refinement steps env1 t  in
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____2686 = norm_refinement env t12  in
                 match uu____2686 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2701;
                     FStar_Syntax_Syntax.vars = uu____2702;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2726 =
                       let uu____2727 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____2728 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2727 uu____2728
                        in
                     failwith uu____2726)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____2742 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____2742
          | FStar_Syntax_Syntax.Tm_uinst uu____2743 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2778 =
                   let uu____2779 = FStar_Syntax_Subst.compress t1'  in
                   uu____2779.FStar_Syntax_Syntax.n  in
                 match uu____2778 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2794 -> aux true t1'
                 | uu____2801 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____2816 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2845 =
                   let uu____2846 = FStar_Syntax_Subst.compress t1'  in
                   uu____2846.FStar_Syntax_Syntax.n  in
                 match uu____2845 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2861 -> aux true t1'
                 | uu____2868 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____2883 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____2928 =
                   let uu____2929 = FStar_Syntax_Subst.compress t1'  in
                   uu____2929.FStar_Syntax_Syntax.n  in
                 match uu____2928 with
                 | FStar_Syntax_Syntax.Tm_refine uu____2944 -> aux true t1'
                 | uu____2951 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____2966 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____2981 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____2996 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3011 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3026 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3055 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3088 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3109 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3136 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3163 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3200 ->
              let uu____3207 =
                let uu____3208 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3209 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3208 uu____3209
                 in
              failwith uu____3207
          | FStar_Syntax_Syntax.Tm_ascribed uu____3222 ->
              let uu____3249 =
                let uu____3250 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3251 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3250 uu____3251
                 in
              failwith uu____3249
          | FStar_Syntax_Syntax.Tm_delayed uu____3264 ->
              let uu____3287 =
                let uu____3288 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3289 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3288 uu____3289
                 in
              failwith uu____3287
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3302 =
                let uu____3303 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3304 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3303 uu____3304
                 in
              failwith uu____3302
           in
        let uu____3317 = whnf env t1  in aux false uu____3317
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        FStar_TypeChecker_Normalize.normalize_refinement steps env t0
  
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun t  ->
      let uu____3373 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3373 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3413 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3413, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____3437 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____3437 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.bv,
                                                          FStar_Syntax_Syntax.term)
                                                          FStar_Pervasives_Native.tuple2
                                                          FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.term)
  =
  fun uu____3496  ->
    match uu____3496 with
    | (t_base,refopt) ->
        let uu____3527 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3527 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3565 =
      let uu____3568 =
        let uu____3571 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3594  ->
                  match uu____3594 with | (uu____3601,uu____3602,x) -> x))
           in
        FStar_List.append wl.attempting uu____3571  in
      FStar_List.map (wl_prob_to_string wl) uu____3568  in
    FStar_All.pipe_right uu____3565 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3
let flex_t_to_string :
  'Auu____3616 .
    ('Auu____3616,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____3627  ->
    match uu____3627 with
    | (uu____3634,c,args) ->
        let uu____3637 = print_ctx_uvar c  in
        let uu____3638 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____3637 uu____3638
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3644 = FStar_Syntax_Util.head_and_args t  in
    match uu____3644 with
    | (head1,_args) ->
        let uu____3687 =
          let uu____3688 = FStar_Syntax_Subst.compress head1  in
          uu____3688.FStar_Syntax_Syntax.n  in
        (match uu____3687 with
         | FStar_Syntax_Syntax.Tm_uvar uu____3691 -> true
         | uu____3704 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____3710 = FStar_Syntax_Util.head_and_args t  in
    match uu____3710 with
    | (head1,_args) ->
        let uu____3753 =
          let uu____3754 = FStar_Syntax_Subst.compress head1  in
          uu____3754.FStar_Syntax_Syntax.n  in
        (match uu____3753 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____3758) -> u
         | uu____3775 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____3798 = FStar_Syntax_Util.head_and_args t  in
      match uu____3798 with
      | (head1,args) ->
          let uu____3845 =
            let uu____3846 = FStar_Syntax_Subst.compress head1  in
            uu____3846.FStar_Syntax_Syntax.n  in
          (match uu____3845 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____3854)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____3887 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___332_3912  ->
                         match uu___332_3912 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____3916 =
                               let uu____3917 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____3917.FStar_Syntax_Syntax.n  in
                             (match uu____3916 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____3921 -> false)
                         | uu____3922 -> true))
                  in
               (match uu____3887 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____3946 =
                        FStar_List.collect
                          (fun uu___333_3958  ->
                             match uu___333_3958 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____3962 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____3962]
                             | uu____3963 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____3946 FStar_List.rev  in
                    let uu____3986 =
                      let uu____3993 =
                        let uu____4002 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___334_4024  ->
                                  match uu___334_4024 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4028 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4028]
                                  | uu____4029 -> []))
                           in
                        FStar_All.pipe_right uu____4002 FStar_List.rev  in
                      let uu____4052 =
                        let uu____4055 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4055  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____3993 uu____4052
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____3986 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4090  ->
                                match uu____4090 with
                                | (x,i) ->
                                    let uu____4109 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4109, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4140  ->
                                match uu____4140 with
                                | (a,i) ->
                                    let uu____4159 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4159, i)) args_sol
                            in
                         let all_args = FStar_List.append args_sol_s args  in
                         let t1 =
                           FStar_Syntax_Syntax.mk_Tm_app t_v all_args
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         (FStar_Syntax_Unionfind.change
                            uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                          ((t1, v1, all_args), wl1))))
           | uu____4181 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4201 =
          let uu____4224 =
            let uu____4225 = FStar_Syntax_Subst.compress k  in
            uu____4225.FStar_Syntax_Syntax.n  in
          match uu____4224 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4306 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4306)
              else
                (let uu____4340 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4340 with
                 | (ys',t1,uu____4373) ->
                     let uu____4378 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4378))
          | uu____4417 ->
              let uu____4418 =
                let uu____4423 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4423)  in
              ((ys, t), uu____4418)
           in
        match uu____4201 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.mk_residual_comp
                      FStar_Parser_Const.effect_Tot_lid
                      FStar_Pervasives_Native.None []))
            else
              (let c1 =
                 let uu____4516 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4516 c  in
               FStar_Syntax_Util.abs ys1 t1
                 (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_comp_of_comp c1)))
  
let (solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option ->
        uvi Prims.list -> worklist -> worklist)
  =
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            def_check_prob "solve_prob'" prob;
            (let phi =
               match logical_guard with
               | FStar_Pervasives_Native.None  -> FStar_Syntax_Util.t_true
               | FStar_Pervasives_Native.Some phi -> phi  in
             let assign_solution xs uv phi1 =
               (let uu____4590 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4590
                then
                  let uu____4591 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4592 = print_ctx_uvar uv  in
                  let uu____4593 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4591 uu____4592 uu____4593
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____4599 =
                   let uu____4600 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.strcat "solve_prob'.sol." uu____4600  in
                 let uu____4601 =
                   let uu____4604 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____4604
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____4599 uu____4601 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____4637 =
               let uu____4638 =
                 let uu____4639 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____4640 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____4639 uu____4640
                  in
               failwith uu____4638  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____4704  ->
                       match uu____4704 with
                       | (a,i) ->
                           let uu____4725 =
                             let uu____4726 = FStar_Syntax_Subst.compress a
                                in
                             uu____4726.FStar_Syntax_Syntax.n  in
                           (match uu____4725 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____4752 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____4762 =
                 let uu____4763 = is_flex g  in Prims.op_Negation uu____4763
                  in
               if uu____4762
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____4767 = destruct_flex_t g wl  in
                  match uu____4767 with
                  | ((uu____4772,uv1,args),wl1) ->
                      ((let uu____4777 = args_as_binders args  in
                        assign_solution uu____4777 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___357_4779 = wl1  in
              {
                attempting = (uu___357_4779.attempting);
                wl_deferred = (uu___357_4779.wl_deferred);
                ctr = (wl1.ctr + (Prims.parse_int "1"));
                defer_ok = (uu___357_4779.defer_ok);
                smt_ok = (uu___357_4779.smt_ok);
                umax_heuristic_ok = (uu___357_4779.umax_heuristic_ok);
                tcenv = (uu___357_4779.tcenv);
                wl_implicits = (uu___357_4779.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____4800 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____4800
         then
           let uu____4801 = FStar_Util.string_of_int pid  in
           let uu____4802 =
             let uu____4803 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____4803 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____4801 uu____4802
         else ());
        commit sol;
        (let uu___358_4810 = wl  in
         {
           attempting = (uu___358_4810.attempting);
           wl_deferred = (uu___358_4810.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___358_4810.defer_ok);
           smt_ok = (uu___358_4810.smt_ok);
           umax_heuristic_ok = (uu___358_4810.umax_heuristic_ok);
           tcenv = (uu___358_4810.tcenv);
           wl_implicits = (uu___358_4810.wl_implicits)
         })
  
let (solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist)
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          def_check_prob "solve_prob.prob" prob;
          FStar_Util.iter_opt logical_guard
            (def_check_scoped "solve_prob.guard" prob);
          (let conj_guard1 t g =
             match (t, g) with
             | (uu____4872,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____4900 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____4900
              in
           (let uu____4906 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____4906
            then
              let uu____4907 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____4908 =
                let uu____4909 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____4909 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____4907 uu____4908
            else ());
           solve_prob' false prob logical_guard uvis wl)
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2)
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____4934 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____4934 FStar_Util.set_elements  in
      let occurs =
        FStar_All.pipe_right uvars1
          (FStar_Util.for_some
             (fun uv  ->
                FStar_Syntax_Unionfind.equiv
                  uv.FStar_Syntax_Syntax.ctx_uvar_head
                  uk.FStar_Syntax_Syntax.ctx_uvar_head))
         in
      (uvars1, occurs)
  
let (occurs_check :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list,Prims.bool,Prims.string
                                                            FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3)
  =
  fun uk  ->
    fun t  ->
      let uu____4968 = occurs uk t  in
      match uu____4968 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____4997 =
                 let uu____4998 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____4999 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____4998 uu____4999
                  in
               FStar_Pervasives_Native.Some uu____4997)
             in
          (uvars1, (Prims.op_Negation occurs1), msg)
  
let rec (maximal_prefix :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,(FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.binders)
                                     FStar_Pervasives_Native.tuple2)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun bs'  ->
      match (bs, bs') with
      | ((b,i)::bs_tail,(b',i')::bs'_tail) ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            let uu____5112 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5112 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5162 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5218  ->
             match uu____5218 with
             | (x,uu____5230) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5247 = FStar_List.last bs  in
      match uu____5247 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5271) ->
          let uu____5282 =
            FStar_Util.prefix_until
              (fun uu___335_5297  ->
                 match uu___335_5297 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5299 -> false) g
             in
          (match uu____5282 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5312,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5348 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5348 with
        | (pfx,uu____5358) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5370 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5370 with
             | (uu____5377,src',wl1) ->
                 (FStar_Syntax_Unionfind.change
                    src.FStar_Syntax_Syntax.ctx_uvar_head src';
                  wl1))
  
let (restrict_all_uvars :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar Prims.list -> worklist -> worklist)
  =
  fun tgt  ->
    fun sources  ->
      fun wl  -> FStar_List.fold_right (restrict_ctx tgt) sources wl
  
let (intersect_binders :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun g  ->
    fun v1  ->
      fun v2  ->
        let as_set1 v3 =
          FStar_All.pipe_right v3
            (FStar_List.fold_left
               (fun out  ->
                  fun x  ->
                    FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
               FStar_Syntax_Syntax.no_names)
           in
        let v1_set = as_set1 v1  in
        let ctx_binders =
          FStar_List.fold_left
            (fun out  ->
               fun b  ->
                 match b with
                 | FStar_Syntax_Syntax.Binding_var x ->
                     FStar_Util.set_add x out
                 | uu____5489 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____5490 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5554  ->
                  fun uu____5555  ->
                    match (uu____5554, uu____5555) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____5658 =
                          let uu____5659 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____5659
                           in
                        if uu____5658
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____5688 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____5688
                           then
                             let uu____5703 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____5703)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____5490 with | (isect,uu____5752) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5787 'Auu____5788 .
    (FStar_Syntax_Syntax.bv,'Auu____5787) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5788) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5845  ->
              fun uu____5846  ->
                match (uu____5845, uu____5846) with
                | ((a,uu____5864),(b,uu____5866)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5881 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5881) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____5911  ->
           match uu____5911 with
           | (y,uu____5917) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____5926 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5926) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                                    FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ctx  ->
      fun args  ->
        let rec aux seen args1 =
          match args1 with
          | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
          | (arg,i)::args2 ->
              let hd1 = sn env arg  in
              (match hd1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_name a ->
                   let uu____6088 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6088
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6118 -> FStar_Pervasives_Native.None)
           in
        aux [] args
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____6165 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6203 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6216 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___336_6221  ->
    match uu___336_6221 with
    | MisMatch (d1,d2) ->
        let uu____6232 =
          let uu____6233 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____6234 =
            let uu____6235 =
              let uu____6236 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6236 ")"  in
            Prims.strcat ") (" uu____6235  in
          Prims.strcat uu____6233 uu____6234  in
        Prims.strcat "MisMatch (" uu____6232
    | HeadMatch u ->
        let uu____6238 = FStar_Util.string_of_bool u  in
        Prims.strcat "HeadMatch " uu____6238
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___337_6243  ->
    match uu___337_6243 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____6258 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv  in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          if
            ((env.FStar_TypeChecker_Env.curmodule).FStar_Ident.str =
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr)
              && (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
          then d1
          else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when
          i > (Prims.parse_int "0") ->
          let uu____6273 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6273 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6284 -> d)
      | d1 -> d1
  
let rec (delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____6307 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6316 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6342 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6342
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6343 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6344 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6345 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6358 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6371 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6395) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6401,uu____6402) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6444) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6469;
             FStar_Syntax_Syntax.index = uu____6470;
             FStar_Syntax_Syntax.sort = t2;_},uu____6472)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6479 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6480 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6481 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6496 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6503 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6523 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6523
  
let rec (head_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let t11 = FStar_Syntax_Util.unmeta t1  in
        let t21 = FStar_Syntax_Util.unmeta t2  in
        match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____6541;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____6542;
             FStar_Syntax_Syntax.ltyp = uu____6543;
             FStar_Syntax_Syntax.rng = uu____6544;_},uu____6545)
            ->
            let uu____6556 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____6556 t21
        | (uu____6557,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____6558;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____6559;
             FStar_Syntax_Syntax.ltyp = uu____6560;
             FStar_Syntax_Syntax.rng = uu____6561;_})
            ->
            let uu____6572 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____6572
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____6582 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6582
            then FullMatch
            else
              (let uu____6584 =
                 let uu____6593 =
                   let uu____6596 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6596  in
                 let uu____6597 =
                   let uu____6600 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6600  in
                 (uu____6593, uu____6597)  in
               MisMatch uu____6584)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6606),FStar_Syntax_Syntax.Tm_uinst (g,uu____6608)) ->
            let uu____6617 = head_matches env f g  in
            FStar_All.pipe_right uu____6617 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6620 = FStar_Const.eq_const c d  in
            if uu____6620
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6627),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6629)) ->
            let uu____6662 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6662
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6669),FStar_Syntax_Syntax.Tm_refine (y,uu____6671)) ->
            let uu____6680 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6680 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6682),uu____6683) ->
            let uu____6688 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6688 head_match
        | (uu____6689,FStar_Syntax_Syntax.Tm_refine (x,uu____6691)) ->
            let uu____6696 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6696 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6697,FStar_Syntax_Syntax.Tm_type
           uu____6698) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6699,FStar_Syntax_Syntax.Tm_arrow uu____6700) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6730),FStar_Syntax_Syntax.Tm_app (head',uu____6732))
            ->
            let uu____6781 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6781 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6783),uu____6784) ->
            let uu____6809 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6809 head_match
        | (uu____6810,FStar_Syntax_Syntax.Tm_app (head1,uu____6812)) ->
            let uu____6837 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6837 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____6838,FStar_Syntax_Syntax.Tm_let
           uu____6839) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____6864,FStar_Syntax_Syntax.Tm_match uu____6865) ->
            HeadMatch true
        | uu____6910 ->
            let uu____6915 =
              let uu____6924 = delta_depth_of_term env t11  in
              let uu____6927 = delta_depth_of_term env t21  in
              (uu____6924, uu____6927)  in
            MisMatch uu____6915
  
let (head_matches_delta :
  FStar_TypeChecker_Env.env ->
    worklist ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (match_result,(FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                          FStar_Pervasives_Native.tuple2
                          FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun wl  ->
      fun t1  ->
        fun t2  ->
          let maybe_inline t =
            let head1 = FStar_Syntax_Util.head_of t  in
            (let uu____6992 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____6992
             then
               let uu____6993 = FStar_Syntax_Print.term_to_string t  in
               let uu____6994 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____6993 uu____6994
             else ());
            (let uu____6996 =
               let uu____6997 = FStar_Syntax_Util.un_uinst head1  in
               uu____6997.FStar_Syntax_Syntax.n  in
             match uu____6996 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7003 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7003 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7017 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7017
                        then
                          let uu____7018 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7018
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7020 ->
                      let basic_steps =
                        [FStar_TypeChecker_Env.UnfoldUntil
                           FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF;
                        FStar_TypeChecker_Env.Primops;
                        FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.Iota]  in
                      let steps =
                        if wl.smt_ok
                        then basic_steps
                        else
                          (FStar_TypeChecker_Env.Exclude
                             FStar_TypeChecker_Env.Zeta)
                          :: basic_steps
                         in
                      let t' =
                        FStar_TypeChecker_Normalize.normalize steps env t  in
                      let uu____7035 =
                        let uu____7036 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7036 = FStar_Syntax_Util.Equal  in
                      if uu____7035
                      then
                        ((let uu____7040 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7040
                          then
                            let uu____7041 =
                              FStar_Syntax_Print.term_to_string t  in
                            FStar_Util.print1 "Did not inline %s\n"
                              uu____7041
                          else ());
                         FStar_Pervasives_Native.None)
                      else
                        ((let uu____7045 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7045
                          then
                            let uu____7046 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____7047 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7046
                              uu____7047
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7049 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > (Prims.parse_int "0")
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail1 d r t11 t21 =
            (r,
              (if d > (Prims.parse_int "0")
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            (let uu____7187 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7187
             then
               let uu____7188 = FStar_Syntax_Print.term_to_string t11  in
               let uu____7189 = FStar_Syntax_Print.term_to_string t21  in
               let uu____7190 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7188
                 uu____7189 uu____7190
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____7214 =
                 if d1_greater_than_d2
                 then
                   let t1' =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d2;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11
                      in
                   (t1', t21)
                 else
                   (let t2' =
                      normalize_refinement
                        [FStar_TypeChecker_Env.UnfoldUntil d1;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF] env t21
                       in
                    (t11, t2'))
                  in
               match uu____7214 with
               | (t12,t22) ->
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____7259 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____7259 with
               | FStar_Pervasives_Native.None  -> fail1 n_delta r1 t11 t21
               | FStar_Pervasives_Native.Some d1 ->
                   let t12 =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11
                      in
                   let t22 =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t21
                      in
                   aux retry (n_delta + (Prims.parse_int "1")) t12 t22
                in
             match r with
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  i),FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level j))
                 when
                 ((i > (Prims.parse_int "0")) || (j > (Prims.parse_int "0")))
                   && (i <> j)
                 ->
                 reduce_one_and_try_again
                   (FStar_Syntax_Syntax.Delta_equational_at_level i)
                   (FStar_Syntax_Syntax.Delta_equational_at_level j)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____7291),uu____7292)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7310 =
                      let uu____7319 = maybe_inline t11  in
                      let uu____7322 = maybe_inline t21  in
                      (uu____7319, uu____7322)  in
                    match uu____7310 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + (Prims.parse_int "1")) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + (Prims.parse_int "1")) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + (Prims.parse_int "1")) t12 t22)
             | MisMatch
                 (uu____7359,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7360))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____7378 =
                      let uu____7387 = maybe_inline t11  in
                      let uu____7390 = maybe_inline t21  in
                      (uu____7387, uu____7390)  in
                    match uu____7378 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + (Prims.parse_int "1")) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + (Prims.parse_int "1")) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + (Prims.parse_int "1")) t12 t22)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 when d1 = d2 -> reduce_both_and_try_again d1 r
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 -> reduce_one_and_try_again d1 d2
             | MisMatch uu____7439 -> fail1 n_delta r t11 t21
             | uu____7448 -> success n_delta r t11 t21)
             in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7461 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7461
           then
             let uu____7462 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7463 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7464 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7471 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____7483 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7483
                    (fun uu____7517  ->
                       match uu____7517 with
                       | (t11,t21) ->
                           let uu____7524 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7525 =
                             let uu____7526 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7526  in
                           Prims.strcat uu____7524 uu____7525))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____7462 uu____7463 uu____7464 uu____7471
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7538 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7538 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___338_7551  ->
    match uu___338_7551 with
    | FStar_TypeChecker_Common.Rigid_rigid  -> (Prims.parse_int "0")
    | FStar_TypeChecker_Common.Flex_rigid_eq  -> (Prims.parse_int "1")
    | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> (Prims.parse_int "2")
    | FStar_TypeChecker_Common.Flex_rigid  -> (Prims.parse_int "3")
    | FStar_TypeChecker_Common.Rigid_flex  -> (Prims.parse_int "4")
    | FStar_TypeChecker_Common.Flex_flex  -> (Prims.parse_int "5")
  
let (rank_leq :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1  -> fun r2  -> (rank_t_num r1) <= (rank_t_num r2) 
let (rank_less_than :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1  -> fun r2  -> (r1 <> r2) && ((rank_t_num r1) <= (rank_t_num r2)) 
let (compress_tprob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem ->
      FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem)
  =
  fun tcenv  ->
    fun p  ->
      let uu___359_7588 = p  in
      let uu____7591 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7592 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___359_7588.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7591;
        FStar_TypeChecker_Common.relation =
          (uu___359_7588.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7592;
        FStar_TypeChecker_Common.element =
          (uu___359_7588.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___359_7588.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___359_7588.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___359_7588.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___359_7588.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___359_7588.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7606 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7606
            (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20)
      | FStar_TypeChecker_Common.CProb uu____7611 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7633 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7633 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7641 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7641 with
           | (lh,lhs_args) ->
               let uu____7688 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7688 with
                | (rh,rhs_args) ->
                    let uu____7735 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7748,FStar_Syntax_Syntax.Tm_uvar uu____7749)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7838 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7865,uu____7866)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7881,FStar_Syntax_Syntax.Tm_uvar uu____7882)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7897,FStar_Syntax_Syntax.Tm_arrow uu____7898)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___360_7928 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___360_7928.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___360_7928.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___360_7928.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___360_7928.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___360_7928.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___360_7928.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___360_7928.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___360_7928.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___360_7928.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7931,FStar_Syntax_Syntax.Tm_type uu____7932)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___360_7948 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___360_7948.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___360_7948.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___360_7948.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___360_7948.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___360_7948.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___360_7948.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___360_7948.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___360_7948.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___360_7948.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7951,FStar_Syntax_Syntax.Tm_uvar uu____7952)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___360_7968 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___360_7968.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___360_7968.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___360_7968.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___360_7968.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___360_7968.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___360_7968.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___360_7968.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___360_7968.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___360_7968.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7971,FStar_Syntax_Syntax.Tm_uvar uu____7972)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7987,uu____7988)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8003,FStar_Syntax_Syntax.Tm_uvar uu____8004)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8019,uu____8020) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7735 with
                     | (rank,tp1) ->
                         let uu____8033 =
                           FStar_All.pipe_right
                             (let uu___361_8037 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___361_8037.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___361_8037.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___361_8037.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___361_8037.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___361_8037.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___361_8037.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___361_8037.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___361_8037.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___361_8037.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_21  ->
                                FStar_TypeChecker_Common.TProb _0_21)
                            in
                         (rank, uu____8033))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8043 =
            FStar_All.pipe_right
              (let uu___362_8047 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___362_8047.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___362_8047.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___362_8047.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___362_8047.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___362_8047.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___362_8047.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___362_8047.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___362_8047.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___362_8047.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_22  -> FStar_TypeChecker_Common.CProb _0_22)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8043)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____8108 probs =
      match uu____8108 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8189 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____8210 = rank wl.tcenv hd1  in
               (match uu____8210 with
                | (rank1,hd2) ->
                    if rank_leq rank1 FStar_TypeChecker_Common.Flex_rigid_eq
                    then
                      (match min1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.Some
                             (hd2, (FStar_List.append out tl1), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           FStar_Pervasives_Native.Some
                             (hd2, (FStar_List.append out (m :: tl1)), rank1))
                    else
                      (let uu____8269 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8273 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____8273)
                          in
                       if uu____8269
                       then
                         match min1 with
                         | FStar_Pervasives_Native.None  ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd2), out) tl1
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd2), (m ::
                                 out)) tl1
                       else aux (min_rank, min1, (hd2 :: out)) tl1)))
       in
    aux (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, [])
      wl.attempting
  
let (flex_prob_closing :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob -> Prims.bool)
  =
  fun tcenv  ->
    fun bs  ->
      fun p  ->
        let flex_will_be_closed t =
          let uu____8341 = FStar_Syntax_Util.head_and_args t  in
          match uu____8341 with
          | (hd1,uu____8359) ->
              let uu____8384 =
                let uu____8385 = FStar_Syntax_Subst.compress hd1  in
                uu____8385.FStar_Syntax_Syntax.n  in
              (match uu____8384 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____8389) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8423  ->
                           match uu____8423 with
                           | (y,uu____8431) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8453  ->
                                       match uu____8453 with
                                       | (x,uu____8461) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8466 -> false)
           in
        let uu____8467 = rank tcenv p  in
        match uu____8467 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8474 -> true
             | FStar_TypeChecker_Common.TProb p2 ->
                 (match r with
                  | FStar_TypeChecker_Common.Rigid_rigid  -> true
                  | FStar_TypeChecker_Common.Flex_rigid_eq  -> true
                  | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> true
                  | FStar_TypeChecker_Common.Flex_rigid  ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.lhs
                  | FStar_TypeChecker_Common.Rigid_flex  ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.rhs
                  | FStar_TypeChecker_Common.Flex_flex  ->
                      (p2.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                        &&
                        ((flex_will_be_closed p2.FStar_TypeChecker_Common.lhs)
                           ||
                           (flex_will_be_closed
                              p2.FStar_TypeChecker_Common.rhs))))
  
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of Prims.string 
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____8501 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8515 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8529 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> Prims.string) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let rec (really_solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun pid_orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          let u11 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1  in
          let u21 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2  in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u3  ->
                        let uu____8581 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8581 with
                        | (k,uu____8587) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8597 -> false)))
            | uu____8598 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8650 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8656 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8656 = (Prims.parse_int "0")))
                           in
                        if uu____8650 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8672 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8678 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8678 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8672)
               in
            let uu____8679 = filter1 u12  in
            let uu____8682 = filter1 u22  in (uu____8679, uu____8682)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____8712 = filter_out_common_univs us1 us2  in
                   (match uu____8712 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____8771 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____8771 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____8774 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____8784 =
                             let uu____8785 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____8786 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____8785 uu____8786
                              in
                           UFailed uu____8784))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____8810 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____8810 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____8836 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____8836 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____8839 ->
                   let uu____8844 =
                     let uu____8845 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____8846 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)" uu____8845
                       uu____8846 msg
                      in
                   UFailed uu____8844)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8847,uu____8848) ->
              let uu____8849 =
                let uu____8850 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8851 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8850 uu____8851
                 in
              failwith uu____8849
          | (FStar_Syntax_Syntax.U_unknown ,uu____8852) ->
              let uu____8853 =
                let uu____8854 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8855 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8854 uu____8855
                 in
              failwith uu____8853
          | (uu____8856,FStar_Syntax_Syntax.U_bvar uu____8857) ->
              let uu____8858 =
                let uu____8859 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8860 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8859 uu____8860
                 in
              failwith uu____8858
          | (uu____8861,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8862 =
                let uu____8863 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8864 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8863 uu____8864
                 in
              failwith uu____8862
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8888 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8888
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8902 = occurs_univ v1 u3  in
              if uu____8902
              then
                let uu____8903 =
                  let uu____8904 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8905 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8904 uu____8905
                   in
                try_umax_components u11 u21 uu____8903
              else
                (let uu____8907 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8907)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8919 = occurs_univ v1 u3  in
              if uu____8919
              then
                let uu____8920 =
                  let uu____8921 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8922 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8921 uu____8922
                   in
                try_umax_components u11 u21 uu____8920
              else
                (let uu____8924 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8924)
          | (FStar_Syntax_Syntax.U_max uu____8925,uu____8926) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8932 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8932
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8934,FStar_Syntax_Syntax.U_max uu____8935) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8941 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8941
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8943,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8944,FStar_Syntax_Syntax.U_name
             uu____8945) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8946) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8947) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8948,FStar_Syntax_Syntax.U_succ
             uu____8949) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8950,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
  
let (solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          if (wl.tcenv).FStar_TypeChecker_Env.lax_universes
          then USolved wl
          else really_solve_universe_eq orig wl u1 u2
  
let match_num_binders :
  'a 'b .
    ('a Prims.list,'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
      ('a Prims.list,'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
        (('a Prims.list,'b) FStar_Pervasives_Native.tuple2,('a Prims.list,
                                                             'b)
                                                             FStar_Pervasives_Native.tuple2)
          FStar_Pervasives_Native.tuple2
  =
  fun bc1  ->
    fun bc2  ->
      let uu____9050 = bc1  in
      match uu____9050 with
      | (bs1,mk_cod1) ->
          let uu____9094 = bc2  in
          (match uu____9094 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____9205 = aux xs ys  in
                     (match uu____9205 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____9288 =
                       let uu____9295 = mk_cod1 xs  in ([], uu____9295)  in
                     let uu____9298 =
                       let uu____9305 = mk_cod2 ys  in ([], uu____9305)  in
                     (uu____9288, uu____9298)
                  in
               aux bs1 bs2)
  
let (guard_of_prob :
  FStar_TypeChecker_Env.env ->
    worklist ->
      tprob ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun wl  ->
      fun problem  ->
        fun t1  ->
          fun t2  ->
            let has_type_guard t11 t21 =
              match problem.FStar_TypeChecker_Common.element with
              | FStar_Pervasives_Native.Some t ->
                  let uu____9373 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____9373 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____9376 =
                    let uu____9377 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____9377 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____9376
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____9382 = has_type_guard t1 t2  in (uu____9382, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____9383 = has_type_guard t2 t1  in (uu____9383, wl)
  
let is_flex_pat :
  'Auu____9392 'Auu____9393 'Auu____9394 .
    ('Auu____9392,'Auu____9393,'Auu____9394 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___339_9407  ->
    match uu___339_9407 with
    | (uu____9416,uu____9417,[]) -> true
    | uu____9420 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____9451 = f  in
      match uu____9451 with
      | (uu____9458,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____9459;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____9460;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____9463;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____9464;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____9465;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____9525  ->
                 match uu____9525 with
                 | (y,uu____9533) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9687 =
                  let uu____9702 =
                    let uu____9705 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9705  in
                  ((FStar_List.rev pat_binders), uu____9702)  in
                FStar_Pervasives_Native.Some uu____9687
            | (uu____9738,[]) ->
                let uu____9769 =
                  let uu____9784 =
                    let uu____9787 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9787  in
                  ((FStar_List.rev pat_binders), uu____9784)  in
                FStar_Pervasives_Native.Some uu____9769
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9878 =
                  let uu____9879 = FStar_Syntax_Subst.compress a  in
                  uu____9879.FStar_Syntax_Syntax.n  in
                (match uu____9878 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9899 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9899
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___363_9926 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___363_9926.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___363_9926.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9930 =
                            let uu____9931 =
                              let uu____9938 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9938)  in
                            FStar_Syntax_Syntax.NT uu____9931  in
                          [uu____9930]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___364_9954 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___364_9954.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___364_9954.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9955 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9995 =
                  let uu____10010 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____10010  in
                (match uu____9995 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10085 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10118 ->
               let uu____10119 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____10119 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____10438 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____10438
       then
         let uu____10439 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10439
       else ());
      (let uu____10441 = next_prob probs  in
       match uu____10441 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___365_10468 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___365_10468.wl_deferred);
               ctr = (uu___365_10468.ctr);
               defer_ok = (uu___365_10468.defer_ok);
               smt_ok = (uu___365_10468.smt_ok);
               umax_heuristic_ok = (uu___365_10468.umax_heuristic_ok);
               tcenv = (uu___365_10468.tcenv);
               wl_implicits = (uu___365_10468.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____10476 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____10476
                 then
                   let uu____10477 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____10477
                 else
                   if
                     (rank1 = FStar_TypeChecker_Common.Rigid_rigid) ||
                       ((tp.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                          && (rank1 <> FStar_TypeChecker_Common.Flex_flex))
                   then solve_t' env tp probs1
                   else
                     if probs1.defer_ok
                     then
                       solve env
                         (defer "deferring flex_rigid or flex_flex subtyping"
                            hd1 probs1)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t' env
                           (let uu___366_10482 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___366_10482.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___366_10482.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___366_10482.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___366_10482.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___366_10482.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___366_10482.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___366_10482.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___366_10482.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___366_10482.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____10504 ->
                let uu____10513 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____10572  ->
                          match uu____10572 with
                          | (c,uu____10580,uu____10581) -> c < probs.ctr))
                   in
                (match uu____10513 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____10622 =
                            let uu____10627 =
                              FStar_List.map
                                (fun uu____10642  ->
                                   match uu____10642 with
                                   | (uu____10653,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____10627, (probs.wl_implicits))  in
                          Success uu____10622
                      | uu____10656 ->
                          let uu____10665 =
                            let uu___367_10666 = probs  in
                            let uu____10667 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____10686  ->
                                      match uu____10686 with
                                      | (uu____10693,uu____10694,y) -> y))
                               in
                            {
                              attempting = uu____10667;
                              wl_deferred = rest;
                              ctr = (uu___367_10666.ctr);
                              defer_ok = (uu___367_10666.defer_ok);
                              smt_ok = (uu___367_10666.smt_ok);
                              umax_heuristic_ok =
                                (uu___367_10666.umax_heuristic_ok);
                              tcenv = (uu___367_10666.tcenv);
                              wl_implicits = (uu___367_10666.wl_implicits)
                            }  in
                          solve env uu____10665))))

and (solve_one_universe_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> worklist -> solution)
  =
  fun env  ->
    fun orig  ->
      fun u1  ->
        fun u2  ->
          fun wl  ->
            let uu____10701 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10701 with
            | USolved wl1 ->
                let uu____10703 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10703
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 -> solve env (defer "" orig wl1)

and (solve_maybe_uinsts :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol)
  =
  fun env  ->
    fun orig  ->
      fun t1  ->
        fun t2  ->
          fun wl  ->
            let rec aux wl1 us1 us2 =
              match (us1, us2) with
              | ([],[]) -> USolved wl1
              | (u1::us11,u2::us21) ->
                  let uu____10755 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10755 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10758 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10770;
                  FStar_Syntax_Syntax.vars = uu____10771;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10774;
                  FStar_Syntax_Syntax.vars = uu____10775;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10787,uu____10788) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10795,FStar_Syntax_Syntax.Tm_uinst uu____10796) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10803 -> USolved wl

and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____10813 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10813
              then
                let uu____10814 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10814 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and (solve_rigid_flex_or_flex_rigid_subtyping :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Env.env -> tprob -> worklist -> solution)
  =
  fun rank1  ->
    fun env  ->
      fun tp  ->
        fun wl  ->
          def_check_prob "solve_rigid_flex_or_flex_rigid_subtyping"
            (FStar_TypeChecker_Common.TProb tp);
          (let flip = rank1 = FStar_TypeChecker_Common.Flex_rigid  in
           let meet_or_join op ts env1 wl1 =
             let eq_prob t1 t2 wl2 =
               let uu____10900 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____10900 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____10953 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____10953
                then
                  let uu____10954 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____10955 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____10954 uu____10955
                else ());
               (let uu____10957 = head_matches_delta env1 wl2 t1 t2  in
                match uu____10957 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____11002 = eq_prob t1 t2 wl2  in
                         (match uu____11002 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____11023 ->
                         let uu____11032 = eq_prob t1 t2 wl2  in
                         (match uu____11032 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____11081 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____11096 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____11097 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____11096, uu____11097)
                           | FStar_Pervasives_Native.None  ->
                               let uu____11102 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____11103 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____11102, uu____11103)
                            in
                         (match uu____11081 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11134 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____11134 with
                                | (t1_hd,t1_args) ->
                                    let uu____11179 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____11179 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____11243 =
                                              let uu____11250 =
                                                let uu____11261 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____11261 :: t1_args  in
                                              let uu____11278 =
                                                let uu____11287 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____11287 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____11336  ->
                                                   fun uu____11337  ->
                                                     fun uu____11338  ->
                                                       match (uu____11336,
                                                               uu____11337,
                                                               uu____11338)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____11388),
                                                          (a2,uu____11390))
                                                           ->
                                                           let uu____11427 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____11427
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11250
                                                uu____11278
                                               in
                                            match uu____11243 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___368_11453 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___368_11453.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___368_11453.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___368_11453.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____11461 =
                                                  solve env1 wl'  in
                                                (match uu____11461 with
                                                 | Success (uu____11464,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___369_11468
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___369_11468.attempting);
                                                            wl_deferred =
                                                              (uu___369_11468.wl_deferred);
                                                            ctr =
                                                              (uu___369_11468.ctr);
                                                            defer_ok =
                                                              (uu___369_11468.defer_ok);
                                                            smt_ok =
                                                              (uu___369_11468.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___369_11468.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___369_11468.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____11469 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____11501 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____11501 with
                                | (t1_base,p1_opt) ->
                                    let uu____11536 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____11536 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____11634 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____11634
                                             then x.FStar_Syntax_Syntax.sort
                                             else
                                               FStar_Syntax_Util.refine x t
                                              in
                                           match (p1_opt1, p2_opt1) with
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi1),FStar_Pervasives_Native.Some
                                              (y,phi2)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    ((Prims.parse_int "0"),
                                                      x1)]
                                                  in
                                               let phi11 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi1
                                                  in
                                               let phi21 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi2
                                                  in
                                               let uu____11682 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____11682
                                           | (FStar_Pervasives_Native.None
                                              ,FStar_Pervasives_Native.Some
                                              (x,phi)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    ((Prims.parse_int "0"),
                                                      x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____11712 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11712
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi),FStar_Pervasives_Native.None
                                              ) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    ((Prims.parse_int "0"),
                                                      x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____11742 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____11742
                                           | uu____11745 -> t_base  in
                                         let uu____11762 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____11762 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____11776 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____11776, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11783 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____11783 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____11818 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____11818 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____11853 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____11853
                                                         with
                                                         | (p,wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1
                                                                in
                                                             (t, [p], wl4))))))
                                 in
                              let uu____11877 = combine t11 t21 wl2  in
                              (match uu____11877 with
                               | (t12,ps,wl3) ->
                                   ((let uu____11910 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____11910
                                     then
                                       let uu____11911 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____11911
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____11950 ts1 =
               match uu____11950 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____12013 = pairwise out t wl2  in
                        (match uu____12013 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____12049 =
               let uu____12060 = FStar_List.hd ts  in (uu____12060, [], wl1)
                in
             let uu____12069 = FStar_List.tl ts  in
             aux uu____12049 uu____12069  in
           let uu____12076 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____12076 with
           | (this_flex,this_rigid) ->
               let uu____12100 =
                 let uu____12101 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____12101.FStar_Syntax_Syntax.n  in
               (match uu____12100 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____12126 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____12126
                    then
                      let uu____12127 = destruct_flex_t this_flex wl  in
                      (match uu____12127 with
                       | (flex,wl1) ->
                           let uu____12134 = quasi_pattern env flex  in
                           (match uu____12134 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____12152 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____12152
                                  then
                                    let uu____12153 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12153
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12156 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___370_12159 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___370_12159.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___370_12159.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___370_12159.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___370_12159.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___370_12159.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___370_12159.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___370_12159.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___370_12159.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___370_12159.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____12156)
                | uu____12160 ->
                    ((let uu____12162 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____12162
                      then
                        let uu____12163 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12163
                      else ());
                     (let uu____12165 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____12165 with
                      | (u,_args) ->
                          let uu____12208 =
                            let uu____12209 = FStar_Syntax_Subst.compress u
                               in
                            uu____12209.FStar_Syntax_Syntax.n  in
                          (match uu____12208 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____12236 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____12236 with
                                 | (u',uu____12254) ->
                                     let uu____12279 =
                                       let uu____12280 = whnf env u'  in
                                       uu____12280.FStar_Syntax_Syntax.n  in
                                     (match uu____12279 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12301 -> false)
                                  in
                               let uu____12302 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___340_12325  ->
                                         match uu___340_12325 with
                                         | FStar_TypeChecker_Common.TProb tp1
                                             ->
                                             let tp2 = maybe_invert tp1  in
                                             (match tp2.FStar_TypeChecker_Common.rank
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  rank' when rank1 = rank' ->
                                                  if flip
                                                  then
                                                    equiv1
                                                      tp2.FStar_TypeChecker_Common.lhs
                                                  else
                                                    equiv1
                                                      tp2.FStar_TypeChecker_Common.rhs
                                              | uu____12334 -> false)
                                         | uu____12337 -> false))
                                  in
                               (match uu____12302 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____12351 = whnf env this_rigid
                                         in
                                      let uu____12352 =
                                        FStar_List.collect
                                          (fun uu___341_12358  ->
                                             match uu___341_12358 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____12364 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____12364]
                                             | uu____12366 -> [])
                                          bounds_probs
                                         in
                                      uu____12351 :: uu____12352  in
                                    let uu____12367 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____12367 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____12398 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____12413 =
                                               let uu____12414 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____12414.FStar_Syntax_Syntax.n
                                                in
                                             match uu____12413 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____12426 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____12426)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____12435 -> bound  in
                                           let uu____12436 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____12436)  in
                                         (match uu____12398 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____12465 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____12465
                                                then
                                                  let wl'1 =
                                                    let uu___371_12467 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___371_12467.wl_deferred);
                                                      ctr =
                                                        (uu___371_12467.ctr);
                                                      defer_ok =
                                                        (uu___371_12467.defer_ok);
                                                      smt_ok =
                                                        (uu___371_12467.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___371_12467.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___371_12467.tcenv);
                                                      wl_implicits =
                                                        (uu___371_12467.wl_implicits)
                                                    }  in
                                                  let uu____12468 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____12468
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12471 =
                                                  solve_t env eq_prob
                                                    (let uu___372_12473 = wl'
                                                        in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___372_12473.wl_deferred);
                                                       ctr =
                                                         (uu___372_12473.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___372_12473.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___372_12473.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___372_12473.tcenv);
                                                       wl_implicits =
                                                         (uu___372_12473.wl_implicits)
                                                     })
                                                   in
                                                match uu____12471 with
                                                | Success uu____12474 ->
                                                    let wl2 =
                                                      let uu___373_12480 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___373_12480.wl_deferred);
                                                        ctr =
                                                          (uu___373_12480.ctr);
                                                        defer_ok =
                                                          (uu___373_12480.defer_ok);
                                                        smt_ok =
                                                          (uu___373_12480.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___373_12480.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___373_12480.tcenv);
                                                        wl_implicits =
                                                          (uu___373_12480.wl_implicits)
                                                      }  in
                                                    let g =
                                                      FStar_List.fold_left
                                                        (fun g  ->
                                                           fun p  ->
                                                             FStar_Syntax_Util.mk_conj
                                                               g (p_guard p))
                                                        eq_prob.FStar_TypeChecker_Common.logical_guard
                                                        sub_probs
                                                       in
                                                    let wl3 =
                                                      solve_prob' false
                                                        (FStar_TypeChecker_Common.TProb
                                                           tp)
                                                        (FStar_Pervasives_Native.Some
                                                           g) [] wl2
                                                       in
                                                    let uu____12495 =
                                                      FStar_List.fold_left
                                                        (fun wl4  ->
                                                           fun p  ->
                                                             solve_prob' true
                                                               p
                                                               FStar_Pervasives_Native.None
                                                               [] wl4) wl3
                                                        bounds_probs
                                                       in
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     solve env wl3)
                                                | Failed (p,msg) ->
                                                    ((let uu____12506 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____12506
                                                      then
                                                        let uu____12507 =
                                                          let uu____12508 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12508
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____12507
                                                      else ());
                                                     (let uu____12514 =
                                                        let uu____12529 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____12529)
                                                         in
                                                      match uu____12514 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____12551))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12577 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12577
                                                            with
                                                            | (eq_prob1,wl2)
                                                                ->
                                                                (def_check_prob
                                                                   "meet_or_join3"
                                                                   (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                 (let wl3 =
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    (FStar_Pervasives_Native.Some
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)))
                                                                    [] wl2
                                                                     in
                                                                  let uu____12594
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12594))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____12619 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____12619
                                                            with
                                                            | (eq_prob1,wl2)
                                                                ->
                                                                (def_check_prob
                                                                   "meet_or_join4"
                                                                   (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                 (let phi1 =
                                                                    guard_on_element
                                                                    wl2 tp x
                                                                    phi  in
                                                                  let wl3 =
                                                                    let uu____12637
                                                                    =
                                                                    let uu____12642
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____12642
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____12637
                                                                    [] wl2
                                                                     in
                                                                  let uu____12647
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____12647))))
                                                      | uu____12648 ->
                                                          giveup env
                                                            (Prims.strcat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____12663 when flip ->
                               let uu____12664 =
                                 let uu____12665 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12666 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____12665 uu____12666
                                  in
                               failwith uu____12664
                           | uu____12667 ->
                               let uu____12668 =
                                 let uu____12669 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____12670 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____12669 uu____12670
                                  in
                               failwith uu____12668)))))

and (imitate_arrow :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      worklist ->
        flex_t ->
          FStar_Syntax_Syntax.binders ->
            FStar_Syntax_Syntax.term ->
              FStar_TypeChecker_Common.rel ->
                FStar_Syntax_Syntax.term -> solution)
  =
  fun orig  ->
    fun env  ->
      fun wl  ->
        fun lhs  ->
          fun bs_lhs  ->
            fun t_res_lhs  ->
              fun rel  ->
                fun arrow1  ->
                  let bs_lhs_args =
                    FStar_List.map
                      (fun uu____12704  ->
                         match uu____12704 with
                         | (x,i) ->
                             let uu____12723 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____12723, i)) bs_lhs
                     in
                  let uu____12726 = lhs  in
                  match uu____12726 with
                  | (uu____12727,u_lhs,uu____12729) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12826 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12836 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12836, univ)
                             in
                          match uu____12826 with
                          | (k,univ) ->
                              let uu____12843 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____12843 with
                               | (uu____12860,u,wl3) ->
                                   let uu____12863 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12863, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12889 =
                              let uu____12902 =
                                let uu____12913 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12913 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12964  ->
                                   fun uu____12965  ->
                                     match (uu____12964, uu____12965) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____13066 =
                                           let uu____13073 =
                                             let uu____13076 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13076
                                              in
                                           copy_uvar u_lhs [] uu____13073 wl2
                                            in
                                         (match uu____13066 with
                                          | (uu____13105,t_a,wl3) ->
                                              let uu____13108 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____13108 with
                                               | (uu____13127,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____12902
                                ([], wl1)
                               in
                            (match uu____12889 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___374_13183 = ct  in
                                   let uu____13184 =
                                     let uu____13187 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____13187
                                      in
                                   let uu____13202 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___374_13183.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___374_13183.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13184;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13202;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___374_13183.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___375_13220 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___375_13220.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___375_13220.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____13223 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____13223 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13285 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____13285 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____13296 =
                                          let uu____13301 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____13301)  in
                                        TERM uu____13296  in
                                      let uu____13302 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____13302 with
                                       | (sub_prob,wl3) ->
                                           let uu____13315 =
                                             let uu____13316 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____13316
                                              in
                                           solve env uu____13315))
                             | (x,imp)::formals2 ->
                                 let uu____13338 =
                                   let uu____13345 =
                                     let uu____13348 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____13348
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____13345 wl1
                                    in
                                 (match uu____13338 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____13369 =
                                          let uu____13372 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13372
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____13369 u_x
                                         in
                                      let uu____13373 =
                                        let uu____13376 =
                                          let uu____13379 =
                                            let uu____13380 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____13380, imp)  in
                                          [uu____13379]  in
                                        FStar_List.append bs_terms
                                          uu____13376
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____13373 formals2 wl2)
                              in
                           let uu____13407 = occurs_check u_lhs arrow1  in
                           (match uu____13407 with
                            | (uu____13418,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____13429 =
                                    let uu____13430 = FStar_Option.get msg
                                       in
                                    Prims.strcat "occurs-check failed: "
                                      uu____13430
                                     in
                                  giveup_or_defer env orig wl uu____13429
                                else aux [] [] formals wl))

and (solve_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.prob ->
          worklist ->
            (worklist ->
               FStar_Syntax_Syntax.binders ->
                 FStar_TypeChecker_Env.env ->
                   FStar_Syntax_Syntax.subst_elt Prims.list ->
                     (FStar_TypeChecker_Common.prob,worklist)
                       FStar_Pervasives_Native.tuple2)
              -> solution)
  =
  fun env  ->
    fun bs1  ->
      fun bs2  ->
        fun orig  ->
          fun wl  ->
            fun rhs  ->
              (let uu____13459 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____13459
               then
                 let uu____13460 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____13461 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____13460 (rel_to_string (p_rel orig)) uu____13461
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____13582 = rhs wl1 scope env1 subst1  in
                     (match uu____13582 with
                      | (rhs_prob,wl2) ->
                          ((let uu____13602 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13602
                            then
                              let uu____13603 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____13603
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____13676 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____13676 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___376_13678 = hd1  in
                       let uu____13679 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___376_13678.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___376_13678.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13679
                       }  in
                     let hd21 =
                       let uu___377_13683 = hd2  in
                       let uu____13684 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___377_13683.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___377_13683.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13684
                       }  in
                     let uu____13687 =
                       let uu____13692 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____13692
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____13687 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____13711 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____13711
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____13715 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____13715 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____13778 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____13778
                                  in
                               ((let uu____13796 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____13796
                                 then
                                   let uu____13797 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____13798 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____13797
                                     uu____13798
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____13825 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____13858 = aux wl [] env [] bs1 bs2  in
               match uu____13858 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____13907 = attempt sub_probs wl2  in
                   solve env uu____13907)

and (try_solve_without_smt_or_else :
  FStar_TypeChecker_Env.env ->
    worklist ->
      (FStar_TypeChecker_Env.env -> worklist -> solution) ->
        (FStar_TypeChecker_Env.env ->
           worklist ->
             (FStar_TypeChecker_Common.prob,Prims.string)
               FStar_Pervasives_Native.tuple2 -> solution)
          -> solution)
  =
  fun env  ->
    fun wl  ->
      fun try_solve  ->
        fun else_solve  ->
          let wl' =
            let uu___378_13927 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___378_13927.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___378_13927.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____13935 = try_solve env wl'  in
          match uu____13935 with
          | Success (uu____13936,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___379_13940 = wl  in
                  {
                    attempting = (uu___379_13940.attempting);
                    wl_deferred = (uu___379_13940.wl_deferred);
                    ctr = (uu___379_13940.ctr);
                    defer_ok = (uu___379_13940.defer_ok);
                    smt_ok = (uu___379_13940.smt_ok);
                    umax_heuristic_ok = (uu___379_13940.umax_heuristic_ok);
                    tcenv = (uu___379_13940.tcenv);
                    wl_implicits = (FStar_List.append wl.wl_implicits imps)
                  }  in
                solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____13948 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13948 wl)

and (solve_t_flex_rigid_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      worklist -> flex_t -> FStar_Syntax_Syntax.term -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun lhs  ->
          fun rhs  ->
            let binders_as_bv_set bs =
              let uu____13962 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13962 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13996 = lhs1  in
              match uu____13996 with
              | (uu____13999,ctx_u,uu____14001) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____14009 ->
                        let uu____14010 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____14010 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____14057 = quasi_pattern env1 lhs1  in
              match uu____14057 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____14087) ->
                  let uu____14092 = lhs1  in
                  (match uu____14092 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____14106 = occurs_check ctx_u rhs1  in
                       (match uu____14106 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____14148 =
                                let uu____14155 =
                                  let uu____14156 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____14156
                                   in
                                FStar_Util.Inl uu____14155  in
                              (uu____14148, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____14178 =
                                 let uu____14179 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____14179  in
                               if uu____14178
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____14199 =
                                    let uu____14206 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____14206  in
                                  let uu____14211 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____14199, uu____14211)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____14254 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____14254 with
              | (rhs_hd,args) ->
                  let uu____14297 = FStar_Util.prefix args  in
                  (match uu____14297 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14369 = lhs1  in
                       (match uu____14369 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____14373 =
                              let uu____14384 =
                                let uu____14391 =
                                  let uu____14394 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____14394
                                   in
                                copy_uvar u_lhs [] uu____14391 wl1  in
                              match uu____14384 with
                              | (uu____14421,t_last_arg,wl2) ->
                                  let uu____14424 =
                                    let uu____14431 =
                                      let uu____14432 =
                                        let uu____14441 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____14441]  in
                                      FStar_List.append bs_lhs uu____14432
                                       in
                                    copy_uvar u_lhs uu____14431 t_res_lhs wl2
                                     in
                                  (match uu____14424 with
                                   | (uu____14476,lhs',wl3) ->
                                       let uu____14479 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____14479 with
                                        | (uu____14496,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____14373 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____14517 =
                                     let uu____14518 =
                                       let uu____14523 =
                                         let uu____14524 =
                                           let uu____14527 =
                                             let uu____14532 =
                                               let uu____14533 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____14533]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____14532
                                              in
                                           uu____14527
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____14524
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____14523)  in
                                     TERM uu____14518  in
                                   [uu____14517]  in
                                 let uu____14560 =
                                   let uu____14567 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____14567 with
                                   | (p1,wl3) ->
                                       let uu____14586 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____14586 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____14560 with
                                  | (sub_probs,wl3) ->
                                      let uu____14617 =
                                        let uu____14618 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____14618  in
                                      solve env1 uu____14617))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____14651 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____14651 with
                | (uu____14668,args) ->
                    (match args with | [] -> false | uu____14702 -> true)
                 in
              let is_arrow rhs2 =
                let uu____14719 =
                  let uu____14720 = FStar_Syntax_Subst.compress rhs2  in
                  uu____14720.FStar_Syntax_Syntax.n  in
                match uu____14719 with
                | FStar_Syntax_Syntax.Tm_arrow uu____14723 -> true
                | uu____14738 -> false  in
              let uu____14739 = quasi_pattern env1 lhs1  in
              match uu____14739 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14750 =
                    let uu____14751 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____14751
                     in
                  giveup_or_defer env1 orig1 wl1 uu____14750
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____14758 = is_app rhs1  in
                  if uu____14758
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____14760 = is_arrow rhs1  in
                     if uu____14760
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____14762 =
                          let uu____14763 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____14763
                           in
                        giveup_or_defer env1 orig1 wl1 uu____14762))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-rigid subtyping"
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-rigid subtyping"
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____14766 = lhs  in
                (match uu____14766 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____14770 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____14770 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____14787 =
                              let uu____14790 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____14790
                               in
                            FStar_All.pipe_right uu____14787
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____14807 = occurs_check ctx_uv rhs1  in
                          (match uu____14807 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14829 =
                                   let uu____14830 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____14830
                                    in
                                 giveup_or_defer env orig wl uu____14829
                               else
                                 (let uu____14832 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____14832
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____14837 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____14837
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____14839 =
                                         let uu____14840 =
                                           names_to_string1 fvs2  in
                                         let uu____14841 =
                                           names_to_string1 fvs1  in
                                         let uu____14842 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____14840 uu____14841
                                           uu____14842
                                          in
                                       giveup_or_defer env orig wl
                                         uu____14839)
                                    else first_order orig env wl lhs rhs1))
                      | uu____14850 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____14854 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____14854 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____14877 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____14877
                             | (FStar_Util.Inl msg,uu____14879) ->
                                 first_order orig env wl lhs rhs)))

and (solve_t_flex_flex :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> flex_t -> flex_t -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun lhs  ->
          fun rhs  ->
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-flex subtyping"
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-flex subtyping"
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then giveup_or_defer env orig wl "flex-flex non-pattern"
                else
                  (let uu____14912 =
                     let uu____14929 = quasi_pattern env lhs  in
                     let uu____14936 = quasi_pattern env rhs  in
                     (uu____14929, uu____14936)  in
                   match uu____14912 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14979 = lhs  in
                       (match uu____14979 with
                        | ({ FStar_Syntax_Syntax.n = uu____14980;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14982;_},u_lhs,uu____14984)
                            ->
                            let uu____14987 = rhs  in
                            (match uu____14987 with
                             | (uu____14988,u_rhs,uu____14990) ->
                                 let uu____14991 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14991
                                 then
                                   let uu____14996 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14996
                                 else
                                   (let uu____14998 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____14998 with
                                    | (ctx_w,(ctx_l,ctx_r)) ->
                                        let gamma_w =
                                          gamma_until
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_gamma
                                            ctx_w
                                           in
                                        let zs =
                                          intersect_binders gamma_w
                                            (FStar_List.append ctx_l
                                               binders_lhs)
                                            (FStar_List.append ctx_r
                                               binders_rhs)
                                           in
                                        let uu____15030 =
                                          let uu____15037 =
                                            let uu____15040 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____15040
                                             in
                                          new_uvar
                                            (Prims.strcat "flex-flex quasi:"
                                               (Prims.strcat "\tlhs="
                                                  (Prims.strcat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.strcat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____15037
                                            FStar_Syntax_Syntax.Strict
                                           in
                                        (match uu____15030 with
                                         | (uu____15043,w,wl1) ->
                                             let w_app =
                                               let uu____15049 =
                                                 let uu____15054 =
                                                   FStar_List.map
                                                     (fun uu____15065  ->
                                                        match uu____15065
                                                        with
                                                        | (z,uu____15073) ->
                                                            let uu____15078 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____15078) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____15054
                                                  in
                                               uu____15049
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____15082 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____15082
                                               then
                                                 let uu____15083 =
                                                   let uu____15086 =
                                                     flex_t_to_string lhs  in
                                                   let uu____15087 =
                                                     let uu____15090 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____15091 =
                                                       let uu____15094 =
                                                         term_to_string w  in
                                                       let uu____15095 =
                                                         let uu____15098 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____15105 =
                                                           let uu____15108 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____15115 =
                                                             let uu____15118
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____15118]
                                                              in
                                                           uu____15108 ::
                                                             uu____15115
                                                            in
                                                         uu____15098 ::
                                                           uu____15105
                                                          in
                                                       uu____15094 ::
                                                         uu____15095
                                                        in
                                                     uu____15090 ::
                                                       uu____15091
                                                      in
                                                   uu____15086 :: uu____15087
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____15083
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____15124 =
                                                     let uu____15129 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____15129)  in
                                                   TERM uu____15124  in
                                                 let uu____15130 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____15130
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____15135 =
                                                        let uu____15140 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____15140)
                                                         in
                                                      TERM uu____15135  in
                                                    [s1; s2])
                                                  in
                                               let uu____15141 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____15141))))))
                   | uu____15142 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____15207 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____15207
            then
              let uu____15208 = FStar_Syntax_Print.term_to_string t1  in
              let uu____15209 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____15210 = FStar_Syntax_Print.term_to_string t2  in
              let uu____15211 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____15208 uu____15209 uu____15210 uu____15211
            else ());
           (let uu____15214 = FStar_Syntax_Util.head_and_args t1  in
            match uu____15214 with
            | (head1,args1) ->
                let uu____15257 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____15257 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____15322 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____15322 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____15347 =
                         let uu____15348 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____15349 = args_to_string args1  in
                         let uu____15352 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____15353 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____15348 uu____15349 uu____15352 uu____15353
                          in
                       giveup env1 uu____15347 orig
                     else
                       (let uu____15357 =
                          (nargs = (Prims.parse_int "0")) ||
                            (let uu____15363 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____15363 = FStar_Syntax_Util.Equal)
                           in
                        if uu____15357
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___380_15365 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___380_15365.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___380_15365.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___380_15365.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___380_15365.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___380_15365.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___380_15365.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___380_15365.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___380_15365.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____15372 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____15372
                                    else solve env1 wl2))
                        else
                          (let uu____15375 = base_and_refinement env1 t1  in
                           match uu____15375 with
                           | (base1,refinement1) ->
                               let uu____15400 = base_and_refinement env1 t2
                                  in
                               (match uu____15400 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         let mk_sub_probs wl2 =
                                           let argp =
                                             if need_unif
                                             then
                                               FStar_List.zip
                                                 ((head1,
                                                    FStar_Pervasives_Native.None)
                                                 :: args1)
                                                 ((head2,
                                                    FStar_Pervasives_Native.None)
                                                 :: args2)
                                             else FStar_List.zip args1 args2
                                              in
                                           let uu____15563 =
                                             FStar_List.fold_right
                                               (fun uu____15603  ->
                                                  fun uu____15604  ->
                                                    match (uu____15603,
                                                            uu____15604)
                                                    with
                                                    | (((a1,uu____15656),
                                                        (a2,uu____15658)),
                                                       (probs,wl3)) ->
                                                        let uu____15707 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____15707
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____15563 with
                                           | (subprobs,wl3) ->
                                               ((let uu____15749 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____15749
                                                 then
                                                   let uu____15750 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____15750
                                                 else ());
                                                (let uu____15753 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____15753
                                                 then
                                                   FStar_List.iter
                                                     (def_check_prob
                                                        "solve_t' subprobs")
                                                     subprobs
                                                 else ());
                                                (subprobs, wl3))
                                            in
                                         let solve_sub_probs env2 wl2 =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  if Prims.op_Negation ok
                                                  then solve env2 wl3
                                                  else
                                                    (let uu____15773 =
                                                       mk_sub_probs wl3  in
                                                     match uu____15773 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____15789 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____15789
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____15797 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____15797))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____15820 =
                                                    mk_sub_probs wl3  in
                                                  match uu____15820 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____15834 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____15834)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____15859 =
                                           match uu____15859 with
                                           | (prob,reason) ->
                                               ((let uu____15867 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____15867
                                                 then
                                                   let uu____15868 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____15869 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____15868 uu____15869
                                                     reason
                                                 else ());
                                                (let uu____15871 =
                                                   let uu____15880 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____15883 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____15880, uu____15883)
                                                    in
                                                 match uu____15871 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____15896 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____15896 with
                                                      | (head1',uu____15914)
                                                          ->
                                                          let uu____15939 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____15939
                                                           with
                                                           | (head2',uu____15957)
                                                               ->
                                                               let uu____15982
                                                                 =
                                                                 let uu____15987
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____15988
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____15987,
                                                                   uu____15988)
                                                                  in
                                                               (match uu____15982
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____15990
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____15990
                                                                    then
                                                                    let uu____15991
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____15992
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____15993
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____15994
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____15991
                                                                    uu____15992
                                                                    uu____15993
                                                                    uu____15994
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____15996
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___381_16004
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___381_16004.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___381_16004.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___381_16004.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___381_16004.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___381_16004.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___381_16004.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___381_16004.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___381_16004.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____16006
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____16006
                                                                    then
                                                                    let uu____16007
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____16007
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____16009 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____16021 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____16021 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____16028 =
                                             let uu____16029 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____16029.FStar_Syntax_Syntax.n
                                              in
                                           match uu____16028 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____16033 -> false  in
                                         (match d with
                                          | FStar_Pervasives_Native.Some d1
                                              when
                                              wl1.smt_ok &&
                                                (Prims.op_Negation
                                                   treat_as_injective)
                                              ->
                                              try_solve_without_smt_or_else
                                                env1 wl1
                                                solve_sub_probs_no_smt
                                                (unfold_and_retry d1)
                                          | uu____16035 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____16038 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___382_16074 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___382_16074.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___382_16074.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___382_16074.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___382_16074.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___382_16074.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___382_16074.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___382_16074.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___382_16074.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____16149 = destruct_flex_t scrutinee wl1  in
             match uu____16149 with
             | ((_t,uv,_args),wl2) ->
                 let uu____16160 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____16160 with
                  | (xs,pat_term,uu____16175,uu____16176) ->
                      let uu____16181 =
                        FStar_List.fold_left
                          (fun uu____16204  ->
                             fun x  ->
                               match uu____16204 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____16225 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____16225 with
                                    | (uu____16244,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____16181 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____16265 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____16265 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___383_16281 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___383_16281.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___383_16281.umax_heuristic_ok);
                                    tcenv = (uu___383_16281.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____16289 = solve env1 wl'  in
                                (match uu____16289 with
                                 | Success (uu____16292,imps) ->
                                     let wl'1 =
                                       let uu___384_16295 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___384_16295.wl_deferred);
                                         ctr = (uu___384_16295.ctr);
                                         defer_ok = (uu___384_16295.defer_ok);
                                         smt_ok = (uu___384_16295.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___384_16295.umax_heuristic_ok);
                                         tcenv = (uu___384_16295.tcenv);
                                         wl_implicits =
                                           (uu___384_16295.wl_implicits)
                                       }  in
                                     let uu____16296 = solve env1 wl'1  in
                                     (match uu____16296 with
                                      | Success (uu____16299,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___385_16303 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___385_16303.attempting);
                                                 wl_deferred =
                                                   (uu___385_16303.wl_deferred);
                                                 ctr = (uu___385_16303.ctr);
                                                 defer_ok =
                                                   (uu___385_16303.defer_ok);
                                                 smt_ok =
                                                   (uu___385_16303.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___385_16303.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___385_16303.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____16304 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____16310 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____16331 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____16331
                 then
                   let uu____16332 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____16333 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____16332 uu____16333
                 else ());
                (let uu____16335 =
                   let uu____16356 =
                     let uu____16365 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____16365)  in
                   let uu____16372 =
                     let uu____16381 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____16381)  in
                   (uu____16356, uu____16372)  in
                 match uu____16335 with
                 | ((uu____16410,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____16413;
                                   FStar_Syntax_Syntax.vars = uu____16414;_}),
                    (s,t)) ->
                     let uu____16485 =
                       let uu____16486 = is_flex scrutinee  in
                       Prims.op_Negation uu____16486  in
                     if uu____16485
                     then
                       ((let uu____16494 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____16494
                         then
                           let uu____16495 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____16495
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____16507 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16507
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____16513 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____16513
                           then
                             let uu____16514 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____16515 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____16514 uu____16515
                           else ());
                          (let pat_discriminates uu___342_16536 =
                             match uu___342_16536 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____16551;
                                  FStar_Syntax_Syntax.p = uu____16552;_},FStar_Pervasives_Native.None
                                ,uu____16553) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____16566;
                                  FStar_Syntax_Syntax.p = uu____16567;_},FStar_Pervasives_Native.None
                                ,uu____16568) -> true
                             | uu____16593 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____16693 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____16693 with
                                       | (uu____16694,uu____16695,t') ->
                                           let uu____16713 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____16713 with
                                            | (FullMatch ,uu____16724) ->
                                                true
                                            | (HeadMatch
                                               uu____16737,uu____16738) ->
                                                true
                                            | uu____16751 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____16784 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____16784
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____16789 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____16789 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____16877,uu____16878) ->
                                       branches1
                                   | uu____17023 -> branches  in
                                 let uu____17078 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____17087 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____17087 with
                                        | (p,uu____17091,uu____17092) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_23  -> FStar_Util.Inr _0_23)
                                   uu____17078))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17148 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____17148 with
                                | (p,uu____17156,e) ->
                                    ((let uu____17175 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____17175
                                      then
                                        let uu____17176 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____17177 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17176 uu____17177
                                      else ());
                                     (let uu____17179 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_24  -> FStar_Util.Inr _0_24)
                                        uu____17179)))))
                 | ((s,t),(uu____17194,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____17197;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17198;_}))
                     ->
                     let uu____17267 =
                       let uu____17268 = is_flex scrutinee  in
                       Prims.op_Negation uu____17268  in
                     if uu____17267
                     then
                       ((let uu____17276 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____17276
                         then
                           let uu____17277 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____17277
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____17289 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17289
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____17295 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____17295
                           then
                             let uu____17296 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____17297 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____17296 uu____17297
                           else ());
                          (let pat_discriminates uu___342_17318 =
                             match uu___342_17318 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____17333;
                                  FStar_Syntax_Syntax.p = uu____17334;_},FStar_Pervasives_Native.None
                                ,uu____17335) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____17348;
                                  FStar_Syntax_Syntax.p = uu____17349;_},FStar_Pervasives_Native.None
                                ,uu____17350) -> true
                             | uu____17375 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____17475 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____17475 with
                                       | (uu____17476,uu____17477,t') ->
                                           let uu____17495 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____17495 with
                                            | (FullMatch ,uu____17506) ->
                                                true
                                            | (HeadMatch
                                               uu____17519,uu____17520) ->
                                                true
                                            | uu____17533 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____17566 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____17566
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____17571 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____17571 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____17659,uu____17660) ->
                                       branches1
                                   | uu____17805 -> branches  in
                                 let uu____17860 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____17869 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____17869 with
                                        | (p,uu____17873,uu____17874) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_25  -> FStar_Util.Inr _0_25)
                                   uu____17860))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17930 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____17930 with
                                | (p,uu____17938,e) ->
                                    ((let uu____17957 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____17957
                                      then
                                        let uu____17958 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____17959 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17958 uu____17959
                                      else ());
                                     (let uu____17961 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _0_26  -> FStar_Util.Inr _0_26)
                                        uu____17961)))))
                 | uu____17974 ->
                     ((let uu____17996 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____17996
                       then
                         let uu____17997 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____17998 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____17997 uu____17998
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____18040 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____18040
            then
              let uu____18041 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____18042 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____18043 = FStar_Syntax_Print.term_to_string t1  in
              let uu____18044 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____18041 uu____18042 uu____18043 uu____18044
            else ());
           (let uu____18046 = head_matches_delta env1 wl1 t1 t2  in
            match uu____18046 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____18077,uu____18078) ->
                     let rec may_relate head3 =
                       let uu____18105 =
                         let uu____18106 = FStar_Syntax_Subst.compress head3
                            in
                         uu____18106.FStar_Syntax_Syntax.n  in
                       match uu____18105 with
                       | FStar_Syntax_Syntax.Tm_name uu____18109 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____18110 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____18134 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____18134 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____18135 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____18136
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____18137 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____18139,uu____18140) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____18182) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____18188) ->
                           may_relate t
                       | uu____18193 -> false  in
                     let uu____18194 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____18194 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____18209 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____18209
                          then
                            let uu____18210 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____18210 with
                             | (guard,wl2) ->
                                 let uu____18217 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____18217)
                          else
                            (let uu____18219 =
                               let uu____18220 =
                                 FStar_Syntax_Print.term_to_string head1  in
                               let uu____18221 =
                                 let uu____18222 =
                                   let uu____18225 =
                                     delta_depth_of_term env1 head1  in
                                   FStar_Util.bind_opt uu____18225
                                     (fun x  ->
                                        let uu____18231 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____18231)
                                    in
                                 FStar_Util.dflt "" uu____18222  in
                               let uu____18232 =
                                 FStar_Syntax_Print.term_to_string head2  in
                               let uu____18233 =
                                 let uu____18234 =
                                   let uu____18237 =
                                     delta_depth_of_term env1 head2  in
                                   FStar_Util.bind_opt uu____18237
                                     (fun x  ->
                                        let uu____18243 =
                                          FStar_Syntax_Print.delta_depth_to_string
                                            x
                                           in
                                        FStar_Pervasives_Native.Some
                                          uu____18243)
                                    in
                                 FStar_Util.dflt "" uu____18234  in
                               FStar_Util.format4
                                 "head mismatch (%s (%s) vs %s (%s))"
                                 uu____18220 uu____18221 uu____18232
                                 uu____18233
                                in
                             giveup env1 uu____18219 orig))
                 | (HeadMatch (true ),uu____18244) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____18257 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____18257 with
                        | (guard,wl2) ->
                            let uu____18264 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____18264)
                     else
                       (let uu____18266 =
                          let uu____18267 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____18268 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____18267 uu____18268
                           in
                        giveup env1 uu____18266 orig)
                 | (uu____18269,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___386_18283 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___386_18283.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___386_18283.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___386_18283.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___386_18283.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___386_18283.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___386_18283.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___386_18283.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___386_18283.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____18307 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____18307
          then
            let uu____18308 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____18308
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____18313 =
                let uu____18316 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18316  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____18313 t1);
             (let uu____18334 =
                let uu____18337 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____18337  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____18334 t2);
             (let uu____18355 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____18355
              then
                let uu____18356 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____18357 =
                  let uu____18358 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____18359 =
                    let uu____18360 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____18360  in
                  Prims.strcat uu____18358 uu____18359  in
                let uu____18361 =
                  let uu____18362 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____18363 =
                    let uu____18364 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____18364  in
                  Prims.strcat uu____18362 uu____18363  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____18356
                  uu____18357 uu____18361
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____18367,uu____18368) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____18391,FStar_Syntax_Syntax.Tm_delayed uu____18392) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____18415,uu____18416) ->
                  let uu____18443 =
                    let uu___387_18444 = problem  in
                    let uu____18445 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___387_18444.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18445;
                      FStar_TypeChecker_Common.relation =
                        (uu___387_18444.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___387_18444.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___387_18444.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___387_18444.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___387_18444.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___387_18444.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___387_18444.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___387_18444.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18443 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____18446,uu____18447) ->
                  let uu____18454 =
                    let uu___388_18455 = problem  in
                    let uu____18456 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___388_18455.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____18456;
                      FStar_TypeChecker_Common.relation =
                        (uu___388_18455.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___388_18455.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___388_18455.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___388_18455.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___388_18455.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___388_18455.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___388_18455.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___388_18455.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18454 wl
              | (uu____18457,FStar_Syntax_Syntax.Tm_ascribed uu____18458) ->
                  let uu____18485 =
                    let uu___389_18486 = problem  in
                    let uu____18487 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___389_18486.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___389_18486.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___389_18486.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18487;
                      FStar_TypeChecker_Common.element =
                        (uu___389_18486.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___389_18486.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___389_18486.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___389_18486.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___389_18486.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___389_18486.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18485 wl
              | (uu____18488,FStar_Syntax_Syntax.Tm_meta uu____18489) ->
                  let uu____18496 =
                    let uu___390_18497 = problem  in
                    let uu____18498 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___390_18497.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___390_18497.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___390_18497.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____18498;
                      FStar_TypeChecker_Common.element =
                        (uu___390_18497.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___390_18497.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___390_18497.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___390_18497.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___390_18497.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___390_18497.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____18496 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____18500),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____18502)) ->
                  let uu____18511 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____18511
              | (FStar_Syntax_Syntax.Tm_bvar uu____18512,uu____18513) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____18514,FStar_Syntax_Syntax.Tm_bvar uu____18515) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___343_18584 =
                    match uu___343_18584 with
                    | [] -> c
                    | bs ->
                        let uu____18612 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____18612
                     in
                  let uu____18623 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____18623 with
                   | ((bs11,c11),(bs21,c21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let c12 =
                                    FStar_Syntax_Subst.subst_comp subst1 c11
                                     in
                                  let c22 =
                                    FStar_Syntax_Subst.subst_comp subst1 c21
                                     in
                                  let rel =
                                    let uu____18772 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____18772
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation
                                     in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs
                 (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                 (bs2,tbody2,lopt2)) ->
                  let mk_t t l uu___344_18857 =
                    match uu___344_18857 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____18899 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____18899 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____19044 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____19045 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____19044
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____19045 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____19046,uu____19047) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____19076 -> true
                    | uu____19095 -> false  in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                          in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3)
                     in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____19148 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___391_19156 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___391_19156.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___391_19156.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___391_19156.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___391_19156.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___391_19156.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___391_19156.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___391_19156.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___391_19156.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___391_19156.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___391_19156.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___391_19156.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___391_19156.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___391_19156.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___391_19156.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___391_19156.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___391_19156.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___391_19156.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___391_19156.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___391_19156.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___391_19156.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___391_19156.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___391_19156.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___391_19156.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___391_19156.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___391_19156.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___391_19156.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___391_19156.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___391_19156.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___391_19156.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___391_19156.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___391_19156.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___391_19156.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___391_19156.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___391_19156.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___391_19156.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___391_19156.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___391_19156.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___391_19156.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___391_19156.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___391_19156.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____19148 with
                       | (uu____19159,ty,uu____19161) ->
                           let uu____19162 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____19162)
                     in
                  let uu____19163 =
                    let uu____19180 = maybe_eta t1  in
                    let uu____19187 = maybe_eta t2  in
                    (uu____19180, uu____19187)  in
                  (match uu____19163 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___392_19229 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___392_19229.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___392_19229.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___392_19229.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___392_19229.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___392_19229.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___392_19229.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___392_19229.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___392_19229.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____19250 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19250
                       then
                         let uu____19251 = destruct_flex_t not_abs wl  in
                         (match uu____19251 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___393_19266 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___393_19266.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___393_19266.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___393_19266.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___393_19266.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___393_19266.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___393_19266.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___393_19266.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___393_19266.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____19288 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19288
                       then
                         let uu____19289 = destruct_flex_t not_abs wl  in
                         (match uu____19289 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___393_19304 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___393_19304.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___393_19304.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___393_19304.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___393_19304.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___393_19304.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___393_19304.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___393_19304.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___393_19304.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19306 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____19323,FStar_Syntax_Syntax.Tm_abs uu____19324) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____19353 -> true
                    | uu____19372 -> false  in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                          in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3)
                     in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____19425 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___391_19433 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___391_19433.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___391_19433.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___391_19433.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___391_19433.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___391_19433.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___391_19433.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___391_19433.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___391_19433.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___391_19433.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___391_19433.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___391_19433.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___391_19433.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___391_19433.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___391_19433.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___391_19433.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___391_19433.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___391_19433.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___391_19433.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___391_19433.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___391_19433.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___391_19433.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___391_19433.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___391_19433.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___391_19433.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___391_19433.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___391_19433.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___391_19433.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___391_19433.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___391_19433.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___391_19433.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___391_19433.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___391_19433.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___391_19433.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___391_19433.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___391_19433.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___391_19433.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___391_19433.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___391_19433.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___391_19433.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___391_19433.FStar_TypeChecker_Env.nbe)
                            }) t
                          in
                       match uu____19425 with
                       | (uu____19436,ty,uu____19438) ->
                           let uu____19439 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____19439)
                     in
                  let uu____19440 =
                    let uu____19457 = maybe_eta t1  in
                    let uu____19464 = maybe_eta t2  in
                    (uu____19457, uu____19464)  in
                  (match uu____19440 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___392_19506 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___392_19506.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___392_19506.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___392_19506.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___392_19506.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___392_19506.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___392_19506.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___392_19506.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___392_19506.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____19527 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19527
                       then
                         let uu____19528 = destruct_flex_t not_abs wl  in
                         (match uu____19528 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___393_19543 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___393_19543.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___393_19543.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___393_19543.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___393_19543.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___393_19543.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___393_19543.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___393_19543.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___393_19543.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____19565 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____19565
                       then
                         let uu____19566 = destruct_flex_t not_abs wl  in
                         (match uu____19566 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___393_19581 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___393_19581.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___393_19581.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___393_19581.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___393_19581.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___393_19581.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___393_19581.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___393_19581.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___393_19581.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____19583 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____19612 =
                    let uu____19617 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____19617 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___394_19645 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___394_19645.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___394_19645.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___395_19647 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___395_19647.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___395_19647.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____19648,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___394_19662 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___394_19662.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___394_19662.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___395_19664 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___395_19664.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___395_19664.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____19665 -> (x1, x2)  in
                  (match uu____19612 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____19684 = as_refinement false env t11  in
                       (match uu____19684 with
                        | (x12,phi11) ->
                            let uu____19691 = as_refinement false env t21  in
                            (match uu____19691 with
                             | (x22,phi21) ->
                                 ((let uu____19699 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____19699
                                   then
                                     ((let uu____19701 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____19702 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19703 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____19701
                                         uu____19702 uu____19703);
                                      (let uu____19704 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____19705 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____19706 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____19704
                                         uu____19705 uu____19706))
                                   else ());
                                  (let uu____19708 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____19708 with
                                   | (base_prob,wl1) ->
                                       let x13 =
                                         FStar_Syntax_Syntax.freshen_bv x12
                                          in
                                       let subst1 =
                                         [FStar_Syntax_Syntax.DB
                                            ((Prims.parse_int "0"), x13)]
                                          in
                                       let phi12 =
                                         FStar_Syntax_Subst.subst subst1
                                           phi11
                                          in
                                       let phi22 =
                                         FStar_Syntax_Subst.subst subst1
                                           phi21
                                          in
                                       let env1 =
                                         FStar_TypeChecker_Env.push_bv env
                                           x13
                                          in
                                       let mk_imp1 imp phi13 phi23 =
                                         let uu____19776 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____19776
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____19788 =
                                         let impl =
                                           if
                                             problem.FStar_TypeChecker_Common.relation
                                               = FStar_TypeChecker_Common.EQ
                                           then
                                             mk_imp1 FStar_Syntax_Util.mk_iff
                                               phi12 phi22
                                           else
                                             mk_imp1 FStar_Syntax_Util.mk_imp
                                               phi12 phi22
                                            in
                                         let guard =
                                           FStar_Syntax_Util.mk_conj
                                             (p_guard base_prob) impl
                                            in
                                         (let uu____19799 =
                                            let uu____19802 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19802
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____19799
                                            (p_guard base_prob));
                                         (let uu____19820 =
                                            let uu____19823 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____19823
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____19820
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____19841 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____19841)
                                          in
                                       let has_uvars =
                                         (let uu____19845 =
                                            let uu____19846 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____19846
                                             in
                                          Prims.op_Negation uu____19845) ||
                                           (let uu____19850 =
                                              let uu____19851 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____19851
                                               in
                                            Prims.op_Negation uu____19850)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____19854 =
                                           let uu____19859 =
                                             let uu____19868 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____19868]  in
                                           mk_t_problem wl1 uu____19859 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____19854 with
                                          | (ref_prob,wl2) ->
                                              let uu____19889 =
                                                solve env1
                                                  (let uu___396_19891 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___396_19891.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___396_19891.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___396_19891.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___396_19891.tcenv);
                                                     wl_implicits =
                                                       (uu___396_19891.wl_implicits)
                                                   })
                                                 in
                                              (match uu____19889 with
                                               | Failed (prob,msg) ->
                                                   if
                                                     ((Prims.op_Negation
                                                         env1.FStar_TypeChecker_Env.uvar_subtyping)
                                                        && has_uvars)
                                                       ||
                                                       (Prims.op_Negation
                                                          wl2.smt_ok)
                                                   then giveup env1 msg prob
                                                   else fallback ()
                                               | Success uu____19901 ->
                                                   let guard =
                                                     let uu____19909 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____19909
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___397_19918 = wl3
                                                        in
                                                     {
                                                       attempting =
                                                         (uu___397_19918.attempting);
                                                       wl_deferred =
                                                         (uu___397_19918.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            (Prims.parse_int "1"));
                                                       defer_ok =
                                                         (uu___397_19918.defer_ok);
                                                       smt_ok =
                                                         (uu___397_19918.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___397_19918.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___397_19918.tcenv);
                                                       wl_implicits =
                                                         (uu___397_19918.wl_implicits)
                                                     }  in
                                                   let uu____19919 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____19919))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____19921,FStar_Syntax_Syntax.Tm_uvar uu____19922) ->
                  let uu____19947 = destruct_flex_t t1 wl  in
                  (match uu____19947 with
                   | (f1,wl1) ->
                       let uu____19954 = destruct_flex_t t2 wl1  in
                       (match uu____19954 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____19961;
                    FStar_Syntax_Syntax.pos = uu____19962;
                    FStar_Syntax_Syntax.vars = uu____19963;_},uu____19964),FStar_Syntax_Syntax.Tm_uvar
                 uu____19965) ->
                  let uu____20014 = destruct_flex_t t1 wl  in
                  (match uu____20014 with
                   | (f1,wl1) ->
                       let uu____20021 = destruct_flex_t t2 wl1  in
                       (match uu____20021 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____20028,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20029;
                    FStar_Syntax_Syntax.pos = uu____20030;
                    FStar_Syntax_Syntax.vars = uu____20031;_},uu____20032))
                  ->
                  let uu____20081 = destruct_flex_t t1 wl  in
                  (match uu____20081 with
                   | (f1,wl1) ->
                       let uu____20088 = destruct_flex_t t2 wl1  in
                       (match uu____20088 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20095;
                    FStar_Syntax_Syntax.pos = uu____20096;
                    FStar_Syntax_Syntax.vars = uu____20097;_},uu____20098),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20099;
                    FStar_Syntax_Syntax.pos = uu____20100;
                    FStar_Syntax_Syntax.vars = uu____20101;_},uu____20102))
                  ->
                  let uu____20175 = destruct_flex_t t1 wl  in
                  (match uu____20175 with
                   | (f1,wl1) ->
                       let uu____20182 = destruct_flex_t t2 wl1  in
                       (match uu____20182 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20189,uu____20190) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____20203 = destruct_flex_t t1 wl  in
                  (match uu____20203 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20210;
                    FStar_Syntax_Syntax.pos = uu____20211;
                    FStar_Syntax_Syntax.vars = uu____20212;_},uu____20213),uu____20214)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____20251 = destruct_flex_t t1 wl  in
                  (match uu____20251 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____20258,FStar_Syntax_Syntax.Tm_uvar uu____20259) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____20272,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20273;
                    FStar_Syntax_Syntax.pos = uu____20274;
                    FStar_Syntax_Syntax.vars = uu____20275;_},uu____20276))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____20313,FStar_Syntax_Syntax.Tm_arrow uu____20314) ->
                  solve_t' env
                    (let uu___398_20342 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___398_20342.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___398_20342.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___398_20342.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___398_20342.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___398_20342.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___398_20342.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___398_20342.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___398_20342.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___398_20342.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20343;
                    FStar_Syntax_Syntax.pos = uu____20344;
                    FStar_Syntax_Syntax.vars = uu____20345;_},uu____20346),FStar_Syntax_Syntax.Tm_arrow
                 uu____20347) ->
                  solve_t' env
                    (let uu___398_20399 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___398_20399.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___398_20399.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___398_20399.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___398_20399.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___398_20399.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___398_20399.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___398_20399.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___398_20399.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___398_20399.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20400,FStar_Syntax_Syntax.Tm_uvar uu____20401) ->
                  let uu____20414 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20414
              | (uu____20415,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20416;
                    FStar_Syntax_Syntax.pos = uu____20417;
                    FStar_Syntax_Syntax.vars = uu____20418;_},uu____20419))
                  ->
                  let uu____20456 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20456
              | (FStar_Syntax_Syntax.Tm_uvar uu____20457,uu____20458) ->
                  let uu____20471 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20471
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20472;
                    FStar_Syntax_Syntax.pos = uu____20473;
                    FStar_Syntax_Syntax.vars = uu____20474;_},uu____20475),uu____20476)
                  ->
                  let uu____20513 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____20513
              | (FStar_Syntax_Syntax.Tm_refine uu____20514,uu____20515) ->
                  let t21 =
                    let uu____20523 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____20523  in
                  solve_t env
                    (let uu___399_20549 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___399_20549.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___399_20549.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___399_20549.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___399_20549.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___399_20549.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___399_20549.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___399_20549.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___399_20549.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___399_20549.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____20550,FStar_Syntax_Syntax.Tm_refine uu____20551) ->
                  let t11 =
                    let uu____20559 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____20559  in
                  solve_t env
                    (let uu___400_20585 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___400_20585.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___400_20585.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___400_20585.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___400_20585.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___400_20585.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___400_20585.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___400_20585.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___400_20585.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___400_20585.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____20667 =
                    let uu____20668 = guard_of_prob env wl problem t1 t2  in
                    match uu____20668 with
                    | (guard,wl1) ->
                        let uu____20675 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____20675
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____20894 = br1  in
                        (match uu____20894 with
                         | (p1,w1,uu____20923) ->
                             let uu____20940 = br2  in
                             (match uu____20940 with
                              | (p2,w2,uu____20963) ->
                                  let uu____20968 =
                                    let uu____20969 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____20969  in
                                  if uu____20968
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____20993 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____20993 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____21030 = br2  in
                                         (match uu____21030 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____21063 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____21063
                                                 in
                                              let uu____21068 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____21099,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____21120) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____21179 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____21179 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____21068
                                                (fun uu____21250  ->
                                                   match uu____21250 with
                                                   | (wprobs,wl2) ->
                                                       let uu____21287 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____21287
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____21307
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____21307
                                                              then
                                                                let uu____21308
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____21309
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____21308
                                                                  uu____21309
                                                              else ());
                                                             (let uu____21311
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____21311
                                                                (fun
                                                                   uu____21347
                                                                    ->
                                                                   match uu____21347
                                                                   with
                                                                   | 
                                                                   (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (((scope,
                                                                    prob) ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____21476 -> FStar_Pervasives_Native.None  in
                  let uu____21517 = solve_branches wl brs1 brs2  in
                  (match uu____21517 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____21565 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____21565 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____21598 =
                                FStar_List.map
                                  (fun uu____21610  ->
                                     match uu____21610 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____21598  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____21619 =
                              let uu____21620 =
                                let uu____21621 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____21621
                                  (let uu___401_21629 = wl3  in
                                   {
                                     attempting = (uu___401_21629.attempting);
                                     wl_deferred =
                                       (uu___401_21629.wl_deferred);
                                     ctr = (uu___401_21629.ctr);
                                     defer_ok = (uu___401_21629.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___401_21629.umax_heuristic_ok);
                                     tcenv = (uu___401_21629.tcenv);
                                     wl_implicits =
                                       (uu___401_21629.wl_implicits)
                                   })
                                 in
                              solve env uu____21620  in
                            (match uu____21619 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____21633 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____21639,uu____21640) ->
                  let head1 =
                    let uu____21664 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21664
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21710 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21710
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21756 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21756
                    then
                      let uu____21757 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21758 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21759 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21757 uu____21758 uu____21759
                    else ());
                   (let no_free_uvars t =
                      (let uu____21769 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21769) &&
                        (let uu____21773 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21773)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____21789 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21789 = FStar_Syntax_Util.Equal  in
                    let uu____21790 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21790
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____21791 = equal t1 t2  in
                         (if uu____21791
                          then
                            let uu____21792 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____21792
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____21795 =
                            let uu____21802 = equal t1 t2  in
                            if uu____21802
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____21812 = mk_eq2 wl orig t1 t2  in
                               match uu____21812 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____21795 with
                          | (guard,wl1) ->
                              let uu____21833 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____21833))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____21835,uu____21836) ->
                  let head1 =
                    let uu____21844 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____21844
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____21890 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____21890
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____21936 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____21936
                    then
                      let uu____21937 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____21938 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____21939 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____21937 uu____21938 uu____21939
                    else ());
                   (let no_free_uvars t =
                      (let uu____21949 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____21949) &&
                        (let uu____21953 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____21953)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____21969 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____21969 = FStar_Syntax_Util.Equal  in
                    let uu____21970 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____21970
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____21971 = equal t1 t2  in
                         (if uu____21971
                          then
                            let uu____21972 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____21972
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____21975 =
                            let uu____21982 = equal t1 t2  in
                            if uu____21982
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____21992 = mk_eq2 wl orig t1 t2  in
                               match uu____21992 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____21975 with
                          | (guard,wl1) ->
                              let uu____22013 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____22013))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____22015,uu____22016) ->
                  let head1 =
                    let uu____22018 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22018
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22064 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22064
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22110 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22110
                    then
                      let uu____22111 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22112 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22113 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22111 uu____22112 uu____22113
                    else ());
                   (let no_free_uvars t =
                      (let uu____22123 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22123) &&
                        (let uu____22127 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22127)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____22143 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22143 = FStar_Syntax_Util.Equal  in
                    let uu____22144 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22144
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22145 = equal t1 t2  in
                         (if uu____22145
                          then
                            let uu____22146 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____22146
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22149 =
                            let uu____22156 = equal t1 t2  in
                            if uu____22156
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22166 = mk_eq2 wl orig t1 t2  in
                               match uu____22166 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____22149 with
                          | (guard,wl1) ->
                              let uu____22187 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____22187))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____22189,uu____22190) ->
                  let head1 =
                    let uu____22192 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22192
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22238 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22238
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22284 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22284
                    then
                      let uu____22285 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22286 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22287 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22285 uu____22286 uu____22287
                    else ());
                   (let no_free_uvars t =
                      (let uu____22297 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22297) &&
                        (let uu____22301 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22301)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____22317 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22317 = FStar_Syntax_Util.Equal  in
                    let uu____22318 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22318
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22319 = equal t1 t2  in
                         (if uu____22319
                          then
                            let uu____22320 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____22320
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22323 =
                            let uu____22330 = equal t1 t2  in
                            if uu____22330
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22340 = mk_eq2 wl orig t1 t2  in
                               match uu____22340 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____22323 with
                          | (guard,wl1) ->
                              let uu____22361 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____22361))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____22363,uu____22364) ->
                  let head1 =
                    let uu____22366 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22366
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22412 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22412
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22458 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22458
                    then
                      let uu____22459 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22460 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22461 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22459 uu____22460 uu____22461
                    else ());
                   (let no_free_uvars t =
                      (let uu____22471 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22471) &&
                        (let uu____22475 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22475)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____22491 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22491 = FStar_Syntax_Util.Equal  in
                    let uu____22492 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22492
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22493 = equal t1 t2  in
                         (if uu____22493
                          then
                            let uu____22494 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____22494
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22497 =
                            let uu____22504 = equal t1 t2  in
                            if uu____22504
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22514 = mk_eq2 wl orig t1 t2  in
                               match uu____22514 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____22497 with
                          | (guard,wl1) ->
                              let uu____22535 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____22535))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____22537,uu____22538) ->
                  let head1 =
                    let uu____22556 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22556
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22602 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22602
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22648 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22648
                    then
                      let uu____22649 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22650 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22651 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22649 uu____22650 uu____22651
                    else ());
                   (let no_free_uvars t =
                      (let uu____22661 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22661) &&
                        (let uu____22665 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22665)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____22681 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22681 = FStar_Syntax_Util.Equal  in
                    let uu____22682 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22682
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22683 = equal t1 t2  in
                         (if uu____22683
                          then
                            let uu____22684 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____22684
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22687 =
                            let uu____22694 = equal t1 t2  in
                            if uu____22694
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22704 = mk_eq2 wl orig t1 t2  in
                               match uu____22704 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____22687 with
                          | (guard,wl1) ->
                              let uu____22725 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____22725))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____22727,FStar_Syntax_Syntax.Tm_match uu____22728) ->
                  let head1 =
                    let uu____22752 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22752
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22798 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22798
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____22844 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____22844
                    then
                      let uu____22845 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____22846 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____22847 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22845 uu____22846 uu____22847
                    else ());
                   (let no_free_uvars t =
                      (let uu____22857 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____22857) &&
                        (let uu____22861 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____22861)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____22877 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____22877 = FStar_Syntax_Util.Equal  in
                    let uu____22878 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____22878
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22879 = equal t1 t2  in
                         (if uu____22879
                          then
                            let uu____22880 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____22880
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22883 =
                            let uu____22890 = equal t1 t2  in
                            if uu____22890
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22900 = mk_eq2 wl orig t1 t2  in
                               match uu____22900 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____22883 with
                          | (guard,wl1) ->
                              let uu____22921 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____22921))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____22923,FStar_Syntax_Syntax.Tm_uinst uu____22924) ->
                  let head1 =
                    let uu____22932 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____22932
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____22972 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____22972
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23012 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23012
                    then
                      let uu____23013 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23014 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23015 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23013 uu____23014 uu____23015
                    else ());
                   (let no_free_uvars t =
                      (let uu____23025 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23025) &&
                        (let uu____23029 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23029)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____23045 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23045 = FStar_Syntax_Util.Equal  in
                    let uu____23046 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23046
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23047 = equal t1 t2  in
                         (if uu____23047
                          then
                            let uu____23048 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23048
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23051 =
                            let uu____23058 = equal t1 t2  in
                            if uu____23058
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23068 = mk_eq2 wl orig t1 t2  in
                               match uu____23068 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23051 with
                          | (guard,wl1) ->
                              let uu____23089 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23089))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23091,FStar_Syntax_Syntax.Tm_name uu____23092) ->
                  let head1 =
                    let uu____23094 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23094
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23134 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23134
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23174 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23174
                    then
                      let uu____23175 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23176 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23177 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23175 uu____23176 uu____23177
                    else ());
                   (let no_free_uvars t =
                      (let uu____23187 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23187) &&
                        (let uu____23191 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23191)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____23207 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23207 = FStar_Syntax_Util.Equal  in
                    let uu____23208 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23208
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23209 = equal t1 t2  in
                         (if uu____23209
                          then
                            let uu____23210 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23210
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23213 =
                            let uu____23220 = equal t1 t2  in
                            if uu____23220
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23230 = mk_eq2 wl orig t1 t2  in
                               match uu____23230 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23213 with
                          | (guard,wl1) ->
                              let uu____23251 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23251))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23253,FStar_Syntax_Syntax.Tm_constant uu____23254) ->
                  let head1 =
                    let uu____23256 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23256
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23296 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23296
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23336 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23336
                    then
                      let uu____23337 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23338 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23339 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23337 uu____23338 uu____23339
                    else ());
                   (let no_free_uvars t =
                      (let uu____23349 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23349) &&
                        (let uu____23353 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23353)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____23369 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23369 = FStar_Syntax_Util.Equal  in
                    let uu____23370 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23370
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23371 = equal t1 t2  in
                         (if uu____23371
                          then
                            let uu____23372 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23372
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23375 =
                            let uu____23382 = equal t1 t2  in
                            if uu____23382
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23392 = mk_eq2 wl orig t1 t2  in
                               match uu____23392 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23375 with
                          | (guard,wl1) ->
                              let uu____23413 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23413))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23415,FStar_Syntax_Syntax.Tm_fvar uu____23416) ->
                  let head1 =
                    let uu____23418 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23418
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23458 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23458
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23498 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23498
                    then
                      let uu____23499 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23500 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23501 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23499 uu____23500 uu____23501
                    else ());
                   (let no_free_uvars t =
                      (let uu____23511 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23511) &&
                        (let uu____23515 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23515)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____23531 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23531 = FStar_Syntax_Util.Equal  in
                    let uu____23532 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23532
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23533 = equal t1 t2  in
                         (if uu____23533
                          then
                            let uu____23534 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23534
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23537 =
                            let uu____23544 = equal t1 t2  in
                            if uu____23544
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23554 = mk_eq2 wl orig t1 t2  in
                               match uu____23554 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23537 with
                          | (guard,wl1) ->
                              let uu____23575 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23575))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23577,FStar_Syntax_Syntax.Tm_app uu____23578) ->
                  let head1 =
                    let uu____23596 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23596
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23636 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23636
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____23676 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____23676
                    then
                      let uu____23677 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____23678 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____23679 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23677 uu____23678 uu____23679
                    else ());
                   (let no_free_uvars t =
                      (let uu____23689 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____23689) &&
                        (let uu____23693 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____23693)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____23709 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____23709 = FStar_Syntax_Util.Equal  in
                    let uu____23710 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____23710
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23711 = equal t1 t2  in
                         (if uu____23711
                          then
                            let uu____23712 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____23712
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23715 =
                            let uu____23722 = equal t1 t2  in
                            if uu____23722
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23732 = mk_eq2 wl orig t1 t2  in
                               match uu____23732 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____23715 with
                          | (guard,wl1) ->
                              let uu____23753 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____23753))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____23755,FStar_Syntax_Syntax.Tm_let uu____23756) ->
                  let uu____23781 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____23781
                  then
                    let uu____23782 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____23782
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____23784,uu____23785) ->
                  let uu____23798 =
                    let uu____23803 =
                      let uu____23804 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23805 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23806 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23807 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23804 uu____23805 uu____23806 uu____23807
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23803)
                     in
                  FStar_Errors.raise_error uu____23798
                    t1.FStar_Syntax_Syntax.pos
              | (uu____23808,FStar_Syntax_Syntax.Tm_let uu____23809) ->
                  let uu____23822 =
                    let uu____23827 =
                      let uu____23828 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____23829 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____23830 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____23831 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____23828 uu____23829 uu____23830 uu____23831
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____23827)
                     in
                  FStar_Errors.raise_error uu____23822
                    t1.FStar_Syntax_Syntax.pos
              | uu____23832 -> giveup env "head tag mismatch" orig))))

and (solve_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem ->
      worklist -> solution)
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs  in
        let c2 = problem.FStar_TypeChecker_Common.rhs  in
        let orig = FStar_TypeChecker_Common.CProb problem  in
        let sub_prob wl1 t1 rel t2 reason =
          mk_t_problem wl1 [] orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____23893 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____23893
           then
             let uu____23894 =
               let uu____23895 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____23895  in
             let uu____23896 =
               let uu____23897 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____23897  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____23894 uu____23896
           else ());
          (let uu____23899 =
             let uu____23900 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____23900  in
           if uu____23899
           then
             let uu____23901 =
               let uu____23902 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____23903 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____23902 uu____23903
                in
             giveup env uu____23901 orig
           else
             (let uu____23905 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____23905 with
              | (ret_sub_prob,wl1) ->
                  let uu____23912 =
                    FStar_List.fold_right2
                      (fun uu____23949  ->
                         fun uu____23950  ->
                           fun uu____23951  ->
                             match (uu____23949, uu____23950, uu____23951)
                             with
                             | ((a1,uu____23995),(a2,uu____23997),(arg_sub_probs,wl2))
                                 ->
                                 let uu____24030 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____24030 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____23912 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____24059 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____24059  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       let uu____24067 = attempt sub_probs wl3  in
                       solve env uu____24067)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____24090 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____24093)::[] -> wp1
              | uu____24118 ->
                  let uu____24129 =
                    let uu____24130 =
                      let uu____24131 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____24131  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____24130
                     in
                  failwith uu____24129
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____24137 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____24137]
              | x -> x  in
            let uu____24139 =
              let uu____24150 =
                let uu____24159 =
                  let uu____24160 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____24160 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____24159  in
              [uu____24150]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____24139;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____24177 = lift_c1 ()  in solve_eq uu____24177 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___345_24183  ->
                       match uu___345_24183 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____24184 -> false))
                in
             let uu____24185 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____24215)::uu____24216,(wp2,uu____24218)::uu____24219)
                   -> (wp1, wp2)
               | uu____24292 ->
                   let uu____24317 =
                     let uu____24322 =
                       let uu____24323 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____24324 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____24323 uu____24324
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____24322)
                      in
                   FStar_Errors.raise_error uu____24317
                     env.FStar_TypeChecker_Env.range
                in
             match uu____24185 with
             | (wpc1,wpc2) ->
                 let uu____24331 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____24331
                 then
                   let uu____24334 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____24334 wl
                 else
                   (let uu____24336 =
                      let uu____24343 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____24343  in
                    match uu____24336 with
                    | (c2_decl,qualifiers) ->
                        let uu____24364 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____24364
                        then
                          let c1_repr =
                            let uu____24368 =
                              let uu____24369 =
                                let uu____24370 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____24370  in
                              let uu____24371 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____24369 uu____24371
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____24368
                             in
                          let c2_repr =
                            let uu____24373 =
                              let uu____24374 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____24375 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____24374 uu____24375
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____24373
                             in
                          let uu____24376 =
                            let uu____24381 =
                              let uu____24382 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____24383 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____24382 uu____24383
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____24381
                             in
                          (match uu____24376 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____24387 = attempt [prob] wl2  in
                               solve env uu____24387)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____24398 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____24398
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____24401 =
                                     let uu____24408 =
                                       let uu____24409 =
                                         let uu____24426 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____24429 =
                                           let uu____24440 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____24449 =
                                             let uu____24460 =
                                               let uu____24469 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____24469
                                                in
                                             [uu____24460]  in
                                           uu____24440 :: uu____24449  in
                                         (uu____24426, uu____24429)  in
                                       FStar_Syntax_Syntax.Tm_app uu____24409
                                        in
                                     FStar_Syntax_Syntax.mk uu____24408  in
                                   uu____24401 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____24520 =
                                    let uu____24527 =
                                      let uu____24528 =
                                        let uu____24545 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____24548 =
                                          let uu____24559 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____24568 =
                                            let uu____24579 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____24588 =
                                              let uu____24599 =
                                                let uu____24608 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____24608
                                                 in
                                              [uu____24599]  in
                                            uu____24579 :: uu____24588  in
                                          uu____24559 :: uu____24568  in
                                        (uu____24545, uu____24548)  in
                                      FStar_Syntax_Syntax.Tm_app uu____24528
                                       in
                                    FStar_Syntax_Syntax.mk uu____24527  in
                                  uu____24520 FStar_Pervasives_Native.None r)
                              in
                           (let uu____24665 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24665
                            then
                              let uu____24666 =
                                let uu____24667 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____24667
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____24666
                            else ());
                           (let uu____24669 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____24669 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____24677 =
                                    let uu____24680 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_27  ->
                                         FStar_Pervasives_Native.Some _0_27)
                                      uu____24680
                                     in
                                  solve_prob orig uu____24677 [] wl1  in
                                let uu____24683 = attempt [base_prob] wl2  in
                                solve env uu____24683))))
           in
        let uu____24684 = FStar_Util.physical_equality c1 c2  in
        if uu____24684
        then
          let uu____24685 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____24685
        else
          ((let uu____24688 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____24688
            then
              let uu____24689 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____24690 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____24689
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____24690
            else ());
           (let uu____24692 =
              let uu____24701 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____24704 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____24701, uu____24704)  in
            match uu____24692 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24722),FStar_Syntax_Syntax.Total
                    (t2,uu____24724)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____24741 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24741 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24742,FStar_Syntax_Syntax.Total uu____24743) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24761),FStar_Syntax_Syntax.Total
                    (t2,uu____24763)) ->
                     let uu____24780 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24780 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____24782),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24784)) ->
                     let uu____24801 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24801 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____24803),FStar_Syntax_Syntax.GTotal
                    (t2,uu____24805)) ->
                     let uu____24822 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____24822 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____24823,FStar_Syntax_Syntax.Comp uu____24824) ->
                     let uu____24833 =
                       let uu___402_24836 = problem  in
                       let uu____24839 =
                         let uu____24840 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24840
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___402_24836.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24839;
                         FStar_TypeChecker_Common.relation =
                           (uu___402_24836.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___402_24836.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___402_24836.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___402_24836.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___402_24836.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___402_24836.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___402_24836.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___402_24836.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24833 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____24841,FStar_Syntax_Syntax.Comp uu____24842) ->
                     let uu____24851 =
                       let uu___402_24854 = problem  in
                       let uu____24857 =
                         let uu____24858 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24858
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___402_24854.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____24857;
                         FStar_TypeChecker_Common.relation =
                           (uu___402_24854.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___402_24854.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___402_24854.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___402_24854.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___402_24854.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___402_24854.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___402_24854.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___402_24854.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24851 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24859,FStar_Syntax_Syntax.GTotal uu____24860) ->
                     let uu____24869 =
                       let uu___403_24872 = problem  in
                       let uu____24875 =
                         let uu____24876 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24876
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___403_24872.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___403_24872.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___403_24872.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24875;
                         FStar_TypeChecker_Common.element =
                           (uu___403_24872.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___403_24872.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___403_24872.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___403_24872.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___403_24872.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___403_24872.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24869 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24877,FStar_Syntax_Syntax.Total uu____24878) ->
                     let uu____24887 =
                       let uu___403_24890 = problem  in
                       let uu____24893 =
                         let uu____24894 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____24894
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___403_24890.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___403_24890.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___403_24890.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____24893;
                         FStar_TypeChecker_Common.element =
                           (uu___403_24890.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___403_24890.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___403_24890.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___403_24890.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___403_24890.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___403_24890.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____24887 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____24895,FStar_Syntax_Syntax.Comp uu____24896) ->
                     let uu____24897 =
                       (((FStar_Syntax_Util.is_ml_comp c11) &&
                           (FStar_Syntax_Util.is_ml_comp c21))
                          ||
                          ((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_total_comp c21)))
                         ||
                         (((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_ml_comp c21))
                            &&
                            (problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB))
                        in
                     if uu____24897
                     then
                       let uu____24898 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____24898 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____24902 =
                            let uu____24907 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____24907
                            then (c1_comp, c2_comp)
                            else
                              (let uu____24913 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____24914 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____24913, uu____24914))
                             in
                          match uu____24902 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____24921 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____24921
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____24923 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____24923 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____24926 =
                                  let uu____24927 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____24928 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____24927 uu____24928
                                   in
                                giveup env uu____24926 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____24935 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____24935 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____24976 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____24976 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____24994 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____25022  ->
                match uu____25022 with
                | (u1,u2) ->
                    let uu____25029 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____25030 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____25029 uu____25030))
         in
      FStar_All.pipe_right uu____24994 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let (guard_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____25057,[])) when
          let uu____25082 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____25082 -> "{}"
      | uu____25083 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____25106 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____25106
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____25109 =
              FStar_List.map
                (fun uu____25119  ->
                   match uu____25119 with
                   | (uu____25124,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____25109 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____25129 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____25129 imps
  
let (new_t_problem :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_TypeChecker_Common.prob,worklist)
                  FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun env  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun loc  ->
                let reason =
                  let uu____25182 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____25182
                  then
                    let uu____25183 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____25184 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____25183
                      (rel_to_string rel) uu____25184
                  else "TOP"  in
                let uu____25186 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____25186 with
                | (p,wl1) ->
                    (def_check_prob (Prims.strcat "new_t_problem." reason)
                       (FStar_TypeChecker_Common.TProb p);
                     ((FStar_TypeChecker_Common.TProb p), wl1))
  
let (new_t_prob :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            (FStar_TypeChecker_Common.prob,FStar_Syntax_Syntax.bv,worklist)
              FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    fun env  ->
      fun t1  ->
        fun rel  ->
          fun t2  ->
            let x =
              let uu____25244 =
                let uu____25247 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)
                  uu____25247
                 in
              FStar_Syntax_Syntax.new_bv uu____25244 t1  in
            let uu____25250 =
              let uu____25255 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____25255
               in
            match uu____25250 with | (p,wl1) -> (p, x, wl1)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob,Prims.string)
         FStar_Pervasives_Native.tuple2 ->
         (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
           FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____25328 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____25328
              then
                let uu____25329 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____25329
              else ());
             (let result = err (d, s)  in
              FStar_Syntax_Unionfind.rollback tx; result))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____25351 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____25351
            then
              let uu____25352 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____25352
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____25356 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____25356
             then
               let uu____25357 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____25357
             else ());
            (let f2 =
               let uu____25360 =
                 let uu____25361 = FStar_Syntax_Util.unmeta f1  in
                 uu____25361.FStar_Syntax_Syntax.n  in
               match uu____25360 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____25365 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___404_25366 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___404_25366.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___404_25366.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___404_25366.FStar_TypeChecker_Env.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicit
                                           Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____25420 =
              let uu____25421 =
                let uu____25422 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_29  -> FStar_TypeChecker_Common.NonTrivial _0_29)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____25422;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____25421  in
            FStar_All.pipe_left
              (fun _0_30  -> FStar_Pervasives_Native.Some _0_30) uu____25420
  
let with_guard_no_simp :
  'Auu____25437 .
    'Auu____25437 ->
      FStar_TypeChecker_Common.prob ->
        FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____25460 =
              let uu____25461 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____25461;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____25460
  
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____25491 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____25491
           then
             let uu____25492 = FStar_Syntax_Print.term_to_string t1  in
             let uu____25493 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____25492
               uu____25493
           else ());
          (let uu____25495 =
             let uu____25500 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____25500
              in
           match uu____25495 with
           | (prob,wl) ->
               let g =
                 let uu____25508 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____25518  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____25508  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____25552 = try_teq true env t1 t2  in
        match uu____25552 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____25556 = FStar_TypeChecker_Env.get_range env  in
              let uu____25557 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____25556 uu____25557);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____25564 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____25564
              then
                let uu____25565 = FStar_Syntax_Print.term_to_string t1  in
                let uu____25566 = FStar_Syntax_Print.term_to_string t2  in
                let uu____25567 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____25565
                  uu____25566 uu____25567
              else ());
             g)
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____25589 = FStar_TypeChecker_Env.get_range env  in
          let uu____25590 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____25589 uu____25590
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let rel =
          if env.FStar_TypeChecker_Env.use_eq
          then FStar_TypeChecker_Common.EQ
          else FStar_TypeChecker_Common.SUB  in
        (let uu____25615 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____25615
         then
           let uu____25616 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____25617 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____25616 uu____25617
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____25620 =
           let uu____25627 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____25627 "sub_comp"
            in
         match uu____25620 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____25638 =
                 solve_and_commit env (singleton wl prob1 true)
                   (fun uu____25648  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob1) uu____25638)))
  
let (solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                                 FStar_Syntax_Syntax.universe)
                                                 FStar_Pervasives_Native.tuple2
                                                 Prims.list)
        FStar_Pervasives_Native.tuple2 -> unit)
  =
  fun tx  ->
    fun env  ->
      fun uu____25693  ->
        match uu____25693 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____25736 =
                 let uu____25741 =
                   let uu____25742 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____25743 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____25742 uu____25743
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____25741)  in
               let uu____25744 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____25736 uu____25744)
               in
            let equiv1 v1 v' =
              let uu____25756 =
                let uu____25761 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____25762 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____25761, uu____25762)  in
              match uu____25756 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____25781 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____25811 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____25811 with
                      | FStar_Syntax_Syntax.U_unif uu____25818 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____25847  ->
                                    match uu____25847 with
                                    | (u,v') ->
                                        let uu____25856 = equiv1 v1 v'  in
                                        if uu____25856
                                        then
                                          let uu____25859 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____25859 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____25875 -> []))
               in
            let uu____25880 =
              let wl =
                let uu___405_25884 = empty_worklist env  in
                {
                  attempting = (uu___405_25884.attempting);
                  wl_deferred = (uu___405_25884.wl_deferred);
                  ctr = (uu___405_25884.ctr);
                  defer_ok = false;
                  smt_ok = (uu___405_25884.smt_ok);
                  umax_heuristic_ok = (uu___405_25884.umax_heuristic_ok);
                  tcenv = (uu___405_25884.tcenv);
                  wl_implicits = (uu___405_25884.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____25902  ->
                      match uu____25902 with
                      | (lb,v1) ->
                          let uu____25909 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____25909 with
                           | USolved wl1 -> ()
                           | uu____25911 -> fail1 lb v1)))
               in
            let rec check_ineq uu____25921 =
              match uu____25921 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____25930) -> true
                   | (FStar_Syntax_Syntax.U_succ
                      u0,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name
                      u0,FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif
                      u0,FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name
                      uu____25953,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____25955,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____25966) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____25973,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____25981 -> false)
               in
            let uu____25986 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____26001  ->
                      match uu____26001 with
                      | (u,v1) ->
                          let uu____26008 = check_ineq (u, v1)  in
                          if uu____26008
                          then true
                          else
                            ((let uu____26011 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____26011
                              then
                                let uu____26012 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____26013 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____26012
                                  uu____26013
                              else ());
                             false)))
               in
            if uu____25986
            then ()
            else
              ((let uu____26017 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____26017
                then
                  ((let uu____26019 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____26019);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____26029 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____26029))
                else ());
               (let uu____26039 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____26039))
  
let (solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                               FStar_Syntax_Syntax.universe)
                                               FStar_Pervasives_Native.tuple2
                                               Prims.list)
      FStar_Pervasives_Native.tuple2 -> unit)
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Syntax_Unionfind.new_transaction ()  in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
  
let (try_solve_deferred_constraints :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun defer_ok  ->
    fun env  ->
      fun g  ->
        let fail1 uu____26106 =
          match uu____26106 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___406_26127 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___406_26127.attempting);
            wl_deferred = (uu___406_26127.wl_deferred);
            ctr = (uu___406_26127.ctr);
            defer_ok;
            smt_ok = (uu___406_26127.smt_ok);
            umax_heuristic_ok = (uu___406_26127.umax_heuristic_ok);
            tcenv = (uu___406_26127.tcenv);
            wl_implicits = (uu___406_26127.wl_implicits)
          }  in
        (let uu____26129 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26129
         then
           let uu____26130 = FStar_Util.string_of_bool defer_ok  in
           let uu____26131 = wl_to_string wl  in
           let uu____26132 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____26130 uu____26131 uu____26132
         else ());
        (let g1 =
           let uu____26135 = solve_and_commit env wl fail1  in
           match uu____26135 with
           | FStar_Pervasives_Native.Some
               (uu____26142::uu____26143,uu____26144) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___407_26169 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___407_26169.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___407_26169.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____26170 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___408_26178 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___408_26178.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___408_26178.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___408_26178.FStar_TypeChecker_Env.implicits)
          }))
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints false env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true env g 
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____26226 = FStar_ST.op_Bang last_proof_ns  in
    match uu____26226 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals last_proof_ns
          (FStar_Pervasives_Native.Some pns)
    | FStar_Pervasives_Native.Some old ->
        if old = pns
        then ()
        else
          ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           FStar_ST.op_Colon_Equals last_proof_ns
             (FStar_Pervasives_Native.Some pns))
  
let (discharge_guard' :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let debug1 =
            ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel"))
               ||
               (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "SMTQuery")))
              ||
              (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Tac"))
             in
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___409_26337 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___409_26337.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___409_26337.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___409_26337.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____26338 =
            let uu____26339 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____26339  in
          if uu____26338
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____26347 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____26348 =
                       let uu____26349 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____26349
                        in
                     FStar_Errors.diag uu____26347 uu____26348)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____26353 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____26354 =
                        let uu____26355 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____26355
                         in
                      FStar_Errors.diag uu____26353 uu____26354)
                   else ();
                   (let uu____26358 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____26358
                      "discharge_guard'" env vc1);
                   (let uu____26359 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____26359 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____26366 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____26367 =
                                let uu____26368 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____26368
                                 in
                              FStar_Errors.diag uu____26366 uu____26367)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____26373 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____26374 =
                                let uu____26375 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____26375
                                 in
                              FStar_Errors.diag uu____26373 uu____26374)
                           else ();
                           (let vcs =
                              let uu____26386 = FStar_Options.use_tactics ()
                                 in
                              if uu____26386
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____26406  ->
                                     (let uu____26408 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a229  -> ())
                                        uu____26408);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____26451  ->
                                              match uu____26451 with
                                              | (env1,goal,opts) ->
                                                  let uu____26467 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____26467, opts)))))
                              else
                                (let uu____26469 =
                                   let uu____26476 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____26476)  in
                                 [uu____26469])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____26509  ->
                                    match uu____26509 with
                                    | (env1,goal,opts) ->
                                        let uu____26519 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____26519 with
                                         | FStar_TypeChecker_Common.Trivial 
                                             ->
                                             if debug1
                                             then
                                               FStar_Util.print_string
                                                 "Goal completely solved by tactic\n"
                                             else ()
                                         | FStar_TypeChecker_Common.NonTrivial
                                             goal1 ->
                                             (FStar_Options.push ();
                                              FStar_Options.set opts;
                                              maybe_update_proof_ns env1;
                                              if debug1
                                              then
                                                (let uu____26527 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____26528 =
                                                   let uu____26529 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____26530 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____26529 uu____26530
                                                    in
                                                 FStar_Errors.diag
                                                   uu____26527 uu____26528)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____26533 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____26534 =
                                                   let uu____26535 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____26535
                                                    in
                                                 FStar_Errors.diag
                                                   uu____26533 uu____26534)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal1;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____26549 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____26549 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____26556 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____26556
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____26567 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____26567 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26593 = try_teq false env t1 t2  in
        match uu____26593 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
  
let (resolve_implicits' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun must_total  ->
      fun forcelax  ->
        fun g  ->
          let unresolved ctx_u =
            let uu____26628 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____26628 with
            | FStar_Pervasives_Native.Some uu____26631 -> false
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____26651 = acc  in
            match uu____26651 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____26663 = hd1  in
                     (match uu____26663 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;
                          FStar_TypeChecker_Env.imp_meta = uu____26668;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____26676 = unresolved ctx_u  in
                             if uu____26676
                             then
                               match hd1.FStar_TypeChecker_Env.imp_meta with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env1,tau) ->
                                   let t =
                                     env1.FStar_TypeChecker_Env.synth_hook
                                       env1
                                       (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                       tau
                                      in
                                   let extra =
                                     let uu____26691 = teq_nosmt env1 t tm
                                        in
                                     match uu____26691 with
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "resolve_implicits: unifying with an unresolved uvar failed?"
                                     | FStar_Pervasives_Native.Some g1 ->
                                         g1.FStar_TypeChecker_Env.implicits
                                      in
                                   let hd2 =
                                     let uu___410_26700 = hd1  in
                                     {
                                       FStar_TypeChecker_Env.imp_reason =
                                         (uu___410_26700.FStar_TypeChecker_Env.imp_reason);
                                       FStar_TypeChecker_Env.imp_uvar =
                                         (uu___410_26700.FStar_TypeChecker_Env.imp_uvar);
                                       FStar_TypeChecker_Env.imp_tm =
                                         (uu___410_26700.FStar_TypeChecker_Env.imp_tm);
                                       FStar_TypeChecker_Env.imp_range =
                                         (uu___410_26700.FStar_TypeChecker_Env.imp_range);
                                       FStar_TypeChecker_Env.imp_meta =
                                         FStar_Pervasives_Native.None
                                     }  in
                                   until_fixpoint (out, changed) (hd2 ::
                                     (FStar_List.append extra tl1))
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___411_26708 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___411_26708.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___411_26708.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___411_26708.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___411_26708.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___411_26708.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___411_26708.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___411_26708.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___411_26708.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___411_26708.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___411_26708.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___411_26708.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___411_26708.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___411_26708.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___411_26708.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___411_26708.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___411_26708.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___411_26708.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___411_26708.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___411_26708.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___411_26708.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___411_26708.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___411_26708.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___411_26708.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___411_26708.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___411_26708.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___411_26708.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___411_26708.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___411_26708.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___411_26708.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___411_26708.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___411_26708.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___411_26708.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___411_26708.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___411_26708.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___411_26708.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___411_26708.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___411_26708.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___411_26708.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___411_26708.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___411_26708.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___411_26708.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___411_26708.FStar_TypeChecker_Env.nbe)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___412_26711 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___412_26711.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___412_26711.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___412_26711.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___412_26711.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___412_26711.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___412_26711.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___412_26711.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___412_26711.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___412_26711.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___412_26711.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.is_pattern =
                                          (uu___412_26711.FStar_TypeChecker_Env.is_pattern);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___412_26711.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___412_26711.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___412_26711.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___412_26711.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___412_26711.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___412_26711.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___412_26711.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___412_26711.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___412_26711.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___412_26711.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___412_26711.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___412_26711.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___412_26711.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___412_26711.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___412_26711.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___412_26711.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___412_26711.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___412_26711.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___412_26711.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___412_26711.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___412_26711.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___412_26711.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___412_26711.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___412_26711.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___412_26711.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___412_26711.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___412_26711.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___412_26711.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___412_26711.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___412_26711.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___412_26711.FStar_TypeChecker_Env.nbe)
                                      }
                                    else env1  in
                                  (let uu____26714 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____26714
                                   then
                                     let uu____26715 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____26716 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____26717 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____26718 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____26715 uu____26716 uu____26717
                                       reason uu____26718
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___414_26722  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____26729 =
                                             let uu____26738 =
                                               let uu____26745 =
                                                 let uu____26746 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____26747 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____26748 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____26746 uu____26747
                                                   uu____26748
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____26745, r)
                                                in
                                             [uu____26738]  in
                                           FStar_Errors.add_errors
                                             uu____26729);
                                          FStar_Exn.raise e)
                                      in
                                   let g2 =
                                     if env2.FStar_TypeChecker_Env.is_pattern
                                     then
                                       let uu___415_26762 = g1  in
                                       {
                                         FStar_TypeChecker_Env.guard_f =
                                           FStar_TypeChecker_Common.Trivial;
                                         FStar_TypeChecker_Env.deferred =
                                           (uu___415_26762.FStar_TypeChecker_Env.deferred);
                                         FStar_TypeChecker_Env.univ_ineqs =
                                           (uu___415_26762.FStar_TypeChecker_Env.univ_ineqs);
                                         FStar_TypeChecker_Env.implicits =
                                           (uu___415_26762.FStar_TypeChecker_Env.implicits)
                                       }
                                     else g1  in
                                   let g' =
                                     let uu____26765 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____26775  ->
                                               let uu____26776 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____26777 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____26778 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____26776 uu____26777
                                                 reason uu____26778)) env2 g2
                                         true
                                        in
                                     match uu____26765 with
                                     | FStar_Pervasives_Native.Some g3 -> g3
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Env.implicits
                                         out), true) tl1)))))
             in
          let uu___416_26780 = g  in
          let uu____26781 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___416_26780.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___416_26780.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___416_26780.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____26781
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env true false g 
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____26815 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____26815 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____26816 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a230  -> ()) uu____26816
      | imp::uu____26818 ->
          let uu____26821 =
            let uu____26826 =
              let uu____26827 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____26828 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____26827 uu____26828 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____26826)
             in
          FStar_Errors.raise_error uu____26821
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26844 = teq_nosmt env t1 t2  in
        match uu____26844 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___417_26859 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___417_26859.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___417_26859.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___417_26859.FStar_TypeChecker_Env.implicits)
      }
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____26894 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____26894
         then
           let uu____26895 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____26896 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____26895
             uu____26896
         else ());
        (let uu____26898 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____26898 with
         | (prob,x,wl) ->
             let g =
               let uu____26917 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____26927  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____26917  in
             ((let uu____26947 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____26947
               then
                 let uu____26948 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____26949 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____26950 =
                   let uu____26951 = FStar_Util.must g  in
                   guard_to_string env uu____26951  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____26948 uu____26949 uu____26950
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   FStar_Pervasives_Native.Some (x, g1))))
  
let (get_subtyping_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____26985 = check_subtyping env t1 t2  in
        match uu____26985 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____27004 =
              let uu____27005 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____27005 g  in
            FStar_Pervasives_Native.Some uu____27004
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____27023 = check_subtyping env t1 t2  in
        match uu____27023 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____27042 =
              let uu____27043 =
                let uu____27044 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____27044]  in
              FStar_TypeChecker_Env.close_guard env uu____27043 g  in
            FStar_Pervasives_Native.Some uu____27042
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____27081 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____27081
         then
           let uu____27082 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____27083 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____27082
             uu____27083
         else ());
        (let uu____27085 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____27085 with
         | (prob,x,wl) ->
             let g =
               let uu____27100 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____27110  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____27100  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____27133 =
                      let uu____27134 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____27134]  in
                    FStar_TypeChecker_Env.close_guard env uu____27133 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____27171 = subtype_nosmt env t1 t2  in
        match uu____27171 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
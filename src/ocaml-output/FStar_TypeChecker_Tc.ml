open Prims
let (set_hint_correlator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      let tbl =
        FStar_All.pipe_right env.FStar_TypeChecker_Env.qtbl_name_and_index
          FStar_Pervasives_Native.fst
         in
      let get_n lid =
        let n_opt = FStar_Util.smap_try_find tbl lid.FStar_Ident.str  in
        if FStar_Util.is_some n_opt
        then FStar_All.pipe_right n_opt FStar_Util.must
        else (Prims.parse_int "0")  in
      let uu____65 = FStar_Options.reuse_hint_for ()  in
      match uu____65 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____73 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.lid_add_suffix uu____73 l  in
          let uu___380_74 = env  in
          let uu____75 =
            let uu____90 =
              let uu____98 = let uu____104 = get_n lid  in (lid, uu____104)
                 in
              FStar_Pervasives_Native.Some uu____98  in
            (tbl, uu____90)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___380_74.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___380_74.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___380_74.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___380_74.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___380_74.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___380_74.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___380_74.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___380_74.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___380_74.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___380_74.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___380_74.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___380_74.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___380_74.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___380_74.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___380_74.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___380_74.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___380_74.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___380_74.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___380_74.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___380_74.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___380_74.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___380_74.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___380_74.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___380_74.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___380_74.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___380_74.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___380_74.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___380_74.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___380_74.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___380_74.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___380_74.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____75;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___380_74.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___380_74.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___380_74.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___380_74.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___380_74.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___380_74.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___380_74.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___380_74.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___380_74.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___380_74.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___380_74.FStar_TypeChecker_Env.nbe)
          }
      | FStar_Pervasives_Native.None  ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          let lid =
            match lids with
            | [] ->
                let uu____127 = FStar_TypeChecker_Env.current_module env  in
                let uu____128 =
                  let uu____130 = FStar_Syntax_Syntax.next_id ()  in
                  FStar_All.pipe_right uu____130 FStar_Util.string_of_int  in
                FStar_Ident.lid_add_suffix uu____127 uu____128
            | l::uu____135 -> l  in
          let uu___381_138 = env  in
          let uu____139 =
            let uu____154 =
              let uu____162 = let uu____168 = get_n lid  in (lid, uu____168)
                 in
              FStar_Pervasives_Native.Some uu____162  in
            (tbl, uu____154)  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___381_138.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___381_138.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___381_138.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___381_138.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___381_138.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___381_138.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___381_138.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___381_138.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___381_138.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___381_138.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___381_138.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___381_138.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___381_138.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___381_138.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___381_138.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___381_138.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___381_138.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___381_138.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___381_138.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___381_138.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___381_138.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___381_138.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___381_138.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___381_138.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___381_138.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___381_138.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___381_138.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___381_138.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___381_138.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___381_138.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___381_138.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____139;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___381_138.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___381_138.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___381_138.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___381_138.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___381_138.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___381_138.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___381_138.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___381_138.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___381_138.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___381_138.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___381_138.FStar_TypeChecker_Env.nbe)
          }
  
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    (FStar_Options.log_types ()) &&
      (let uu____194 =
         let uu____196 = FStar_TypeChecker_Env.current_module env  in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____196  in
       Prims.op_Negation uu____194)
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____213 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____213 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____243 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____243
         then
           let uu____247 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu____247
         else ());
        (let uu____252 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____252 with
         | (t',uu____260,uu____261) ->
             ((let uu____263 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____263
               then
                 let uu____267 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____267
               else ());
              t'))
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____288 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____288
  
let check_nogen :
  'Auu____298 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ ->
          ('Auu____298 Prims.list * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let t1 = tc_check_trivial_guard env t k  in
        let uu____321 =
          FStar_TypeChecker_Normalize.normalize [FStar_TypeChecker_Env.Beta]
            env t1
           in
        ([], uu____321)
  
let (monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax))
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail1 uu____357 =
          let uu____358 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____364 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____358 uu____364  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____408)::(wp,uu____410)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____439 -> fail1 ())
        | uu____440 -> fail1 ()
  
let (open_and_check :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp))
  =
  fun env  ->
    fun eff_binders  ->
      fun other_binders  ->
        fun t  ->
          let subst1 =
            FStar_Syntax_Subst.opening_of_binders
              (FStar_List.append eff_binders other_binders)
             in
          let t1 = FStar_Syntax_Subst.subst subst1 t  in
          let uu____506 = FStar_TypeChecker_TcTerm.tc_term env t1  in
          match uu____506 with | (t2,comp,uu____519) -> (t2, comp)
  
let (elaborate_and_star :
  FStar_TypeChecker_DMFF.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.tscheme ->
          (FStar_TypeChecker_DMFF.env * FStar_Syntax_Syntax.typ *
            FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun dmff_env  ->
    fun eff_binders  ->
      fun other_binders  ->
        fun item  ->
          let env = FStar_TypeChecker_DMFF.get_env dmff_env  in
          let uu____558 = item  in
          match uu____558 with
          | (u_item,item1) ->
              let uu____577 =
                open_and_check env eff_binders other_binders item1  in
              (match uu____577 with
               | (item2,item_comp) ->
                   ((let uu____593 =
                       let uu____595 =
                         FStar_Syntax_Util.is_total_lcomp item_comp  in
                       Prims.op_Negation uu____595  in
                     if uu____593
                     then
                       let uu____598 =
                         let uu____604 =
                           let uu____606 =
                             FStar_Syntax_Print.term_to_string item2  in
                           let uu____608 =
                             FStar_Syntax_Print.lcomp_to_string item_comp  in
                           FStar_Util.format2
                             "Computation for [%s] is not total : %s !"
                             uu____606 uu____608
                            in
                         (FStar_Errors.Fatal_ComputationNotTotal, uu____604)
                          in
                       FStar_Errors.raise_err uu____598
                     else ());
                    (let uu____614 =
                       FStar_TypeChecker_DMFF.star_expr dmff_env item2  in
                     match uu____614 with
                     | (item_t,item_wp,item_elab) ->
                         let uu____632 = recheck_debug "*" env item_wp  in
                         let uu____634 = recheck_debug "_" env item_elab  in
                         (dmff_env, item_t, item_wp, item_elab))))
  
let (cps_and_elaborate_ed :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun ed  ->
      let signature = ed.FStar_Syntax_Syntax.signature  in
      let uu____658 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders signature
         in
      match uu____658 with
      | (effect_binders_un,signature_un) ->
          let uu____675 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____675 with
           | (effect_binders,env1,uu____694) ->
               let uu____695 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____695 with
                | (signature1,uu____711) ->
                    let raise_error1 uu____727 =
                      match uu____727 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature1.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____763  ->
                           match uu____763 with
                           | (bv,qual) ->
                               let uu____782 =
                                 let uu___382_783 = bv  in
                                 let uu____784 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___382_783.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___382_783.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____784
                                 }  in
                               (uu____782, qual)) effect_binders
                       in
                    let uu____789 =
                      let uu____796 =
                        let uu____797 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____797.FStar_Syntax_Syntax.n  in
                      match uu____796 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____807)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____839 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____789 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____865 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____865
                           then
                             let uu____868 =
                               let uu____871 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____871  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____868
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature1.FStar_Syntax_Syntax.pos
                            in
                         let uu____883 =
                           open_and_check env1 effect_binders1 []
                             (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                            in
                         (match uu____883 with
                          | (repr,_comp) ->
                              ((let uu____907 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____907
                                then
                                  let uu____911 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____911
                                else ());
                               (let dmff_env =
                                  FStar_TypeChecker_DMFF.empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       env1 FStar_Range.dummyRange)
                                   in
                                let wp_type =
                                  FStar_TypeChecker_DMFF.star_type dmff_env
                                    repr
                                   in
                                let uu____918 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____921 =
                                    let uu____922 =
                                      let uu____923 =
                                        let uu____940 =
                                          let uu____951 =
                                            let uu____960 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____963 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____960, uu____963)  in
                                          [uu____951]  in
                                        (wp_type, uu____940)  in
                                      FStar_Syntax_Syntax.Tm_app uu____923
                                       in
                                    mk1 uu____922  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env1
                                    uu____921
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____1011 =
                                      let uu____1018 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____1018)  in
                                    let uu____1024 =
                                      let uu____1033 =
                                        let uu____1040 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____1040
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____1033]  in
                                    uu____1011 :: uu____1024  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____1077 =
                                  recheck_debug
                                    "turned into the effect signature" env1
                                    effect_signature
                                   in
                                let sigelts = FStar_Util.mk_ref []  in
                                let mk_lid name =
                                  FStar_Syntax_Util.dm4f_lid ed name  in
                                let is_unk t =
                                  let uu____1101 =
                                    let uu____1102 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____1102.FStar_Syntax_Syntax.n  in
                                  match uu____1101 with
                                  | FStar_Syntax_Syntax.Tm_unknown  -> true
                                  | uu____1107 -> false  in
                                let uu____1109 =
                                  elaborate_and_star dmff_env effect_binders1
                                    []
                                    (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                   in
                                match uu____1109 with
                                | (dmff_env1,uu____1135,bind_wp,bind_elab) ->
                                    let bind_wp1 =
                                      let uu____1141 =
                                        is_unk
                                          (FStar_Pervasives_Native.snd
                                             (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind)
                                         in
                                      if uu____1141
                                      then
                                        let uu____1150 =
                                          let uu____1151 =
                                            let uu____1158 =
                                              FStar_Syntax_Syntax.tabbrev
                                                FStar_Parser_Const.range_lid
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____1158
                                             in
                                          [uu____1151]  in
                                        FStar_Syntax_Util.abs uu____1150
                                          bind_wp
                                          FStar_Pervasives_Native.None
                                      else
                                        FStar_Pervasives_Native.snd
                                          (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                       in
                                    let uu____1177 =
                                      elaborate_and_star dmff_env1
                                        effect_binders1 []
                                        (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                       in
                                    (match uu____1177 with
                                     | (dmff_env2,uu____1203,return_wp,return_elab)
                                         ->
                                         let return_wp1 =
                                           let uu____1209 =
                                             is_unk
                                               (FStar_Pervasives_Native.snd
                                                  (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret)
                                              in
                                           if uu____1209
                                           then return_wp
                                           else
                                             FStar_Pervasives_Native.snd
                                               (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                            in
                                         let rc_gtot =
                                           {
                                             FStar_Syntax_Syntax.residual_effect
                                               =
                                               FStar_Parser_Const.effect_GTot_lid;
                                             FStar_Syntax_Syntax.residual_typ
                                               = FStar_Pervasives_Native.None;
                                             FStar_Syntax_Syntax.residual_flags
                                               = []
                                           }  in
                                         let lift_from_pure_wp =
                                           let pure_wp_type t =
                                             FStar_TypeChecker_DMFF.double_star
                                               t
                                              in
                                           let b1 =
                                             let uu____1237 =
                                               FStar_Syntax_Syntax.new_bv
                                                 FStar_Pervasives_Native.None
                                                 FStar_Syntax_Util.ktype
                                                in
                                             FStar_Syntax_Syntax.mk_binder
                                               uu____1237
                                              in
                                           let t_b1 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               (FStar_Pervasives_Native.fst
                                                  b1)
                                              in
                                           let bwp =
                                             let uu____1242 =
                                               let uu____1243 =
                                                 pure_wp_type t_b1  in
                                               FStar_Syntax_Syntax.new_bv
                                                 FStar_Pervasives_Native.None
                                                 uu____1243
                                                in
                                             FStar_Syntax_Syntax.mk_binder
                                               uu____1242
                                              in
                                           let t_wp =
                                             FStar_Syntax_Syntax.bv_to_name
                                               (FStar_Pervasives_Native.fst
                                                  bwp)
                                              in
                                           let b2 =
                                             let uu____1248 =
                                               FStar_Syntax_Syntax.new_bv
                                                 FStar_Pervasives_Native.None
                                                 t_b1
                                                in
                                             FStar_Syntax_Syntax.mk_binder
                                               uu____1248
                                              in
                                           let t_b2 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               (FStar_Pervasives_Native.fst
                                                  b2)
                                              in
                                           let t =
                                             let uu____1253 =
                                               let uu____1254 =
                                                 let uu____1265 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     t_b1
                                                    in
                                                 [uu____1265]  in
                                               FStar_Syntax_Util.mk_app
                                                 wp_type uu____1254
                                                in
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.Beta]
                                               env1 uu____1253
                                              in
                                           let uu____1290 =
                                             FStar_Syntax_Util.arrow_formals_comp
                                               t
                                              in
                                           match uu____1290 with
                                           | (bs,r) ->
                                               let t00 =
                                                 let uu____1326 =
                                                   let uu____1337 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t_b1
                                                      in
                                                   let uu____1344 =
                                                     let uu____1353 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t_b2
                                                        in
                                                     let uu____1360 =
                                                       FStar_List.map
                                                         (fun uu____1385  ->
                                                            match uu____1385
                                                            with
                                                            | (bv,q) ->
                                                                let uu____1404
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    bv
                                                                   in
                                                                (uu____1404,
                                                                  q)) bs
                                                        in
                                                     uu____1353 :: uu____1360
                                                      in
                                                   uu____1337 :: uu____1344
                                                    in
                                                 FStar_Syntax_Util.mk_app
                                                   return_wp1 uu____1326
                                                  in
                                               let t0 =
                                                 FStar_Syntax_Util.abs 
                                                   [b2] t00
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let t1 =
                                                 let uu____1437 =
                                                   let uu____1440 =
                                                     let uu____1451 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t0
                                                        in
                                                     [uu____1451]  in
                                                   FStar_Syntax_Util.mk_app
                                                     t_wp uu____1440
                                                    in
                                                 FStar_Syntax_Util.abs bs
                                                   uu____1437
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let t2 =
                                                 FStar_Syntax_Util.abs
                                                   [b1; bwp] t1
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let t21 =
                                                 FStar_TypeChecker_Normalize.normalize
                                                   [FStar_TypeChecker_Env.Beta]
                                                   env1 t2
                                                  in
                                               ((let uu____1499 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "ED")
                                                    in
                                                 if uu____1499
                                                 then
                                                   let uu____1504 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t21
                                                      in
                                                   FStar_Util.print1
                                                     "elaborated lift from PURE = %s\n"
                                                     uu____1504
                                                 else ());
                                                t21)
                                            in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = (Prims.parse_int "0")
                                           then t
                                           else
                                             (let uu____1534 =
                                                let uu____1535 =
                                                  let uu____1536 =
                                                    let uu____1553 =
                                                      let uu____1564 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____1564
                                                       in
                                                    (t, uu____1553)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____1536
                                                   in
                                                mk1 uu____1535  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____1534)
                                            in
                                         let register name item =
                                           let uu____1598 =
                                             let uu____1603 = mk_lid name  in
                                             let uu____1604 =
                                               FStar_Syntax_Util.abs
                                                 effect_binders1 item
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_TypeChecker_Util.mk_toplevel_definition
                                               env1 uu____1603 uu____1604
                                              in
                                           match uu____1598 with
                                           | (sigelt,fv) ->
                                               ((let uu____1608 =
                                                   let uu____1611 =
                                                     FStar_ST.op_Bang sigelts
                                                      in
                                                   sigelt :: uu____1611  in
                                                 FStar_ST.op_Colon_Equals
                                                   sigelts uu____1608);
                                                fv)
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____1709 =
                                             let uu____1712 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.PushOptions
                                                       (FStar_Pervasives_Native.Some
                                                          "--admit_smt_queries true")))
                                                in
                                             let uu____1715 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____1712 :: uu____1715  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____1709);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____1811 =
                                              let uu____1814 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     FStar_Syntax_Syntax.PopOptions)
                                                 in
                                              let uu____1815 =
                                                FStar_ST.op_Bang sigelts  in
                                              uu____1814 :: uu____1815  in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____1811);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____1911 =
                                               let uu____1914 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.PushOptions
                                                         (FStar_Pervasives_Native.Some
                                                            "--admit_smt_queries true")))
                                                  in
                                               let uu____1917 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____1914 :: uu____1917  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____1911);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____2013 =
                                                let uu____2016 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       FStar_Syntax_Syntax.PopOptions)
                                                   in
                                                let uu____2017 =
                                                  FStar_ST.op_Bang sigelts
                                                   in
                                                uu____2016 :: uu____2017  in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____2013);
                                             (let uu____2110 =
                                                FStar_List.fold_left
                                                  (fun uu____2150  ->
                                                     fun action  ->
                                                       match uu____2150 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____2171 =
                                                             let uu____2178 =
                                                               FStar_TypeChecker_DMFF.get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____2178
                                                               params_un
                                                              in
                                                           (match uu____2171
                                                            with
                                                            | (action_params,env',uu____2187)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____2213
                                                                     ->
                                                                    match uu____2213
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2232
                                                                    =
                                                                    let uu___383_2233
                                                                    = bv  in
                                                                    let uu____2234
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___383_2233.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___383_2233.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2234
                                                                    }  in
                                                                    (uu____2232,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____2240
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    effect_binders1
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____2240
                                                                 with
                                                                 | (dmff_env4,action_t,action_wp,action_elab)
                                                                    ->
                                                                    let name
                                                                    =
                                                                    ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText
                                                                     in
                                                                    let action_typ_with_wp
                                                                    =
                                                                    FStar_TypeChecker_DMFF.trans_F
                                                                    dmff_env'
                                                                    action_t
                                                                    action_wp
                                                                     in
                                                                    let action_params2
                                                                    =
                                                                    FStar_Syntax_Subst.close_binders
                                                                    action_params1
                                                                     in
                                                                    let action_elab1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_elab
                                                                     in
                                                                    let action_typ_with_wp1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_typ_with_wp
                                                                     in
                                                                    let action_elab2
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    action_params2
                                                                    action_elab1
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let action_typ_with_wp2
                                                                    =
                                                                    match action_params2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    action_typ_with_wp1
                                                                    | 
                                                                    uu____2283
                                                                    ->
                                                                    let uu____2284
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2284
                                                                     in
                                                                    ((
                                                                    let uu____2288
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____2288
                                                                    then
                                                                    let uu____2293
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____2296
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____2299
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____2301
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2293
                                                                    uu____2296
                                                                    uu____2299
                                                                    uu____2301
                                                                    else ());
                                                                    (let action_elab3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2
                                                                     in
                                                                    let action_typ_with_wp3
                                                                    =
                                                                    register
                                                                    (Prims.strcat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____2310
                                                                    =
                                                                    let uu____2313
                                                                    =
                                                                    let uu___384_2314
                                                                    = action
                                                                     in
                                                                    let uu____2315
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____2316
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___384_2314.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___384_2314.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___384_2314.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2315;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2316
                                                                    }  in
                                                                    uu____2313
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____2310))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____2110 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions
                                                     in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a"
                                                        FStar_Pervasives_Native.None
                                                        wp_a
                                                       in
                                                    let binders =
                                                      let uu____2360 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____2367 =
                                                        let uu____2376 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____2376]  in
                                                      uu____2360 ::
                                                        uu____2367
                                                       in
                                                    let uu____2401 =
                                                      let uu____2404 =
                                                        let uu____2405 =
                                                          let uu____2406 =
                                                            let uu____2423 =
                                                              let uu____2434
                                                                =
                                                                let uu____2443
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____2446
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____2443,
                                                                  uu____2446)
                                                                 in
                                                              [uu____2434]
                                                               in
                                                            (repr,
                                                              uu____2423)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2406
                                                           in
                                                        mk1 uu____2405  in
                                                      let uu____2482 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2404
                                                        uu____2482
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2401
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____2483 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____2487 =
                                                    let uu____2496 =
                                                      let uu____2497 =
                                                        let uu____2500 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2500
                                                         in
                                                      uu____2497.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____2496 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2514)
                                                        ->
                                                        let uu____2551 =
                                                          let uu____2572 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____2572
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2640 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____2551
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2705 =
                                                               let uu____2706
                                                                 =
                                                                 let uu____2709
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2709
                                                                  in
                                                               uu____2706.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____2705
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2742
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____2742
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2757
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2788
                                                                     ->
                                                                    match uu____2788
                                                                    with
                                                                    | 
                                                                    (bv,uu____2797)
                                                                    ->
                                                                    let uu____2802
                                                                    =
                                                                    let uu____2804
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2804
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2802
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____2757
                                                                    with
                                                                    | 
                                                                    (pre_args,post_args)
                                                                    ->
                                                                    let post
                                                                    =
                                                                    match post_args
                                                                    with
                                                                    | 
                                                                    post::[]
                                                                    -> post
                                                                    | 
                                                                    [] ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____2896
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____2896
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____2906
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____2917
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____2917
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____2927
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____2930
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____2927,
                                                                    uu____2930)))
                                                              | uu____2945 ->
                                                                  let uu____2946
                                                                    =
                                                                    let uu____2952
                                                                    =
                                                                    let uu____2954
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2954
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____2952)
                                                                     in
                                                                  raise_error1
                                                                    uu____2946))
                                                    | uu____2966 ->
                                                        let uu____2967 =
                                                          let uu____2973 =
                                                            let uu____2975 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____2975
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____2973)
                                                           in
                                                        raise_error1
                                                          uu____2967
                                                     in
                                                  (match uu____2487 with
                                                   | (pre,post) ->
                                                       ((let uu____3008 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____3011 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____3014 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___385_3017
                                                             = ed  in
                                                           let uu____3018 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____3019 =
                                                             let uu____3020 =
                                                               let uu____3021
                                                                 =
                                                                 apply_close
                                                                   return_wp2
                                                                  in
                                                               ([],
                                                                 uu____3021)
                                                                in
                                                             let uu____3028 =
                                                               let uu____3029
                                                                 =
                                                                 apply_close
                                                                   bind_wp2
                                                                  in
                                                               ([],
                                                                 uu____3029)
                                                                in
                                                             {
                                                               FStar_Syntax_Syntax.monad_m
                                                                 =
                                                                 FStar_Syntax_Syntax.tun;
                                                               FStar_Syntax_Syntax.monad_ret
                                                                 = uu____3020;
                                                               FStar_Syntax_Syntax.monad_bind
                                                                 = uu____3028
                                                             }  in
                                                           let uu____3036 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature
                                                              in
                                                           let uu____3037 =
                                                             let uu____3038 =
                                                               apply_close
                                                                 repr2
                                                                in
                                                             let uu____3039 =
                                                               let uu____3040
                                                                 =
                                                                 apply_close
                                                                   return_elab1
                                                                  in
                                                               ([],
                                                                 uu____3040)
                                                                in
                                                             let uu____3047 =
                                                               let uu____3048
                                                                 =
                                                                 apply_close
                                                                   bind_elab1
                                                                  in
                                                               ([],
                                                                 uu____3048)
                                                                in
                                                             {
                                                               FStar_Syntax_Syntax.monad_m
                                                                 = uu____3038;
                                                               FStar_Syntax_Syntax.monad_ret
                                                                 = uu____3039;
                                                               FStar_Syntax_Syntax.monad_bind
                                                                 = uu____3047
                                                             }  in
                                                           {
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___385_3017.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___385_3017.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___385_3017.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____3018;
                                                             FStar_Syntax_Syntax.spec
                                                               = uu____3019;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____3036;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___385_3017.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___385_3017.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___385_3017.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___385_3017.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___385_3017.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___385_3017.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___385_3017.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___385_3017.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____3037;
                                                             FStar_Syntax_Syntax.elaborated
                                                               =
                                                               (uu___385_3017.FStar_Syntax_Syntax.elaborated);
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___385_3017.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____3055 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____3055
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____3073
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____3073
                                                               then
                                                                 let uu____3077
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____3077
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders1)
                                                                    =
                                                                    (Prims.parse_int "0")
                                                                 then
                                                                   let lift_from_pure
                                                                    =
                                                                    let uu____3096
                                                                    =
                                                                    let uu____3099
                                                                    =
                                                                    let uu____3100
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____3100)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3099
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____3096;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____3107
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____3107
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____3110
                                                                 =
                                                                 let uu____3113
                                                                   =
                                                                   let uu____3116
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____3116
                                                                    in
                                                                 FStar_List.append
                                                                   uu____3113
                                                                   sigelts'
                                                                  in
                                                               (uu____3110,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  
let tc_eff_decl :
  'Auu____3177 .
    FStar_TypeChecker_Env.env ->
      'Auu____3177 ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun se  ->
      fun ed  ->
        (let uu____3194 =
           FStar_TypeChecker_Env.debug env0 (FStar_Options.Other "ED")  in
         if uu____3194
         then
           let uu____3198 = FStar_Syntax_Print.eff_decl_to_string ed  in
           FStar_Util.print1 "initial eff_decl :\n\t%s\n" uu____3198
         else ());
        (let uu____3203 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____3203 with
         | (open_annotated_univs,annotated_univ_names) ->
             let open_univs n_binders t =
               let uu____3235 =
                 FStar_Syntax_Subst.shift_subst n_binders
                   open_annotated_univs
                  in
               FStar_Syntax_Subst.subst uu____3235 t  in
             let open_univs_binders n_binders bs =
               let uu____3251 =
                 FStar_Syntax_Subst.shift_subst n_binders
                   open_annotated_univs
                  in
               FStar_Syntax_Subst.subst_binders uu____3251 bs  in
             let n_effect_params =
               FStar_List.length ed.FStar_Syntax_Syntax.binders  in
             let signature = ed.FStar_Syntax_Syntax.signature  in
             let uu____3262 =
               let uu____3269 =
                 open_univs_binders (Prims.parse_int "0")
                   ed.FStar_Syntax_Syntax.binders
                  in
               let uu____3271 = open_univs n_effect_params signature  in
               FStar_Syntax_Subst.open_term' uu____3269 uu____3271  in
             (match uu____3262 with
              | (effect_params_un,signature_un,opening) ->
                  let env =
                    FStar_TypeChecker_Env.push_univ_vars env0
                      annotated_univ_names
                     in
                  let uu____3282 =
                    FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un
                     in
                  (match uu____3282 with
                   | (effect_params,env1,uu____3291) ->
                       let uu____3292 =
                         FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                           signature_un
                          in
                       (match uu____3292 with
                        | (signature1,uu____3298) ->
                            let ed1 =
                              let uu___386_3300 = ed  in
                              {
                                FStar_Syntax_Syntax.cattributes =
                                  (uu___386_3300.FStar_Syntax_Syntax.cattributes);
                                FStar_Syntax_Syntax.mname =
                                  (uu___386_3300.FStar_Syntax_Syntax.mname);
                                FStar_Syntax_Syntax.univs =
                                  (uu___386_3300.FStar_Syntax_Syntax.univs);
                                FStar_Syntax_Syntax.binders = effect_params;
                                FStar_Syntax_Syntax.spec =
                                  (uu___386_3300.FStar_Syntax_Syntax.spec);
                                FStar_Syntax_Syntax.signature = signature1;
                                FStar_Syntax_Syntax.if_then_else =
                                  (uu___386_3300.FStar_Syntax_Syntax.if_then_else);
                                FStar_Syntax_Syntax.ite_wp =
                                  (uu___386_3300.FStar_Syntax_Syntax.ite_wp);
                                FStar_Syntax_Syntax.stronger =
                                  (uu___386_3300.FStar_Syntax_Syntax.stronger);
                                FStar_Syntax_Syntax.close_wp =
                                  (uu___386_3300.FStar_Syntax_Syntax.close_wp);
                                FStar_Syntax_Syntax.assert_p =
                                  (uu___386_3300.FStar_Syntax_Syntax.assert_p);
                                FStar_Syntax_Syntax.assume_p =
                                  (uu___386_3300.FStar_Syntax_Syntax.assume_p);
                                FStar_Syntax_Syntax.null_wp =
                                  (uu___386_3300.FStar_Syntax_Syntax.null_wp);
                                FStar_Syntax_Syntax.trivial =
                                  (uu___386_3300.FStar_Syntax_Syntax.trivial);
                                FStar_Syntax_Syntax.repr =
                                  (uu___386_3300.FStar_Syntax_Syntax.repr);
                                FStar_Syntax_Syntax.elaborated =
                                  (uu___386_3300.FStar_Syntax_Syntax.elaborated);
                                FStar_Syntax_Syntax.actions =
                                  (uu___386_3300.FStar_Syntax_Syntax.actions);
                                FStar_Syntax_Syntax.eff_attrs =
                                  (uu___386_3300.FStar_Syntax_Syntax.eff_attrs)
                              }  in
                            let ed2 =
                              match (effect_params, annotated_univ_names)
                              with
                              | ([],[]) -> ed1
                              | uu____3328 ->
                                  let op uu____3360 =
                                    match uu____3360 with
                                    | (us,t) ->
                                        let n_us = FStar_List.length us  in
                                        let uu____3380 =
                                          let uu____3381 =
                                            FStar_Syntax_Subst.shift_subst
                                              n_us opening
                                             in
                                          let uu____3390 = open_univs n_us t
                                             in
                                          FStar_Syntax_Subst.subst uu____3381
                                            uu____3390
                                           in
                                        (us, uu____3380)
                                     in
                                  let uu___387_3399 = ed1  in
                                  let uu____3400 =
                                    let uu____3401 =
                                      let uu____3402 =
                                        op
                                          ([],
                                            ((ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m))
                                         in
                                      FStar_Pervasives_Native.snd uu____3402
                                       in
                                    let uu____3413 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                       in
                                    let uu____3414 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                       in
                                    {
                                      FStar_Syntax_Syntax.monad_m =
                                        uu____3401;
                                      FStar_Syntax_Syntax.monad_ret =
                                        uu____3413;
                                      FStar_Syntax_Syntax.monad_bind =
                                        uu____3414
                                    }  in
                                  let uu____3415 =
                                    op ed1.FStar_Syntax_Syntax.if_then_else
                                     in
                                  let uu____3416 =
                                    op ed1.FStar_Syntax_Syntax.ite_wp  in
                                  let uu____3417 =
                                    op ed1.FStar_Syntax_Syntax.stronger  in
                                  let uu____3418 =
                                    op ed1.FStar_Syntax_Syntax.close_wp  in
                                  let uu____3419 =
                                    op ed1.FStar_Syntax_Syntax.assert_p  in
                                  let uu____3420 =
                                    op ed1.FStar_Syntax_Syntax.assume_p  in
                                  let uu____3421 =
                                    op ed1.FStar_Syntax_Syntax.null_wp  in
                                  let uu____3422 =
                                    op ed1.FStar_Syntax_Syntax.trivial  in
                                  let uu____3423 =
                                    let uu____3424 =
                                      let uu____3425 =
                                        op
                                          ([],
                                            ((ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m))
                                         in
                                      FStar_Pervasives_Native.snd uu____3425
                                       in
                                    let uu____3436 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                       in
                                    let uu____3437 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                       in
                                    {
                                      FStar_Syntax_Syntax.monad_m =
                                        uu____3424;
                                      FStar_Syntax_Syntax.monad_ret =
                                        uu____3436;
                                      FStar_Syntax_Syntax.monad_bind =
                                        uu____3437
                                    }  in
                                  let uu____3438 =
                                    FStar_List.map
                                      (fun a  ->
                                         let uu___388_3446 = a  in
                                         let uu____3447 =
                                           let uu____3448 =
                                             op
                                               ((a.FStar_Syntax_Syntax.action_univs),
                                                 (a.FStar_Syntax_Syntax.action_defn))
                                              in
                                           FStar_Pervasives_Native.snd
                                             uu____3448
                                            in
                                         let uu____3459 =
                                           let uu____3460 =
                                             op
                                               ((a.FStar_Syntax_Syntax.action_univs),
                                                 (a.FStar_Syntax_Syntax.action_typ))
                                              in
                                           FStar_Pervasives_Native.snd
                                             uu____3460
                                            in
                                         {
                                           FStar_Syntax_Syntax.action_name =
                                             (uu___388_3446.FStar_Syntax_Syntax.action_name);
                                           FStar_Syntax_Syntax.action_unqualified_name
                                             =
                                             (uu___388_3446.FStar_Syntax_Syntax.action_unqualified_name);
                                           FStar_Syntax_Syntax.action_univs =
                                             (uu___388_3446.FStar_Syntax_Syntax.action_univs);
                                           FStar_Syntax_Syntax.action_params
                                             =
                                             (uu___388_3446.FStar_Syntax_Syntax.action_params);
                                           FStar_Syntax_Syntax.action_defn =
                                             uu____3447;
                                           FStar_Syntax_Syntax.action_typ =
                                             uu____3459
                                         }) ed1.FStar_Syntax_Syntax.actions
                                     in
                                  {
                                    FStar_Syntax_Syntax.cattributes =
                                      (uu___387_3399.FStar_Syntax_Syntax.cattributes);
                                    FStar_Syntax_Syntax.mname =
                                      (uu___387_3399.FStar_Syntax_Syntax.mname);
                                    FStar_Syntax_Syntax.univs =
                                      annotated_univ_names;
                                    FStar_Syntax_Syntax.binders =
                                      (uu___387_3399.FStar_Syntax_Syntax.binders);
                                    FStar_Syntax_Syntax.spec = uu____3400;
                                    FStar_Syntax_Syntax.signature =
                                      (uu___387_3399.FStar_Syntax_Syntax.signature);
                                    FStar_Syntax_Syntax.if_then_else =
                                      uu____3415;
                                    FStar_Syntax_Syntax.ite_wp = uu____3416;
                                    FStar_Syntax_Syntax.stronger = uu____3417;
                                    FStar_Syntax_Syntax.close_wp = uu____3418;
                                    FStar_Syntax_Syntax.assert_p = uu____3419;
                                    FStar_Syntax_Syntax.assume_p = uu____3420;
                                    FStar_Syntax_Syntax.null_wp = uu____3421;
                                    FStar_Syntax_Syntax.trivial = uu____3422;
                                    FStar_Syntax_Syntax.repr = uu____3423;
                                    FStar_Syntax_Syntax.elaborated =
                                      (uu___387_3399.FStar_Syntax_Syntax.elaborated);
                                    FStar_Syntax_Syntax.actions = uu____3438;
                                    FStar_Syntax_Syntax.eff_attrs =
                                      (uu___387_3399.FStar_Syntax_Syntax.eff_attrs)
                                  }
                               in
                            ((let uu____3472 =
                                FStar_TypeChecker_Env.debug env0
                                  (FStar_Options.Other "ED")
                                 in
                              if uu____3472
                              then
                                let uu____3476 =
                                  FStar_Syntax_Print.eff_decl_to_string ed2
                                   in
                                FStar_Util.print1
                                  "eff_decl after opening:\n\t%s\n"
                                  uu____3476
                              else ());
                             (let wp_with_fresh_result_type env2 mname
                                signature2 =
                                let fail1 t =
                                  let uu____3515 =
                                    FStar_TypeChecker_Err.unexpected_signature_for_monad
                                      env2 mname t
                                     in
                                  let uu____3521 =
                                    FStar_Ident.range_of_lid mname  in
                                  FStar_Errors.raise_error uu____3515
                                    uu____3521
                                   in
                                let uu____3528 =
                                  let uu____3529 =
                                    FStar_Syntax_Subst.compress signature2
                                     in
                                  uu____3529.FStar_Syntax_Syntax.n  in
                                match uu____3528 with
                                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                    let bs1 =
                                      FStar_Syntax_Subst.open_binders bs  in
                                    (match bs1 with
                                     | (a,uu____3568)::(wp,uu____3570)::[] ->
                                         (a, (wp.FStar_Syntax_Syntax.sort))
                                     | uu____3599 -> fail1 signature2)
                                | uu____3600 -> fail1 signature2  in
                              let uu____3601 =
                                wp_with_fresh_result_type env1
                                  ed2.FStar_Syntax_Syntax.mname signature1
                                 in
                              match uu____3601 with
                              | (a,wp_a) ->
                                  let fresh_effect_signature uu____3625 =
                                    match annotated_univ_names with
                                    | [] ->
                                        let uu____3632 =
                                          FStar_TypeChecker_TcTerm.tc_trivial_guard
                                            env1 signature_un
                                           in
                                        (match uu____3632 with
                                         | (signature2,uu____3644) ->
                                             wp_with_fresh_result_type env1
                                               ed2.FStar_Syntax_Syntax.mname
                                               signature2)
                                    | uu____3645 ->
                                        let uu____3648 =
                                          let uu____3653 =
                                            let uu____3654 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                annotated_univ_names
                                                signature1
                                               in
                                            (annotated_univ_names,
                                              uu____3654)
                                             in
                                          FStar_TypeChecker_Env.inst_tscheme
                                            uu____3653
                                           in
                                        (match uu____3648 with
                                         | (uu____3667,signature2) ->
                                             wp_with_fresh_result_type env1
                                               ed2.FStar_Syntax_Syntax.mname
                                               signature2)
                                     in
                                  let env2 =
                                    let uu____3670 =
                                      FStar_Syntax_Syntax.new_bv
                                        FStar_Pervasives_Native.None
                                        signature1
                                       in
                                    FStar_TypeChecker_Env.push_bv env1
                                      uu____3670
                                     in
                                  ((let uu____3672 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env0)
                                        (FStar_Options.Other "ED")
                                       in
                                    if uu____3672
                                    then
                                      let uu____3677 =
                                        FStar_Syntax_Print.lid_to_string
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      let uu____3679 =
                                        FStar_Syntax_Print.binders_to_string
                                          " " ed2.FStar_Syntax_Syntax.binders
                                         in
                                      let uu____3682 =
                                        FStar_Syntax_Print.term_to_string
                                          signature1
                                         in
                                      let uu____3684 =
                                        let uu____3686 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Print.term_to_string
                                          uu____3686
                                         in
                                      let uu____3687 =
                                        FStar_Syntax_Print.term_to_string
                                          a.FStar_Syntax_Syntax.sort
                                         in
                                      FStar_Util.print5
                                        "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                        uu____3677 uu____3679 uu____3682
                                        uu____3684 uu____3687
                                    else ());
                                   (let check_and_gen' env3 uu____3722 k =
                                      match uu____3722 with
                                      | (us,t) ->
                                          (match annotated_univ_names with
                                           | [] -> check_and_gen env3 t k
                                           | uu____3758::uu____3759 ->
                                               let uu____3762 =
                                                 FStar_Syntax_Subst.subst_tscheme
                                                   open_annotated_univs
                                                   (us, t)
                                                  in
                                               (match uu____3762 with
                                                | (us1,t1) ->
                                                    let uu____3785 =
                                                      FStar_Syntax_Subst.open_univ_vars
                                                        us1 t1
                                                       in
                                                    (match uu____3785 with
                                                     | (us2,t2) ->
                                                         let uu____3800 =
                                                           let uu____3801 =
                                                             FStar_TypeChecker_Env.push_univ_vars
                                                               env3 us2
                                                              in
                                                           tc_check_trivial_guard
                                                             uu____3801 t2 k
                                                            in
                                                         let uu____3802 =
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             us2 t2
                                                            in
                                                         (us2, uu____3802))))
                                       in
                                    let return_wp =
                                      let expected_k =
                                        let uu____3821 =
                                          let uu____3830 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____3837 =
                                            let uu____3846 =
                                              let uu____3853 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____3853
                                               in
                                            [uu____3846]  in
                                          uu____3830 :: uu____3837  in
                                        let uu____3872 =
                                          FStar_Syntax_Syntax.mk_GTotal wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____3821
                                          uu____3872
                                         in
                                      check_and_gen' env2
                                        (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                        expected_k
                                       in
                                    let bind_wp =
                                      let uu____3876 =
                                        fresh_effect_signature ()  in
                                      match uu____3876 with
                                      | (b,wp_b) ->
                                          let a_wp_b =
                                            let uu____3892 =
                                              let uu____3901 =
                                                let uu____3908 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____3908
                                                 in
                                              [uu____3901]  in
                                            let uu____3921 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_b
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____3892 uu____3921
                                             in
                                          let expected_k =
                                            let uu____3927 =
                                              let uu____3936 =
                                                FStar_Syntax_Syntax.null_binder
                                                  FStar_Syntax_Syntax.t_range
                                                 in
                                              let uu____3943 =
                                                let uu____3952 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____3959 =
                                                  let uu____3968 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____3975 =
                                                    let uu____3984 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_a
                                                       in
                                                    let uu____3991 =
                                                      let uu____4000 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          a_wp_b
                                                         in
                                                      [uu____4000]  in
                                                    uu____3984 :: uu____3991
                                                     in
                                                  uu____3968 :: uu____3975
                                                   in
                                                uu____3952 :: uu____3959  in
                                              uu____3936 :: uu____3943  in
                                            let uu____4043 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_b
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____3927 uu____4043
                                             in
                                          check_and_gen' env2
                                            (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                            expected_k
                                       in
                                    let if_then_else1 =
                                      let p =
                                        let uu____4056 =
                                          let uu____4059 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4059
                                           in
                                        let uu____4060 =
                                          let uu____4061 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4061
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4056
                                          uu____4060
                                         in
                                      let expected_k =
                                        let uu____4073 =
                                          let uu____4082 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4089 =
                                            let uu____4098 =
                                              FStar_Syntax_Syntax.mk_binder p
                                               in
                                            let uu____4105 =
                                              let uu____4114 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              let uu____4121 =
                                                let uu____4130 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____4130]  in
                                              uu____4114 :: uu____4121  in
                                            uu____4098 :: uu____4105  in
                                          uu____4082 :: uu____4089  in
                                        let uu____4167 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4073
                                          uu____4167
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.if_then_else
                                        expected_k
                                       in
                                    let ite_wp =
                                      let expected_k =
                                        let uu____4182 =
                                          let uu____4191 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4198 =
                                            let uu____4207 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____4207]  in
                                          uu____4191 :: uu____4198  in
                                        let uu____4232 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4182
                                          uu____4232
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.ite_wp
                                        expected_k
                                       in
                                    let stronger =
                                      let uu____4236 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____4236 with
                                      | (t,uu____4242) ->
                                          let expected_k =
                                            let uu____4246 =
                                              let uu____4255 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4262 =
                                                let uu____4271 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____4278 =
                                                  let uu____4287 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____4287]  in
                                                uu____4271 :: uu____4278  in
                                              uu____4255 :: uu____4262  in
                                            let uu____4318 =
                                              FStar_Syntax_Syntax.mk_Total t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4246 uu____4318
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.stronger
                                            expected_k
                                       in
                                    let close_wp =
                                      let b =
                                        let uu____4331 =
                                          let uu____4334 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4334
                                           in
                                        let uu____4335 =
                                          let uu____4336 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4336
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4331
                                          uu____4335
                                         in
                                      let b_wp_a =
                                        let uu____4348 =
                                          let uu____4357 =
                                            let uu____4364 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                b
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____4364
                                             in
                                          [uu____4357]  in
                                        let uu____4377 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4348
                                          uu____4377
                                         in
                                      let expected_k =
                                        let uu____4383 =
                                          let uu____4392 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4399 =
                                            let uu____4408 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4415 =
                                              let uu____4424 =
                                                FStar_Syntax_Syntax.null_binder
                                                  b_wp_a
                                                 in
                                              [uu____4424]  in
                                            uu____4408 :: uu____4415  in
                                          uu____4392 :: uu____4399  in
                                        let uu____4455 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4383
                                          uu____4455
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.close_wp
                                        expected_k
                                       in
                                    let assert_p =
                                      let expected_k =
                                        let uu____4470 =
                                          let uu____4479 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4486 =
                                            let uu____4495 =
                                              let uu____4502 =
                                                let uu____4503 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____4503
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4502
                                               in
                                            let uu____4512 =
                                              let uu____4521 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____4521]  in
                                            uu____4495 :: uu____4512  in
                                          uu____4479 :: uu____4486  in
                                        let uu____4552 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4470
                                          uu____4552
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.assert_p
                                        expected_k
                                       in
                                    let assume_p =
                                      let expected_k =
                                        let uu____4567 =
                                          let uu____4576 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4583 =
                                            let uu____4592 =
                                              let uu____4599 =
                                                let uu____4600 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____4600
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4599
                                               in
                                            let uu____4609 =
                                              let uu____4618 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____4618]  in
                                            uu____4592 :: uu____4609  in
                                          uu____4576 :: uu____4583  in
                                        let uu____4649 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4567
                                          uu____4649
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.assume_p
                                        expected_k
                                       in
                                    let null_wp =
                                      let expected_k =
                                        let uu____4664 =
                                          let uu____4673 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          [uu____4673]  in
                                        let uu____4692 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4664
                                          uu____4692
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.null_wp
                                        expected_k
                                       in
                                    let trivial_wp =
                                      let uu____4696 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____4696 with
                                      | (t,uu____4702) ->
                                          let expected_k =
                                            let uu____4706 =
                                              let uu____4715 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4722 =
                                                let uu____4731 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____4731]  in
                                              uu____4715 :: uu____4722  in
                                            let uu____4756 =
                                              FStar_Syntax_Syntax.mk_GTotal t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4706 uu____4756
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.trivial
                                            expected_k
                                       in
                                    let uu____4759 =
                                      let uu____4772 =
                                        let uu____4773 =
                                          FStar_Syntax_Subst.compress
                                            (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                           in
                                        uu____4773.FStar_Syntax_Syntax.n  in
                                      match uu____4772 with
                                      | FStar_Syntax_Syntax.Tm_unknown  ->
                                          (((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m),
                                            ((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind),
                                            ((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret),
                                            (ed2.FStar_Syntax_Syntax.actions))
                                      | uu____4792 ->
                                          let repr =
                                            let uu____4794 =
                                              FStar_Syntax_Util.type_u ()  in
                                            match uu____4794 with
                                            | (t,uu____4800) ->
                                                let expected_k =
                                                  let uu____4804 =
                                                    let uu____4813 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a
                                                       in
                                                    let uu____4820 =
                                                      let uu____4829 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          wp_a
                                                         in
                                                      [uu____4829]  in
                                                    uu____4813 :: uu____4820
                                                     in
                                                  let uu____4854 =
                                                    FStar_Syntax_Syntax.mk_GTotal
                                                      t
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____4804 uu____4854
                                                   in
                                                tc_check_trivial_guard env2
                                                  (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                                  expected_k
                                             in
                                          let mk_repr' t wp =
                                            let repr1 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Env.EraseUniverses;
                                                FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                env2 repr
                                               in
                                            let uu____4871 =
                                              let uu____4878 =
                                                let uu____4879 =
                                                  let uu____4896 =
                                                    let uu____4907 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        t
                                                       in
                                                    let uu____4916 =
                                                      let uu____4927 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          wp
                                                         in
                                                      [uu____4927]  in
                                                    uu____4907 :: uu____4916
                                                     in
                                                  (repr1, uu____4896)  in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____4879
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____4878
                                               in
                                            uu____4871
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          let mk_repr a1 wp =
                                            let uu____4988 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            mk_repr' uu____4988 wp  in
                                          let destruct_repr t =
                                            let uu____5003 =
                                              let uu____5004 =
                                                FStar_Syntax_Subst.compress t
                                                 in
                                              uu____5004.FStar_Syntax_Syntax.n
                                               in
                                            match uu____5003 with
                                            | FStar_Syntax_Syntax.Tm_app
                                                (uu____5015,(t1,uu____5017)::
                                                 (wp,uu____5019)::[])
                                                -> (t1, wp)
                                            | uu____5078 ->
                                                failwith
                                                  "Unexpected repr type"
                                             in
                                          let bind_repr =
                                            let r =
                                              let uu____5090 =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  FStar_Parser_Const.range_0
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              FStar_All.pipe_right uu____5090
                                                FStar_Syntax_Syntax.fv_to_tm
                                               in
                                            let uu____5091 =
                                              fresh_effect_signature ()  in
                                            match uu____5091 with
                                            | (b,wp_b) ->
                                                let a_wp_b =
                                                  let uu____5107 =
                                                    let uu____5116 =
                                                      let uu____5123 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.null_binder
                                                        uu____5123
                                                       in
                                                    [uu____5116]  in
                                                  let uu____5136 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      wp_b
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____5107 uu____5136
                                                   in
                                                let wp_f =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "wp_f"
                                                    FStar_Pervasives_Native.None
                                                    wp_a
                                                   in
                                                let wp_g =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "wp_g"
                                                    FStar_Pervasives_Native.None
                                                    a_wp_b
                                                   in
                                                let x_a =
                                                  let uu____5144 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "x_a"
                                                    FStar_Pervasives_Native.None
                                                    uu____5144
                                                   in
                                                let wp_g_x =
                                                  let uu____5149 =
                                                    let uu____5154 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        wp_g
                                                       in
                                                    let uu____5155 =
                                                      let uu____5156 =
                                                        let uu____5165 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Syntax.as_arg
                                                          uu____5165
                                                         in
                                                      [uu____5156]  in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____5154 uu____5155
                                                     in
                                                  uu____5149
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                let res =
                                                  let wp =
                                                    let uu____5198 =
                                                      let uu____5203 =
                                                        let uu____5204 =
                                                          FStar_TypeChecker_Env.inst_tscheme
                                                            bind_wp
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____5204
                                                          FStar_Pervasives_Native.snd
                                                         in
                                                      let uu____5213 =
                                                        let uu____5214 =
                                                          let uu____5217 =
                                                            let uu____5220 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                a
                                                               in
                                                            let uu____5221 =
                                                              let uu____5224
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  b
                                                                 in
                                                              let uu____5225
                                                                =
                                                                let uu____5228
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f
                                                                   in
                                                                let uu____5229
                                                                  =
                                                                  let uu____5232
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                  [uu____5232]
                                                                   in
                                                                uu____5228 ::
                                                                  uu____5229
                                                                 in
                                                              uu____5224 ::
                                                                uu____5225
                                                               in
                                                            uu____5220 ::
                                                              uu____5221
                                                             in
                                                          r :: uu____5217  in
                                                        FStar_List.map
                                                          FStar_Syntax_Syntax.as_arg
                                                          uu____5214
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____5203 uu____5213
                                                       in
                                                    uu____5198
                                                      FStar_Pervasives_Native.None
                                                      FStar_Range.dummyRange
                                                     in
                                                  mk_repr b wp  in
                                                let maybe_range_arg =
                                                  let uu____5252 =
                                                    FStar_Util.for_some
                                                      (FStar_Syntax_Util.attr_eq
                                                         FStar_Syntax_Util.dm4f_bind_range_attr)
                                                      ed2.FStar_Syntax_Syntax.eff_attrs
                                                     in
                                                  if uu____5252
                                                  then
                                                    let uu____5263 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        FStar_Syntax_Syntax.t_range
                                                       in
                                                    let uu____5270 =
                                                      let uu____5279 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          FStar_Syntax_Syntax.t_range
                                                         in
                                                      [uu____5279]  in
                                                    uu____5263 :: uu____5270
                                                  else []  in
                                                let expected_k =
                                                  let uu____5315 =
                                                    let uu____5324 =
                                                      let uu____5333 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a
                                                         in
                                                      let uu____5340 =
                                                        let uu____5349 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            b
                                                           in
                                                        [uu____5349]  in
                                                      uu____5333 ::
                                                        uu____5340
                                                       in
                                                    let uu____5374 =
                                                      let uu____5383 =
                                                        let uu____5392 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_f
                                                           in
                                                        let uu____5399 =
                                                          let uu____5408 =
                                                            let uu____5415 =
                                                              let uu____5416
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_f
                                                                 in
                                                              mk_repr a
                                                                uu____5416
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____5415
                                                             in
                                                          let uu____5417 =
                                                            let uu____5426 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_g
                                                               in
                                                            let uu____5433 =
                                                              let uu____5442
                                                                =
                                                                let uu____5449
                                                                  =
                                                                  let uu____5450
                                                                    =
                                                                    let uu____5459
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____5459]
                                                                     in
                                                                  let uu____5478
                                                                    =
                                                                    let uu____5481
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____5481
                                                                     in
                                                                  FStar_Syntax_Util.arrow
                                                                    uu____5450
                                                                    uu____5478
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____5449
                                                                 in
                                                              [uu____5442]
                                                               in
                                                            uu____5426 ::
                                                              uu____5433
                                                             in
                                                          uu____5408 ::
                                                            uu____5417
                                                           in
                                                        uu____5392 ::
                                                          uu____5399
                                                         in
                                                      FStar_List.append
                                                        maybe_range_arg
                                                        uu____5383
                                                       in
                                                    FStar_List.append
                                                      uu____5324 uu____5374
                                                     in
                                                  let uu____5526 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      res
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____5315 uu____5526
                                                   in
                                                let uu____5529 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env2 expected_k
                                                   in
                                                (match uu____5529 with
                                                 | (expected_k1,uu____5537,uu____5538)
                                                     ->
                                                     let env3 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env2
                                                         (FStar_Pervasives_Native.snd
                                                            (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind).FStar_Syntax_Syntax.pos
                                                        in
                                                     let env4 =
                                                       let uu___389_5545 =
                                                         env3  in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.is_pattern
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.is_pattern);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.instantiate_imp);
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           = true;
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___389_5545.FStar_TypeChecker_Env.nbe)
                                                       }  in
                                                     let br =
                                                       check_and_gen' env4
                                                         (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                                         expected_k1
                                                        in
                                                     br)
                                             in
                                          let return_repr =
                                            let x_a =
                                              let uu____5558 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____5558
                                               in
                                            let res =
                                              let wp =
                                                let uu____5566 =
                                                  let uu____5571 =
                                                    let uu____5572 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        return_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____5572
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____5581 =
                                                    let uu____5582 =
                                                      let uu____5585 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      let uu____5586 =
                                                        let uu____5589 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        [uu____5589]  in
                                                      uu____5585 ::
                                                        uu____5586
                                                       in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____5582
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____5571 uu____5581
                                                   in
                                                uu____5566
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr a wp  in
                                            let expected_k =
                                              let uu____5603 =
                                                let uu____5612 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____5619 =
                                                  let uu____5628 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x_a
                                                     in
                                                  [uu____5628]  in
                                                uu____5612 :: uu____5619  in
                                              let uu____5653 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____5603 uu____5653
                                               in
                                            let uu____5656 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k
                                               in
                                            match uu____5656 with
                                            | (expected_k1,uu____5664,uu____5665)
                                                ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env2
                                                    (FStar_Pervasives_Native.snd
                                                       (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret).FStar_Syntax_Syntax.pos
                                                   in
                                                let uu____5671 =
                                                  check_and_gen' env3
                                                    (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                                    expected_k1
                                                   in
                                                (match uu____5671 with
                                                 | (univs1,repr1) ->
                                                     (match univs1 with
                                                      | [] -> ([], repr1)
                                                      | uu____5694 ->
                                                          FStar_Errors.raise_error
                                                            (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                              "Unexpected universe-polymorphic return for effect")
                                                            repr1.FStar_Syntax_Syntax.pos))
                                             in
                                          let actions =
                                            let check_action act =
                                              let uu____5709 =
                                                if
                                                  act.FStar_Syntax_Syntax.action_univs
                                                    = []
                                                then (env2, act)
                                                else
                                                  (let uu____5723 =
                                                     FStar_Syntax_Subst.univ_var_opening
                                                       act.FStar_Syntax_Syntax.action_univs
                                                      in
                                                   match uu____5723 with
                                                   | (usubst,uvs) ->
                                                       let uu____5746 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env2 uvs
                                                          in
                                                       let uu____5747 =
                                                         let uu___390_5748 =
                                                           act  in
                                                         let uu____5749 =
                                                           FStar_Syntax_Subst.subst_binders
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_params
                                                            in
                                                         let uu____5750 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____5751 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_typ
                                                            in
                                                         {
                                                           FStar_Syntax_Syntax.action_name
                                                             =
                                                             (uu___390_5748.FStar_Syntax_Syntax.action_name);
                                                           FStar_Syntax_Syntax.action_unqualified_name
                                                             =
                                                             (uu___390_5748.FStar_Syntax_Syntax.action_unqualified_name);
                                                           FStar_Syntax_Syntax.action_univs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.action_params
                                                             = uu____5749;
                                                           FStar_Syntax_Syntax.action_defn
                                                             = uu____5750;
                                                           FStar_Syntax_Syntax.action_typ
                                                             = uu____5751
                                                         }  in
                                                       (uu____5746,
                                                         uu____5747))
                                                 in
                                              match uu____5709 with
                                              | (env3,act1) ->
                                                  let act_typ =
                                                    let uu____5755 =
                                                      let uu____5756 =
                                                        FStar_Syntax_Subst.compress
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                         in
                                                      uu____5756.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____5755 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,c) ->
                                                        let c1 =
                                                          FStar_Syntax_Util.comp_to_comp_typ
                                                            c
                                                           in
                                                        let uu____5782 =
                                                          FStar_Ident.lid_equals
                                                            c1.FStar_Syntax_Syntax.effect_name
                                                            ed2.FStar_Syntax_Syntax.mname
                                                           in
                                                        if uu____5782
                                                        then
                                                          let uu____5785 =
                                                            let uu____5788 =
                                                              let uu____5789
                                                                =
                                                                let uu____5790
                                                                  =
                                                                  FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____5790
                                                                 in
                                                              mk_repr'
                                                                c1.FStar_Syntax_Syntax.result_typ
                                                                uu____5789
                                                               in
                                                            FStar_Syntax_Syntax.mk_Total
                                                              uu____5788
                                                             in
                                                          FStar_Syntax_Util.arrow
                                                            bs uu____5785
                                                        else
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                    | uu____5813 ->
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  let uu____5814 =
                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                      env3 act_typ
                                                     in
                                                  (match uu____5814 with
                                                   | (act_typ1,uu____5822,g_t)
                                                       ->
                                                       let env' =
                                                         let uu___391_5825 =
                                                           FStar_TypeChecker_Env.set_expected_typ
                                                             env3 act_typ1
                                                            in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             = false;
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.lax);
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___391_5825.FStar_TypeChecker_Env.nbe)
                                                         }  in
                                                       ((let uu____5828 =
                                                           FStar_TypeChecker_Env.debug
                                                             env3
                                                             (FStar_Options.Other
                                                                "ED")
                                                            in
                                                         if uu____5828
                                                         then
                                                           let uu____5832 =
                                                             FStar_Ident.text_of_lid
                                                               act1.FStar_Syntax_Syntax.action_name
                                                              in
                                                           let uu____5834 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act1.FStar_Syntax_Syntax.action_defn
                                                              in
                                                           let uu____5836 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ1
                                                              in
                                                           FStar_Util.print3
                                                             "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                             uu____5832
                                                             uu____5834
                                                             uu____5836
                                                         else ());
                                                        (let uu____5841 =
                                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                             env'
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         match uu____5841
                                                         with
                                                         | (act_defn,uu____5849,g_a)
                                                             ->
                                                             let act_defn1 =
                                                               FStar_TypeChecker_Normalize.normalize
                                                                 [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant]
                                                                 env3
                                                                 act_defn
                                                                in
                                                             let act_typ2 =
                                                               FStar_TypeChecker_Normalize.normalize
                                                                 [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant;
                                                                 FStar_TypeChecker_Env.Eager_unfolding;
                                                                 FStar_TypeChecker_Env.Beta]
                                                                 env3
                                                                 act_typ1
                                                                in
                                                             let uu____5853 =
                                                               let act_typ3 =
                                                                 FStar_Syntax_Subst.compress
                                                                   act_typ2
                                                                  in
                                                               match 
                                                                 act_typ3.FStar_Syntax_Syntax.n
                                                               with
                                                               | FStar_Syntax_Syntax.Tm_arrow
                                                                   (bs,c) ->
                                                                   let uu____5889
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                   (match uu____5889
                                                                    with
                                                                    | 
                                                                    (bs1,uu____5901)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____5908
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____5908
                                                                     in
                                                                    let uu____5911
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____5911
                                                                    with
                                                                    | 
                                                                    (k1,uu____5925,g)
                                                                    ->
                                                                    (k1, g)))
                                                               | uu____5929
                                                                   ->
                                                                   let uu____5930
                                                                    =
                                                                    let uu____5936
                                                                    =
                                                                    let uu____5938
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____5940
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____5938
                                                                    uu____5940
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____5936)
                                                                     in
                                                                   FStar_Errors.raise_error
                                                                    uu____5930
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                in
                                                             (match uu____5853
                                                              with
                                                              | (expected_k,g_k)
                                                                  ->
                                                                  let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env3
                                                                    act_typ2
                                                                    expected_k
                                                                     in
                                                                  ((let uu____5958
                                                                    =
                                                                    let uu____5959
                                                                    =
                                                                    let uu____5960
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____5960
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____5959
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env3
                                                                    uu____5958);
                                                                   (let act_typ3
                                                                    =
                                                                    let uu____5962
                                                                    =
                                                                    let uu____5963
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____5963.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____5962
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____5988
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____5988
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____5995
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____5995
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____6015
                                                                    =
                                                                    let uu____6016
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____6016]
                                                                     in
                                                                    let uu____6017
                                                                    =
                                                                    let uu____6028
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____6028]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6015;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6017;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____6053
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____6053))
                                                                    | 
                                                                    uu____6056
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____6058
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                    else
                                                                    (let uu____6080
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____6080))
                                                                     in
                                                                    match uu____6058
                                                                    with
                                                                    | 
                                                                    (univs1,act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env3
                                                                    act_typ3
                                                                     in
                                                                    let act_typ5
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    univs1
                                                                    act_typ4
                                                                     in
                                                                    let uu___392_6099
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___392_6099.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___392_6099.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___392_6099.FStar_Syntax_Syntax.action_params);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                    }))))))
                                               in
                                            FStar_All.pipe_right
                                              ed2.FStar_Syntax_Syntax.actions
                                              (FStar_List.map check_action)
                                             in
                                          (repr, bind_repr, return_repr,
                                            actions)
                                       in
                                    match uu____4759 with
                                    | (repr,bind_repr,return_repr,actions) ->
                                        let t0 =
                                          let uu____6123 =
                                            FStar_Syntax_Syntax.mk_Total
                                              signature1
                                             in
                                          FStar_Syntax_Util.arrow
                                            ed2.FStar_Syntax_Syntax.binders
                                            uu____6123
                                           in
                                        let uu____6126 =
                                          let uu____6131 =
                                            FStar_TypeChecker_Util.generalize_universes
                                              env0 t0
                                             in
                                          match uu____6131 with
                                          | (gen_univs,t) ->
                                              (match annotated_univ_names
                                               with
                                               | [] -> (gen_univs, t)
                                               | uu____6150 ->
                                                   let uu____6153 =
                                                     ((FStar_List.length
                                                         gen_univs)
                                                        =
                                                        (FStar_List.length
                                                           annotated_univ_names))
                                                       &&
                                                       (FStar_List.forall2
                                                          (fun u1  ->
                                                             fun u2  ->
                                                               let uu____6160
                                                                 =
                                                                 FStar_Syntax_Syntax.order_univ_name
                                                                   u1 u2
                                                                  in
                                                               uu____6160 =
                                                                 (Prims.parse_int "0"))
                                                          gen_univs
                                                          annotated_univ_names)
                                                      in
                                                   if uu____6153
                                                   then (gen_univs, t)
                                                   else
                                                     (let uu____6171 =
                                                        let uu____6177 =
                                                          let uu____6179 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 annotated_univ_names)
                                                             in
                                                          let uu____6181 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 gen_univs)
                                                             in
                                                          FStar_Util.format2
                                                            "Expected an effect definition with %s universes; but found %s"
                                                            uu____6179
                                                            uu____6181
                                                           in
                                                        (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                          uu____6177)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____6171
                                                        signature1.FStar_Syntax_Syntax.pos))
                                           in
                                        (match uu____6126 with
                                         | (univs1,t) ->
                                             let signature2 =
                                               let uu____6192 =
                                                 let uu____6205 =
                                                   let uu____6206 =
                                                     FStar_Syntax_Subst.compress
                                                       t
                                                      in
                                                   uu____6206.FStar_Syntax_Syntax.n
                                                    in
                                                 (effect_params, uu____6205)
                                                  in
                                               match uu____6192 with
                                               | ([],uu____6217) -> t
                                               | (uu____6232,FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____6233,c)) ->
                                                   FStar_Syntax_Util.comp_result
                                                     c
                                               | uu____6271 ->
                                                   failwith
                                                     "Impossible : t is an arrow"
                                                in
                                             let close1 n1 ts =
                                               let ts1 =
                                                 let uu____6299 =
                                                   FStar_Syntax_Subst.close_tscheme
                                                     effect_params ts
                                                    in
                                                 FStar_Syntax_Subst.close_univ_vars_tscheme
                                                   univs1 uu____6299
                                                  in
                                               let m =
                                                 FStar_List.length
                                                   (FStar_Pervasives_Native.fst
                                                      ts1)
                                                  in
                                               (let uu____6306 =
                                                  ((n1 >=
                                                      (Prims.parse_int "0"))
                                                     &&
                                                     (let uu____6310 =
                                                        FStar_Syntax_Util.is_unknown
                                                          (FStar_Pervasives_Native.snd
                                                             ts1)
                                                         in
                                                      Prims.op_Negation
                                                        uu____6310))
                                                    && (m <> n1)
                                                   in
                                                if uu____6306
                                                then
                                                  let error =
                                                    if m < n1
                                                    then
                                                      "not universe-polymorphic enough"
                                                    else
                                                      "too universe-polymorphic"
                                                     in
                                                  let err_msg =
                                                    let uu____6338 =
                                                      FStar_Util.string_of_int
                                                        m
                                                       in
                                                    let uu____6346 =
                                                      FStar_Util.string_of_int
                                                        n1
                                                       in
                                                    let uu____6348 =
                                                      FStar_Syntax_Print.tscheme_to_string
                                                        ts1
                                                       in
                                                    FStar_Util.format4
                                                      "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                      error uu____6338
                                                      uu____6346 uu____6348
                                                     in
                                                  FStar_Errors.raise_error
                                                    (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                      err_msg)
                                                    (FStar_Pervasives_Native.snd
                                                       ts1).FStar_Syntax_Syntax.pos
                                                else ());
                                               ts1  in
                                             let close_action act =
                                               let uu____6364 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               match uu____6364 with
                                               | (univs2,defn) ->
                                                   let uu____6380 =
                                                     close1
                                                       (~-
                                                          (Prims.parse_int "1"))
                                                       ((act.FStar_Syntax_Syntax.action_univs),
                                                         (act.FStar_Syntax_Syntax.action_typ))
                                                      in
                                                   (match uu____6380 with
                                                    | (univs',typ) ->
                                                        let uu___393_6397 =
                                                          act  in
                                                        {
                                                          FStar_Syntax_Syntax.action_name
                                                            =
                                                            (uu___393_6397.FStar_Syntax_Syntax.action_name);
                                                          FStar_Syntax_Syntax.action_unqualified_name
                                                            =
                                                            (uu___393_6397.FStar_Syntax_Syntax.action_unqualified_name);
                                                          FStar_Syntax_Syntax.action_univs
                                                            = univs2;
                                                          FStar_Syntax_Syntax.action_params
                                                            =
                                                            (uu___393_6397.FStar_Syntax_Syntax.action_params);
                                                          FStar_Syntax_Syntax.action_defn
                                                            = defn;
                                                          FStar_Syntax_Syntax.action_typ
                                                            = typ
                                                        })
                                                in
                                             let ed3 =
                                               let uu___394_6400 = ed2  in
                                               let uu____6401 =
                                                 let uu____6402 =
                                                   close1
                                                     (Prims.parse_int "0")
                                                     return_wp
                                                    in
                                                 let uu____6404 =
                                                   close1
                                                     (Prims.parse_int "1")
                                                     bind_wp
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     =
                                                     FStar_Syntax_Syntax.tun;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____6402;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____6404
                                                 }  in
                                               let uu____6406 =
                                                 close1 (Prims.parse_int "0")
                                                   if_then_else1
                                                  in
                                               let uu____6408 =
                                                 close1 (Prims.parse_int "0")
                                                   ite_wp
                                                  in
                                               let uu____6410 =
                                                 close1 (Prims.parse_int "0")
                                                   stronger
                                                  in
                                               let uu____6412 =
                                                 close1 (Prims.parse_int "1")
                                                   close_wp
                                                  in
                                               let uu____6414 =
                                                 close1 (Prims.parse_int "0")
                                                   assert_p
                                                  in
                                               let uu____6416 =
                                                 close1 (Prims.parse_int "0")
                                                   assume_p
                                                  in
                                               let uu____6418 =
                                                 close1 (Prims.parse_int "0")
                                                   null_wp
                                                  in
                                               let uu____6420 =
                                                 close1 (Prims.parse_int "0")
                                                   trivial_wp
                                                  in
                                               let uu____6422 =
                                                 let uu____6423 =
                                                   let uu____6424 =
                                                     close1
                                                       (Prims.parse_int "0")
                                                       ([], repr)
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____6424
                                                    in
                                                 let uu____6442 =
                                                   close1
                                                     (Prims.parse_int "0")
                                                     return_repr
                                                    in
                                                 let uu____6444 =
                                                   close1
                                                     (Prims.parse_int "1")
                                                     bind_repr
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     = uu____6423;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____6442;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____6444
                                                 }  in
                                               let uu____6446 =
                                                 FStar_List.map close_action
                                                   actions
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.cattributes
                                                   =
                                                   (uu___394_6400.FStar_Syntax_Syntax.cattributes);
                                                 FStar_Syntax_Syntax.mname =
                                                   (uu___394_6400.FStar_Syntax_Syntax.mname);
                                                 FStar_Syntax_Syntax.univs =
                                                   univs1;
                                                 FStar_Syntax_Syntax.binders
                                                   = effect_params;
                                                 FStar_Syntax_Syntax.spec =
                                                   uu____6401;
                                                 FStar_Syntax_Syntax.signature
                                                   = signature2;
                                                 FStar_Syntax_Syntax.if_then_else
                                                   = uu____6406;
                                                 FStar_Syntax_Syntax.ite_wp =
                                                   uu____6408;
                                                 FStar_Syntax_Syntax.stronger
                                                   = uu____6410;
                                                 FStar_Syntax_Syntax.close_wp
                                                   = uu____6412;
                                                 FStar_Syntax_Syntax.assert_p
                                                   = uu____6414;
                                                 FStar_Syntax_Syntax.assume_p
                                                   = uu____6416;
                                                 FStar_Syntax_Syntax.null_wp
                                                   = uu____6418;
                                                 FStar_Syntax_Syntax.trivial
                                                   = uu____6420;
                                                 FStar_Syntax_Syntax.repr =
                                                   uu____6422;
                                                 FStar_Syntax_Syntax.elaborated
                                                   =
                                                   (uu___394_6400.FStar_Syntax_Syntax.elaborated);
                                                 FStar_Syntax_Syntax.actions
                                                   = uu____6446;
                                                 FStar_Syntax_Syntax.eff_attrs
                                                   =
                                                   (uu___394_6400.FStar_Syntax_Syntax.eff_attrs)
                                               }  in
                                             ed3)))))))))
  
let tc_lex_t :
  'Auu____6460 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____6460 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____6495 = FStar_List.hd ses  in
            uu____6495.FStar_Syntax_Syntax.sigrng  in
          (match lids with
           | lex_t1::lex_top1::lex_cons::[] when
               ((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid)
                  &&
                  (FStar_Ident.lid_equals lex_top1
                     FStar_Parser_Const.lextop_lid))
                 &&
                 (FStar_Ident.lid_equals lex_cons
                    FStar_Parser_Const.lexcons_lid)
               -> ()
           | uu____6500 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____6506,[],t,uu____6508,uu____6509);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____6511;
               FStar_Syntax_Syntax.sigattrs = uu____6512;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____6514,_t_top,_lex_t_top,_0_1,uu____6517);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____6519;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____6520;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____6522,_t_cons,_lex_t_cons,_0_2,uu____6525);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____6527;
                 FStar_Syntax_Syntax.sigattrs = uu____6528;_}::[]
               when
               ((_0_1 = (Prims.parse_int "0")) &&
                  (_0_2 = (Prims.parse_int "0")))
                 &&
                 (((FStar_Ident.lid_equals lex_t1
                      FStar_Parser_Const.lex_t_lid)
                     &&
                     (FStar_Ident.lid_equals lex_top1
                        FStar_Parser_Const.lextop_lid))
                    &&
                    (FStar_Ident.lid_equals lex_cons
                       FStar_Parser_Const.lexcons_lid))
               ->
               let u =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r)
                  in
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_type
                      (FStar_Syntax_Syntax.U_name u))
                   FStar_Pervasives_Native.None r
                  in
               let t2 = FStar_Syntax_Subst.close_univ_vars [u] t1  in
               let tc =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_inductive_typ
                        (lex_t1, [u], [], t2, [],
                          [FStar_Parser_Const.lextop_lid;
                          FStar_Parser_Const.lexcons_lid]));
                   FStar_Syntax_Syntax.sigrng = r;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let utop =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r1)
                  in
               let lex_top_t =
                 let uu____6579 =
                   let uu____6586 =
                     let uu____6587 =
                       let uu____6594 =
                         let uu____6597 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____6597
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____6594, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____6587  in
                   FStar_Syntax_Syntax.mk uu____6586  in
                 uu____6579 FStar_Pervasives_Native.None r1  in
               let lex_top_t1 =
                 FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t  in
               let dc_lextop =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_top1, [utop], lex_top_t1,
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.parse_int "0"), []));
                   FStar_Syntax_Syntax.sigrng = r1;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let ucons1 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2)
                  in
               let ucons2 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2)
                  in
               let lex_cons_t =
                 let a =
                   let uu____6615 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6615
                    in
                 let hd1 =
                   let uu____6617 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6617
                    in
                 let tl1 =
                   let uu____6619 =
                     let uu____6620 =
                       let uu____6627 =
                         let uu____6628 =
                           let uu____6635 =
                             let uu____6638 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____6638
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____6635, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____6628  in
                       FStar_Syntax_Syntax.mk uu____6627  in
                     uu____6620 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6619
                    in
                 let res =
                   let uu____6647 =
                     let uu____6654 =
                       let uu____6655 =
                         let uu____6662 =
                           let uu____6665 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____6665
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____6662,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____6655  in
                     FStar_Syntax_Syntax.mk uu____6654  in
                   uu____6647 FStar_Pervasives_Native.None r2  in
                 let uu____6671 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____6671
                  in
               let lex_cons_t1 =
                 FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                   lex_cons_t
                  in
               let dc_lexcons =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_cons, [ucons1; ucons2], lex_cons_t1,
                          FStar_Parser_Const.lex_t_lid,
                          (Prims.parse_int "0"), []));
                   FStar_Syntax_Syntax.sigrng = r2;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let uu____6710 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____6710;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____6715 ->
               let err_msg =
                 let uu____6720 =
                   let uu____6722 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____6722  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____6720
                  in
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT, err_msg)
                 err_range)
  
let (tc_type_common :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Syntax_Syntax.typ ->
        FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun uu____6747  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____6747 with
          | (uvs,t) ->
              let uu____6760 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____6760 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____6772 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____6772 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____6790 =
                        let uu____6793 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____6793
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____6790)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____6816 =
          let uu____6817 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____6817 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____6816 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____6842 =
          let uu____6843 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____6843 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____6842 r
  
let (tc_inductive' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          (let uu____6892 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____6892
           then
             let uu____6895 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____6895
           else ());
          (let uu____6900 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____6900 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____6931 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____6931 FStar_List.flatten  in
               ((let uu____6945 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____6948 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____6948)
                    in
                 if uu____6945
                 then ()
                 else
                   (let env1 =
                      FStar_TypeChecker_Env.push_sigelt env sig_bndle  in
                    FStar_List.iter
                      (fun ty  ->
                         let b =
                           FStar_TypeChecker_TcInductive.check_positivity ty
                             env1
                            in
                         if Prims.op_Negation b
                         then
                           let uu____6964 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____6974,uu____6975,uu____6976,uu____6977,uu____6978)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____6987 -> failwith "Impossible!"  in
                           match uu____6964 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.strcat "Inductive type "
                                      (Prims.strcat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____7006 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____7016,uu____7017,ty_lid,uu____7019,uu____7020)
                               -> (data_lid, ty_lid)
                           | uu____7027 -> failwith "Impossible"  in
                         match uu____7006 with
                         | (data_lid,ty_lid) ->
                             let uu____7035 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____7038 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____7038)
                                in
                             if uu____7035
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.strcat "Exception "
                                      (Prims.strcat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____7052 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____7057,uu____7058,uu____7059,uu____7060,uu____7061)
                         -> lid
                     | uu____7070 -> failwith "Impossible"  in
                   FStar_List.existsb
                     (fun s  ->
                        s = (lid.FStar_Ident.ident).FStar_Ident.idText)
                     FStar_TypeChecker_TcInductive.early_prims_inductives
                    in
                 let is_noeq =
                   FStar_List.existsb
                     (fun q  -> q = FStar_Syntax_Syntax.Noeq) quals
                    in
                 let res =
                   let uu____7088 =
                     (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____7088
                   then (sig_bndle, data_ops_ses)
                   else
                     (let is_unopteq =
                        FStar_List.existsb
                          (fun q  -> q = FStar_Syntax_Syntax.Unopteq) quals
                         in
                      let ses1 =
                        if is_unopteq
                        then
                          FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                            sig_bndle tcs datas env
                        else
                          FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                            sig_bndle tcs datas env
                         in
                      (sig_bndle, (FStar_List.append ses1 data_ops_ses)))
                    in
                 res)))
  
let (tc_inductive :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Ident.lident Prims.list ->
          (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
            Prims.list))
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let env1 = FStar_TypeChecker_Env.push env "tc_inductive"  in
          let pop1 uu____7163 =
            let uu____7164 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___396_7174  ->
               match () with
               | () ->
                   let uu____7181 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____7181 (fun r  -> pop1 (); r)) ()
          with | uu___395_7212 -> (pop1 (); FStar_Exn.raise uu___395_7212)
  
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en  ->
    let env =
      let uu____7233 = FStar_Options.using_facts_from ()  in
      FStar_TypeChecker_Env.set_proof_ns uu____7233 en  in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh (); env
  
let (get_fail_se :
  FStar_Syntax_Syntax.sigelt ->
    (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun se  ->
    let comb f1 f2 =
      match (f1, f2) with
      | (FStar_Pervasives_Native.Some (e1,l1),FStar_Pervasives_Native.Some
         (e2,l2)) ->
          FStar_Pervasives_Native.Some
            ((FStar_List.append e1 e2), (l1 || l2))
      | (FStar_Pervasives_Native.Some (e,l),FStar_Pervasives_Native.None ) ->
          FStar_Pervasives_Native.Some (e, l)
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some (e,l)) ->
          FStar_Pervasives_Native.Some (e, l)
      | uu____7537 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____7595 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____7595 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____7620 .
    'Auu____7620 FStar_Pervasives_Native.option -> 'Auu____7620 Prims.list
  =
  fun uu___374_7629  ->
    match uu___374_7629 with
    | FStar_Pervasives_Native.None  -> []
    | FStar_Pervasives_Native.Some x -> [x]
  
let (check_multi_contained :
  Prims.int Prims.list ->
    Prims.int Prims.list ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option)
  =
  fun l1  ->
    fun l2  ->
      let rec collect1 l =
        match l with
        | [] -> []
        | hd1::tl1 ->
            let uu____7709 = collect1 tl1  in
            (match uu____7709 with
             | [] -> [(hd1, (Prims.parse_int "1"))]
             | (h,n1)::t ->
                 if h = hd1
                 then (h, (n1 + (Prims.parse_int "1"))) :: t
                 else (hd1, (Prims.parse_int "1")) :: (h, n1) :: t)
         in
      let summ l = collect1 l  in
      let l11 = summ l1  in
      let l21 = summ l2  in
      let rec aux l12 l22 =
        match (l12, l22) with
        | ([],[]) -> FStar_Pervasives_Native.None
        | ((e,n1)::uu____7947,[]) ->
            FStar_Pervasives_Native.Some (e, n1, (Prims.parse_int "0"))
        | ([],(e,n1)::uu____8003) ->
            FStar_Pervasives_Native.Some (e, (Prims.parse_int "0"), n1)
        | ((hd1,n1)::tl1,(hd2,n2)::tl2) when hd1 <> hd2 ->
            FStar_Pervasives_Native.Some (hd1, n1, (Prims.parse_int "0"))
        | ((hd1,n1)::tl1,(hd2,n2)::tl2) ->
            if n1 <> n2
            then FStar_Pervasives_Native.Some (hd1, n1, n2)
            else aux tl1 tl2
         in
      aux l11 l21
  
let (check_must_erase_attribute :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
          let uu____8231 =
            let uu____8233 = FStar_Options.ide ()  in
            Prims.op_Negation uu____8233  in
          if uu____8231
          then
            let uu____8236 =
              let uu____8241 = FStar_TypeChecker_Env.dsenv env  in
              let uu____8242 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____8241 uu____8242  in
            (match uu____8236 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some iface_decls1 ->
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.iter
                      (fun lb  ->
                         let lbname =
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                         let has_iface_val =
                           FStar_All.pipe_right iface_decls1
                             (FStar_Util.for_some
                                (FStar_Parser_AST.decl_is_val
                                   ((lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident))
                            in
                         if has_iface_val
                         then
                           let must_erase =
                             FStar_TypeChecker_Util.must_erase_for_extraction
                               env lb.FStar_Syntax_Syntax.lbdef
                              in
                           let has_attr =
                             FStar_TypeChecker_Env.fv_has_attr env lbname
                               FStar_Parser_Const.must_erase_for_extraction_attr
                              in
                           (if must_erase && (Prims.op_Negation has_attr)
                            then
                              let uu____8275 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____8276 =
                                let uu____8282 =
                                  let uu____8284 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____8286 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____8284 uu____8286
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____8282)
                                 in
                              FStar_Errors.log_issue uu____8275 uu____8276
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____8293 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____8294 =
                                   let uu____8300 =
                                     let uu____8302 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____8302
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____8300)
                                    in
                                 FStar_Errors.log_issue uu____8293 uu____8294)
                              else ())
                         else ())))
          else ()
      | uu____8312 -> ()
  
let (tc_decl' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env0  ->
    fun se  ->
      let env = env0  in
      FStar_TypeChecker_Util.check_sigelt_quals env se;
      (let r = se.FStar_Syntax_Syntax.sigrng  in
       match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____8357 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____8385 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) when
           FStar_All.pipe_right lids
             (FStar_Util.for_some
                (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))
           ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let se1 = tc_lex_t env1 ses se.FStar_Syntax_Syntax.sigquals lids
              in
           ([se1], [], env0)
       | FStar_Syntax_Syntax.Sig_bundle (ses,lids) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let ses1 =
             let uu____8445 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____8445
             then
               let ses1 =
                 let uu____8453 =
                   let uu____8454 =
                     let uu____8455 =
                       tc_inductive
                         (let uu___397_8464 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___397_8464.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___397_8464.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___397_8464.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___397_8464.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___397_8464.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___397_8464.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___397_8464.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___397_8464.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___397_8464.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___397_8464.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___397_8464.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___397_8464.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___397_8464.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___397_8464.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___397_8464.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___397_8464.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___397_8464.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___397_8464.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___397_8464.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___397_8464.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___397_8464.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___397_8464.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___397_8464.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___397_8464.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___397_8464.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___397_8464.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___397_8464.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___397_8464.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___397_8464.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___397_8464.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___397_8464.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___397_8464.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___397_8464.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___397_8464.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___397_8464.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___397_8464.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___397_8464.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___397_8464.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___397_8464.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___397_8464.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___397_8464.FStar_TypeChecker_Env.nbe)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____8455
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____8454
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____8453
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____8478 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____8478
                 then
                   let uu____8483 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___398_8487 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___398_8487.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___398_8487.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___398_8487.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___398_8487.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____8483
                 else ());
                ses1)
             else ses  in
           let uu____8497 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____8497 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___399_8521 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___399_8521.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___399_8521.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___399_8521.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___399_8521.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let forfree =
             let uu____8535 =
               let uu____8536 =
                 FStar_Syntax_Subst.compress
                   (ne.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                  in
               uu____8536.FStar_Syntax_Syntax.n  in
             match uu____8535 with
             | FStar_Syntax_Syntax.Tm_unknown  -> false
             | uu____8541 ->
                 Prims.op_Negation ne.FStar_Syntax_Syntax.elaborated
              in
           if forfree
           then
             ((let uu____8554 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____8554
               then FStar_Util.print_string "Beginning DM4F run\n"
               else ());
              (let uu____8561 = cps_and_elaborate_ed env0 ne  in
               match uu____8561 with
               | (ses,ne1,lift_from_pure_opt) ->
                   let ne2 =
                     let uu___400_8594 = ne1  in
                     {
                       FStar_Syntax_Syntax.cattributes =
                         (uu___400_8594.FStar_Syntax_Syntax.cattributes);
                       FStar_Syntax_Syntax.mname =
                         (uu___400_8594.FStar_Syntax_Syntax.mname);
                       FStar_Syntax_Syntax.univs =
                         (uu___400_8594.FStar_Syntax_Syntax.univs);
                       FStar_Syntax_Syntax.binders =
                         (uu___400_8594.FStar_Syntax_Syntax.binders);
                       FStar_Syntax_Syntax.spec =
                         (uu___400_8594.FStar_Syntax_Syntax.spec);
                       FStar_Syntax_Syntax.signature =
                         (uu___400_8594.FStar_Syntax_Syntax.signature);
                       FStar_Syntax_Syntax.if_then_else =
                         (uu___400_8594.FStar_Syntax_Syntax.if_then_else);
                       FStar_Syntax_Syntax.ite_wp =
                         (uu___400_8594.FStar_Syntax_Syntax.ite_wp);
                       FStar_Syntax_Syntax.stronger =
                         (uu___400_8594.FStar_Syntax_Syntax.stronger);
                       FStar_Syntax_Syntax.close_wp =
                         (uu___400_8594.FStar_Syntax_Syntax.close_wp);
                       FStar_Syntax_Syntax.assert_p =
                         (uu___400_8594.FStar_Syntax_Syntax.assert_p);
                       FStar_Syntax_Syntax.assume_p =
                         (uu___400_8594.FStar_Syntax_Syntax.assume_p);
                       FStar_Syntax_Syntax.null_wp =
                         (uu___400_8594.FStar_Syntax_Syntax.null_wp);
                       FStar_Syntax_Syntax.trivial =
                         (uu___400_8594.FStar_Syntax_Syntax.trivial);
                       FStar_Syntax_Syntax.repr =
                         (uu___400_8594.FStar_Syntax_Syntax.repr);
                       FStar_Syntax_Syntax.elaborated = true;
                       FStar_Syntax_Syntax.actions =
                         (uu___400_8594.FStar_Syntax_Syntax.actions);
                       FStar_Syntax_Syntax.eff_attrs =
                         (uu___400_8594.FStar_Syntax_Syntax.eff_attrs)
                     }  in
                   let effect_and_lift_ses =
                     match lift_from_pure_opt with
                     | FStar_Pervasives_Native.Some lift ->
                         [(let uu___401_8603 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne2);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___401_8603.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___401_8603.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___401_8603.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___401_8603.FStar_Syntax_Syntax.sigattrs)
                           });
                         lift]
                     | FStar_Pervasives_Native.None  ->
                         [(let uu___402_8605 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne2);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___402_8605.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___402_8605.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___402_8605.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___402_8605.FStar_Syntax_Syntax.sigattrs)
                           })]
                      in
                   ([], (FStar_List.append ses effect_and_lift_ses), env0)))
           else
             (let ne1 =
                let uu____8613 =
                  (FStar_Options.use_two_phase_tc ()) &&
                    (FStar_TypeChecker_Env.should_verify env)
                   in
                if uu____8613
                then
                  let ne1 =
                    let uu____8617 =
                      let uu____8618 =
                        let uu____8619 =
                          tc_eff_decl
                            (let uu___403_8621 = env  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___403_8621.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___403_8621.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___403_8621.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___403_8621.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___403_8621.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___403_8621.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___403_8621.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___403_8621.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___403_8621.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___403_8621.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___403_8621.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___403_8621.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___403_8621.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___403_8621.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___403_8621.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___403_8621.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___403_8621.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___403_8621.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___403_8621.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___403_8621.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___403_8621.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 = true;
                               FStar_TypeChecker_Env.failhard =
                                 (uu___403_8621.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___403_8621.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___403_8621.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___403_8621.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___403_8621.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___403_8621.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___403_8621.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___403_8621.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___403_8621.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___403_8621.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___403_8621.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___403_8621.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___403_8621.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___403_8621.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___403_8621.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___403_8621.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___403_8621.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___403_8621.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___403_8621.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___403_8621.FStar_TypeChecker_Env.nbe)
                             }) se ne
                           in
                        FStar_All.pipe_right uu____8619
                          (fun ne1  ->
                             let uu___404_8627 = se  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___404_8627.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___404_8627.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___404_8627.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___404_8627.FStar_Syntax_Syntax.sigattrs)
                             })
                         in
                      FStar_All.pipe_right uu____8618
                        (FStar_TypeChecker_Normalize.elim_uvars env)
                       in
                    FStar_All.pipe_right uu____8617
                      FStar_Syntax_Util.eff_decl_of_new_effect
                     in
                  ((let uu____8629 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "TwoPhases")
                       in
                    if uu____8629
                    then
                      let uu____8634 =
                        FStar_Syntax_Print.sigelt_to_string
                          (let uu___405_8638 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne1);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___405_8638.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___405_8638.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___405_8638.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___405_8638.FStar_Syntax_Syntax.sigattrs)
                           })
                         in
                      FStar_Util.print1 "Effect decl after phase 1: %s\n"
                        uu____8634
                    else ());
                   ne1)
                else ne  in
              let ne2 = tc_eff_decl env se ne1  in
              let se1 =
                let uu___406_8646 = se  in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_new_effect ne2);
                  FStar_Syntax_Syntax.sigrng =
                    (uu___406_8646.FStar_Syntax_Syntax.sigrng);
                  FStar_Syntax_Syntax.sigquals =
                    (uu___406_8646.FStar_Syntax_Syntax.sigquals);
                  FStar_Syntax_Syntax.sigmeta =
                    (uu___406_8646.FStar_Syntax_Syntax.sigmeta);
                  FStar_Syntax_Syntax.sigattrs =
                    (uu___406_8646.FStar_Syntax_Syntax.sigattrs)
                }  in
              ([se1], [], env0))
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.source
              in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.target
              in
           let uu____8654 =
             let uu____8661 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____8661
              in
           (match uu____8654 with
            | (a,wp_a_src) ->
                let uu____8678 =
                  let uu____8685 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____8685
                   in
                (match uu____8678 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____8703 =
                         let uu____8706 =
                           let uu____8707 =
                             let uu____8714 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____8714)  in
                           FStar_Syntax_Syntax.NT uu____8707  in
                         [uu____8706]  in
                       FStar_Syntax_Subst.subst uu____8703 wp_b_tgt  in
                     let expected_k =
                       let uu____8722 =
                         let uu____8731 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____8738 =
                           let uu____8747 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____8747]  in
                         uu____8731 :: uu____8738  in
                       let uu____8772 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____8722 uu____8772  in
                     let repr_type eff_name a1 wp =
                       (let uu____8794 =
                          let uu____8796 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____8796  in
                        if uu____8794
                        then
                          let uu____8799 =
                            let uu____8805 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____8805)
                             in
                          let uu____8809 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____8799 uu____8809
                        else ());
                       (let uu____8812 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____8812 with
                        | FStar_Pervasives_Native.None  ->
                            failwith
                              "internal error: reifiable effect has no decl?"
                        | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                            let repr =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                [FStar_Syntax_Syntax.U_unknown] env ed
                                ([],
                                  ((ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m))
                               in
                            let uu____8849 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____8850 =
                              let uu____8857 =
                                let uu____8858 =
                                  let uu____8875 =
                                    let uu____8886 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____8895 =
                                      let uu____8906 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____8906]  in
                                    uu____8886 :: uu____8895  in
                                  (repr, uu____8875)  in
                                FStar_Syntax_Syntax.Tm_app uu____8858  in
                              FStar_Syntax_Syntax.mk uu____8857  in
                            uu____8850 FStar_Pervasives_Native.None
                              uu____8849)
                        in
                     let uu____8954 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____9127 =
                             if
                               (FStar_List.length uvs) >
                                 (Prims.parse_int "0")
                             then
                               let uu____9138 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____9138 with
                               | (usubst,uvs1) ->
                                   let uu____9161 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____9162 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____9161, uu____9162)
                             else (env, lift_wp)  in
                           (match uu____9127 with
                            | (env1,lift_wp1) ->
                                let lift_wp2 =
                                  if
                                    (FStar_List.length uvs) =
                                      (Prims.parse_int "0")
                                  then check_and_gen env1 lift_wp1 expected_k
                                  else
                                    (let lift_wp2 =
                                       tc_check_trivial_guard env1 lift_wp1
                                         expected_k
                                        in
                                     let uu____9212 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____9212))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____9283 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____9298 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____9298 with
                               | (usubst,uvs) ->
                                   let uu____9323 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____9323)
                             else ([], lift)  in
                           (match uu____9283 with
                            | (uvs,lift1) ->
                                ((let uu____9359 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____9359
                                  then
                                    let uu____9363 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____9363
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____9369 =
                                    let uu____9376 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____9376 lift1
                                     in
                                  match uu____9369 with
                                  | (lift2,comp,uu____9401) ->
                                      let uu____9402 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____9402 with
                                       | (uu____9431,lift_wp,lift_elab) ->
                                           let lift_wp1 =
                                             recheck_debug "lift-wp" env
                                               lift_wp
                                              in
                                           let lift_elab1 =
                                             recheck_debug "lift-elab" env
                                               lift_elab
                                              in
                                           if
                                             (FStar_List.length uvs) =
                                               (Prims.parse_int "0")
                                           then
                                             let uu____9463 =
                                               let uu____9474 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____9474
                                                in
                                             let uu____9491 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____9463, uu____9491)
                                           else
                                             (let uu____9520 =
                                                let uu____9531 =
                                                  let uu____9540 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____9540)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____9531
                                                 in
                                              let uu____9555 =
                                                let uu____9564 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____9564)  in
                                              (uu____9520, uu____9555))))))
                        in
                     (match uu____8954 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___407_9638 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___407_9638.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___407_9638.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___407_9638.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___407_9638.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___407_9638.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___407_9638.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___407_9638.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___407_9638.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___407_9638.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___407_9638.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___407_9638.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___407_9638.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___407_9638.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___407_9638.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___407_9638.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___407_9638.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___407_9638.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___407_9638.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___407_9638.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___407_9638.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___407_9638.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___407_9638.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___407_9638.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___407_9638.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___407_9638.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___407_9638.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___407_9638.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___407_9638.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___407_9638.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___407_9638.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___407_9638.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___407_9638.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___407_9638.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___407_9638.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___407_9638.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___407_9638.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___407_9638.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___407_9638.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___407_9638.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___407_9638.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___407_9638.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___407_9638.FStar_TypeChecker_Env.nbe)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____9671 =
                                  let uu____9676 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____9676 with
                                  | (usubst,uvs1) ->
                                      let uu____9699 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____9700 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____9699, uu____9700)
                                   in
                                (match uu____9671 with
                                 | (env2,lift2) ->
                                     let uu____9705 =
                                       let uu____9712 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____9712
                                        in
                                     (match uu____9705 with
                                      | (a1,wp_a_src1) ->
                                          let wp_a =
                                            FStar_Syntax_Syntax.new_bv
                                              FStar_Pervasives_Native.None
                                              wp_a_src1
                                             in
                                          let a_typ =
                                            FStar_Syntax_Syntax.bv_to_name a1
                                             in
                                          let wp_a_typ =
                                            FStar_Syntax_Syntax.bv_to_name
                                              wp_a
                                             in
                                          let repr_f =
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.source
                                              a_typ wp_a_typ
                                             in
                                          let repr_result =
                                            let lift_wp1 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Env.EraseUniverses;
                                                FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                env2
                                                (FStar_Pervasives_Native.snd
                                                   lift_wp)
                                               in
                                            let lift_wp_a =
                                              let uu____9738 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____9739 =
                                                let uu____9746 =
                                                  let uu____9747 =
                                                    let uu____9764 =
                                                      let uu____9775 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____9784 =
                                                        let uu____9795 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____9795]  in
                                                      uu____9775 ::
                                                        uu____9784
                                                       in
                                                    (lift_wp1, uu____9764)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____9747
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____9746
                                                 in
                                              uu____9739
                                                FStar_Pervasives_Native.None
                                                uu____9738
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____9846 =
                                              let uu____9855 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____9862 =
                                                let uu____9871 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____9878 =
                                                  let uu____9887 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____9887]  in
                                                uu____9871 :: uu____9878  in
                                              uu____9855 :: uu____9862  in
                                            let uu____9918 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____9846 uu____9918
                                             in
                                          let uu____9921 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____9921 with
                                           | (expected_k2,uu____9931,uu____9932)
                                               ->
                                               let lift3 =
                                                 if
                                                   (FStar_List.length uvs) =
                                                     (Prims.parse_int "0")
                                                 then
                                                   check_and_gen env2 lift2
                                                     expected_k2
                                                 else
                                                   (let lift3 =
                                                      tc_check_trivial_guard
                                                        env2 lift2
                                                        expected_k2
                                                       in
                                                    let uu____9940 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____9940))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____9948 =
                              let uu____9950 =
                                let uu____9952 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____9952
                                  FStar_List.length
                                 in
                              uu____9950 <> (Prims.parse_int "1")  in
                            if uu____9948
                            then
                              let uu____9974 =
                                let uu____9980 =
                                  let uu____9982 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____9984 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____9986 =
                                    let uu____9988 =
                                      let uu____9990 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____9990
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____9988
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____9982 uu____9984 uu____9986
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____9980)
                                 in
                              FStar_Errors.raise_error uu____9974 r
                            else ());
                           (let uu____10017 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____10020 =
                                   let uu____10022 =
                                     let uu____10025 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____10025
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____10022
                                     FStar_List.length
                                    in
                                 uu____10020 <> (Prims.parse_int "1"))
                               in
                            if uu____10017
                            then
                              let uu____10063 =
                                let uu____10069 =
                                  let uu____10071 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10073 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10075 =
                                    let uu____10077 =
                                      let uu____10079 =
                                        let uu____10082 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____10082
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10079
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10077
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10071 uu____10073 uu____10075
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10069)
                                 in
                              FStar_Errors.raise_error uu____10063 r
                            else ());
                           (let sub2 =
                              let uu___408_10125 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___408_10125.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___408_10125.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___409_10127 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___409_10127.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___409_10127.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___409_10127.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___409_10127.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let uu____10141 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (env, uvs, tps, c)
             else
               (let uu____10169 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____10169 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____10200 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____10200 c  in
                    let uu____10209 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____10209, uvs1, tps1, c1))
              in
           (match uu____10141 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____10231 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____10231 with
                 | (tps2,c2) ->
                     let uu____10248 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____10248 with
                      | (tps3,env3,us) ->
                          let uu____10268 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____10268 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____10296)::uu____10297 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____10316 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____10324 =
                                   let uu____10326 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____10326  in
                                 if uu____10324
                                 then
                                   let uu____10329 =
                                     let uu____10335 =
                                       let uu____10337 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____10339 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____10337 uu____10339
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____10335)
                                      in
                                   FStar_Errors.raise_error uu____10329 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____10347 =
                                   let uu____10348 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____10348
                                    in
                                 match uu____10347 with
                                 | (uvs2,t) ->
                                     let uu____10379 =
                                       let uu____10384 =
                                         let uu____10397 =
                                           let uu____10398 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10398.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____10397)  in
                                       match uu____10384 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____10413,c5)) -> ([], c5)
                                       | (uu____10455,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____10494 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____10379 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____10528 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____10528 with
                                              | (uu____10533,t1) ->
                                                  let uu____10535 =
                                                    let uu____10541 =
                                                      let uu____10543 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____10545 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____10549 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____10543
                                                        uu____10545
                                                        uu____10549
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____10541)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____10535 r)
                                           else ();
                                           (let se1 =
                                              let uu___410_10556 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags1));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___410_10556.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___410_10556.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___410_10556.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___410_10556.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____10563,uu____10564,uu____10565) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___375_10570  ->
                   match uu___375_10570 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____10573 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____10579,uu____10580) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___375_10589  ->
                   match uu___375_10589 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____10592 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____10603 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____10603
             then
               let uu____10606 =
                 let uu____10612 =
                   let uu____10614 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____10614
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____10612)
                  in
               FStar_Errors.raise_error uu____10606 r
             else ());
            (let uu____10620 =
               let uu____10629 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____10629
               then
                 let uu____10640 =
                   tc_declare_typ
                     (let uu___411_10643 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___411_10643.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___411_10643.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___411_10643.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___411_10643.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___411_10643.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___411_10643.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___411_10643.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___411_10643.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___411_10643.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___411_10643.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___411_10643.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___411_10643.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___411_10643.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___411_10643.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___411_10643.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___411_10643.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___411_10643.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___411_10643.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___411_10643.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___411_10643.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___411_10643.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___411_10643.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___411_10643.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___411_10643.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___411_10643.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___411_10643.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___411_10643.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___411_10643.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___411_10643.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___411_10643.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___411_10643.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___411_10643.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___411_10643.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___411_10643.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___411_10643.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___411_10643.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___411_10643.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___411_10643.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___411_10643.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___411_10643.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___411_10643.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___411_10643.FStar_TypeChecker_Env.nbe)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____10640 with
                 | (uvs1,t1) ->
                     ((let uu____10668 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____10668
                       then
                         let uu____10673 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____10675 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____10673 uu____10675
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____10620 with
             | (uvs1,t1) ->
                 let uu____10710 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____10710 with
                  | (uvs2,t2) ->
                      ([(let uu___412_10740 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___412_10740.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___412_10740.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___412_10740.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___412_10740.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____10745 =
             let uu____10754 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____10754
             then
               let uu____10765 =
                 tc_assume
                   (let uu___413_10768 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___413_10768.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___413_10768.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___413_10768.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___413_10768.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___413_10768.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___413_10768.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___413_10768.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___413_10768.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___413_10768.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___413_10768.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___413_10768.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___413_10768.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___413_10768.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___413_10768.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___413_10768.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___413_10768.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___413_10768.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___413_10768.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___413_10768.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___413_10768.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___413_10768.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___413_10768.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___413_10768.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___413_10768.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___413_10768.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___413_10768.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___413_10768.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___413_10768.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___413_10768.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___413_10768.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___413_10768.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___413_10768.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___413_10768.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___413_10768.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___413_10768.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___413_10768.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___413_10768.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___413_10768.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___413_10768.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___413_10768.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___413_10768.FStar_TypeChecker_Env.nbe)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____10765 with
               | (uvs1,t1) ->
                   ((let uu____10794 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____10794
                     then
                       let uu____10799 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10801 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____10799
                         uu____10801
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____10745 with
            | (uvs1,t1) ->
                let uu____10836 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____10836 with
                 | (uvs2,t2) ->
                     ([(let uu___414_10866 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___414_10866.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___414_10866.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___414_10866.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___414_10866.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____10870 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____10870 with
            | (e1,c,g1) ->
                let uu____10890 =
                  let uu____10897 =
                    let uu____10900 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____10900  in
                  let uu____10901 =
                    let uu____10906 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____10906)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____10897 uu____10901
                   in
                (match uu____10890 with
                 | (e2,uu____10918,g) ->
                     ((let uu____10921 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____10921);
                      (let se1 =
                         let uu___415_10923 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___415_10923.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___415_10923.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___415_10923.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___415_10923.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____10935 = FStar_Options.debug_any ()  in
             if uu____10935
             then
               let uu____10938 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____10940 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____10938
                 uu____10940
             else ());
            (let uu____10945 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____10945 with
             | (t1,uu____10963,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____10977 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____10977 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____10980 =
                              let uu____10986 =
                                let uu____10988 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____10990 =
                                  let uu____10992 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____10992
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____10988 uu____10990
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____10986)
                               in
                            FStar_Errors.raise_error uu____10980 r
                        | uu____11004 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___416_11009 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___416_11009.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___416_11009.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___416_11009.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___416_11009.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___416_11009.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___416_11009.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___416_11009.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___416_11009.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___416_11009.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___416_11009.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___416_11009.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___416_11009.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___416_11009.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___416_11009.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___416_11009.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___416_11009.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___416_11009.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___416_11009.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___416_11009.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___416_11009.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___416_11009.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___416_11009.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___416_11009.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___416_11009.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___416_11009.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___416_11009.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___416_11009.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___416_11009.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___416_11009.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___416_11009.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___416_11009.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___416_11009.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___416_11009.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___416_11009.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___416_11009.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___416_11009.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___416_11009.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___416_11009.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___416_11009.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___416_11009.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___416_11009.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___416_11009.FStar_TypeChecker_Env.nbe)
                      }  in
                    ([], ses, env1))))))
       | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let check_quals_eq l qopt val_q =
             match qopt with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some val_q
             | FStar_Pervasives_Native.Some q' ->
                 let drop_logic =
                   FStar_List.filter
                     (fun x  ->
                        Prims.op_Negation (x = FStar_Syntax_Syntax.Logic))
                    in
                 let uu____11077 =
                   let uu____11079 =
                     let uu____11088 = drop_logic val_q  in
                     let uu____11091 = drop_logic q'  in
                     (uu____11088, uu____11091)  in
                   match uu____11079 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____11077
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____11118 =
                      let uu____11124 =
                        let uu____11126 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____11128 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____11130 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____11126 uu____11128 uu____11130
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____11124)
                       in
                    FStar_Errors.raise_error uu____11118 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____11167 =
                   let uu____11168 = FStar_Syntax_Subst.compress def  in
                   uu____11168.FStar_Syntax_Syntax.n  in
                 match uu____11167 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____11180,uu____11181) -> binders
                 | uu____11206 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____11218;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____11323) -> val_bs1
                     | (uu____11354,[]) -> val_bs1
                     | ((body_bv,uu____11386)::bt,(val_bv,aqual)::vt) ->
                         let uu____11443 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____11467) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___417_11481 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___418_11484 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___418_11484.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___417_11481.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___417_11481.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____11443
                      in
                   let uu____11491 =
                     let uu____11498 =
                       let uu____11499 =
                         let uu____11514 = rename_binders1 def_bs val_bs  in
                         (uu____11514, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____11499  in
                     FStar_Syntax_Syntax.mk uu____11498  in
                   uu____11491 FStar_Pervasives_Native.None r1
               | uu____11536 -> typ1  in
             let uu___419_11537 = lb  in
             let uu____11538 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___419_11537.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___419_11537.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____11538;
               FStar_Syntax_Syntax.lbeff =
                 (uu___419_11537.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___419_11537.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___419_11537.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___419_11537.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____11541 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____11596  ->
                     fun lb  ->
                       match uu____11596 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____11642 =
                             let uu____11654 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____11654 with
                             | FStar_Pervasives_Native.None  ->
                                 if lb.FStar_Syntax_Syntax.lbunivs <> []
                                 then (false, lb, quals_opt)
                                 else (gen1, lb, quals_opt)
                             | FStar_Pervasives_Native.Some
                                 ((uvs,tval),quals) ->
                                 let quals_opt1 =
                                   check_quals_eq
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     quals_opt quals
                                    in
                                 let def =
                                   match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_unknown  ->
                                       lb.FStar_Syntax_Syntax.lbdef
                                   | uu____11734 ->
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_ascribed
                                            ((lb.FStar_Syntax_Syntax.lbdef),
                                              ((FStar_Util.Inl
                                                  (lb.FStar_Syntax_Syntax.lbtyp)),
                                                FStar_Pervasives_Native.None),
                                              FStar_Pervasives_Native.None))
                                         FStar_Pervasives_Native.None
                                         (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.pos
                                    in
                                 (if
                                    (lb.FStar_Syntax_Syntax.lbunivs <> []) &&
                                      ((FStar_List.length
                                          lb.FStar_Syntax_Syntax.lbunivs)
                                         <> (FStar_List.length uvs))
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_IncoherentInlineUniverse,
                                        "Inline universes are incoherent with annotation from val declaration")
                                      r
                                  else ();
                                  (let uu____11781 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____11781, quals_opt1)))
                              in
                           (match uu____11642 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____11541 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____11885 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___376_11891  ->
                                match uu___376_11891 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____11896 -> false))
                         in
                      if uu____11885
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____11909 =
                    let uu____11916 =
                      let uu____11917 =
                        let uu____11931 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____11931)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____11917  in
                    FStar_Syntax_Syntax.mk uu____11916  in
                  uu____11909 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___420_11953 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___420_11953.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___420_11953.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___420_11953.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___420_11953.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___420_11953.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___420_11953.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___420_11953.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___420_11953.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___420_11953.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___420_11953.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___420_11953.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___420_11953.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___420_11953.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___420_11953.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___420_11953.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___420_11953.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___420_11953.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___420_11953.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___420_11953.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___420_11953.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___420_11953.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___420_11953.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___420_11953.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___420_11953.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___420_11953.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___420_11953.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___420_11953.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___420_11953.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___420_11953.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___420_11953.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___420_11953.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___420_11953.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___420_11953.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___420_11953.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___420_11953.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___420_11953.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___420_11953.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___420_11953.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___420_11953.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___420_11953.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___420_11953.FStar_TypeChecker_Env.nbe)
                  }  in
                let e1 =
                  let uu____11956 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____11956
                  then
                    let drop_lbtyp e_lax =
                      let uu____11965 =
                        let uu____11966 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____11966.FStar_Syntax_Syntax.n  in
                      match uu____11965 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____11988 =
                              let uu____11989 = FStar_Syntax_Subst.compress e
                                 in
                              uu____11989.FStar_Syntax_Syntax.n  in
                            match uu____11988 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____11993,lb1::[]),uu____11995) ->
                                let uu____12011 =
                                  let uu____12012 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____12012.FStar_Syntax_Syntax.n  in
                                (match uu____12011 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____12017 -> false)
                            | uu____12019 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___421_12023 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___422_12038 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___422_12038.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___422_12038.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___422_12038.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___422_12038.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___422_12038.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___422_12038.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___421_12023.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___421_12023.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____12041 -> e_lax  in
                    let e1 =
                      let uu____12043 =
                        let uu____12044 =
                          let uu____12045 =
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              (let uu___423_12054 = env'  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___423_12054.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___423_12054.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___423_12054.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___423_12054.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___423_12054.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___423_12054.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___423_12054.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___423_12054.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___423_12054.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___423_12054.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___423_12054.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___423_12054.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___423_12054.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___423_12054.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___423_12054.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___423_12054.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___423_12054.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___423_12054.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___423_12054.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___423_12054.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___423_12054.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 = true;
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___423_12054.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___423_12054.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___423_12054.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___423_12054.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___423_12054.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___423_12054.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___423_12054.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___423_12054.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___423_12054.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___423_12054.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___423_12054.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___423_12054.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___423_12054.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___423_12054.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___423_12054.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___423_12054.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___423_12054.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___423_12054.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___423_12054.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___423_12054.FStar_TypeChecker_Env.nbe)
                               }) e
                             in
                          FStar_All.pipe_right uu____12045
                            (fun uu____12067  ->
                               match uu____12067 with
                               | (e1,uu____12075,uu____12076) -> e1)
                           in
                        FStar_All.pipe_right uu____12044
                          (FStar_TypeChecker_Normalize.remove_uvar_solutions
                             env')
                         in
                      FStar_All.pipe_right uu____12043 drop_lbtyp  in
                    ((let uu____12078 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "TwoPhases")
                         in
                      if uu____12078
                      then
                        let uu____12083 =
                          FStar_Syntax_Print.term_to_string e1  in
                        FStar_Util.print1 "Let binding after phase 1: %s\n"
                          uu____12083
                      else ());
                     e1)
                  else e  in
                let uu____12090 =
                  let uu____12099 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____12099 with
                  | FStar_Pervasives_Native.None  ->
                      ((se.FStar_Syntax_Syntax.sigattrs),
                        FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some
                      (ats,(tau,FStar_Pervasives_Native.None )::[]) ->
                      (ats, (FStar_Pervasives_Native.Some tau))
                  | FStar_Pervasives_Native.Some (ats,args) ->
                      (FStar_Errors.log_issue r
                         (FStar_Errors.Warning_UnrecognizedAttribute,
                           "Ill-formed application of `postprocess_with`");
                       ((se.FStar_Syntax_Syntax.sigattrs),
                         FStar_Pervasives_Native.None))
                   in
                (match uu____12090 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___424_12204 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___424_12204.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___424_12204.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___424_12204.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___424_12204.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___425_12217 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___425_12217.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___425_12217.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___425_12217.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___425_12217.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___425_12217.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___425_12217.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____12218 =
                       let uu____12230 =
                         FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env'
                           e1
                          in
                       match uu____12230 with
                       | ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                            FStar_Syntax_Syntax.pos = uu____12250;
                            FStar_Syntax_Syntax.vars = uu____12251;_},uu____12252,g)
                           when FStar_TypeChecker_Env.is_trivial g ->
                           let lbs2 =
                             let uu____12282 =
                               FStar_All.pipe_right
                                 (FStar_Pervasives_Native.snd lbs1)
                                 (FStar_List.map rename_parameters)
                                in
                             ((FStar_Pervasives_Native.fst lbs1),
                               uu____12282)
                              in
                           let lbs3 =
                             let uu____12306 =
                               match post_tau with
                               | FStar_Pervasives_Native.Some tau ->
                                   FStar_List.map (postprocess_lb tau)
                                     (FStar_Pervasives_Native.snd lbs2)
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.snd lbs2
                                in
                             ((FStar_Pervasives_Native.fst lbs2),
                               uu____12306)
                              in
                           let quals1 =
                             match e2.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_meta
                                 (uu____12329,FStar_Syntax_Syntax.Meta_desugared
                                  (FStar_Syntax_Syntax.Masked_effect ))
                                 -> FStar_Syntax_Syntax.HasMaskedEffect ::
                                 quals
                             | uu____12334 -> quals  in
                           ((let uu___426_12343 = se1  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_let (lbs3, lids));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___426_12343.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals = quals1;
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___426_12343.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___426_12343.FStar_Syntax_Syntax.sigattrs)
                             }), lbs3)
                       | uu____12346 ->
                           failwith
                             "impossible (typechecking should preserve Tm_let)"
                        in
                     (match uu____12218 with
                      | (se2,lbs1) ->
                          (FStar_All.pipe_right
                             (FStar_Pervasives_Native.snd lbs1)
                             (FStar_List.iter
                                (fun lb  ->
                                   let fv =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_TypeChecker_Env.insert_fv_info env1
                                     fv lb.FStar_Syntax_Syntax.lbtyp));
                           (let uu____12402 = log env1  in
                            if uu____12402
                            then
                              let uu____12405 =
                                let uu____12407 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs1)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let should_log =
                                            let uu____12427 =
                                              let uu____12436 =
                                                let uu____12437 =
                                                  let uu____12440 =
                                                    FStar_Util.right
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  uu____12440.FStar_Syntax_Syntax.fv_name
                                                   in
                                                uu____12437.FStar_Syntax_Syntax.v
                                                 in
                                              FStar_TypeChecker_Env.try_lookup_val_decl
                                                env1 uu____12436
                                               in
                                            match uu____12427 with
                                            | FStar_Pervasives_Native.None 
                                                -> true
                                            | uu____12449 -> false  in
                                          if should_log
                                          then
                                            let uu____12461 =
                                              FStar_Syntax_Print.lbname_to_string
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            let uu____12463 =
                                              FStar_Syntax_Print.term_to_string
                                                lb.FStar_Syntax_Syntax.lbtyp
                                               in
                                            FStar_Util.format2 "let %s : %s"
                                              uu____12461 uu____12463
                                          else ""))
                                   in
                                FStar_All.pipe_right uu____12407
                                  (FStar_String.concat "\n")
                                 in
                              FStar_Util.print1 "%s\n" uu____12405
                            else ());
                           check_must_erase_attribute env0 se2;
                           ([se2], [], env0))))))
  
let (tc_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun se  ->
      let env1 = set_hint_correlator env se  in
      (let uu____12515 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____12515
       then
         let uu____12518 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____12518
       else ());
      (let uu____12523 = get_fail_se se  in
       match uu____12523 with
       | FStar_Pervasives_Native.Some (uu____12544,false ) when
           let uu____12561 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____12561 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___427_12587 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___427_12587.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___427_12587.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___427_12587.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___427_12587.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___427_12587.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___427_12587.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___427_12587.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___427_12587.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___427_12587.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___427_12587.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___427_12587.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___427_12587.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___427_12587.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___427_12587.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___427_12587.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___427_12587.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___427_12587.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___427_12587.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___427_12587.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___427_12587.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___427_12587.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___427_12587.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___427_12587.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___427_12587.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___427_12587.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___427_12587.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___427_12587.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___427_12587.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___427_12587.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___427_12587.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___427_12587.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___427_12587.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___427_12587.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___427_12587.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___427_12587.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___427_12587.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___427_12587.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___427_12587.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___427_12587.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___427_12587.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___427_12587.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___427_12587.FStar_TypeChecker_Env.nbe)
               }
             else env1  in
           ((let uu____12592 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____12592
             then
               let uu____12595 =
                 let uu____12597 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____12597
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____12595
             else ());
            (let uu____12611 =
               FStar_Errors.catch_errors
                 (fun uu____12641  ->
                    FStar_Options.with_saved_options
                      (fun uu____12653  -> tc_decl' env' se))
                in
             match uu____12611 with
             | (errs,uu____12665) ->
                 ((let uu____12695 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____12695
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____12730 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____12730  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____12742 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____12753 =
                            let uu____12763 =
                              check_multi_contained errnos1 actual  in
                            match uu____12763 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")))
                             in
                          (match uu____12753 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____12828 =
                                   let uu____12834 =
                                     let uu____12836 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____12839 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____12842 =
                                       FStar_Util.string_of_int e  in
                                     let uu____12844 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____12846 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____12836 uu____12839 uu____12842
                                       uu____12844 uu____12846
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____12834)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____12828)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____12873 .
    'Auu____12873 ->
      FStar_Ident.lident Prims.list ->
        FStar_Syntax_Syntax.sigelt ->
          (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident
            Prims.list)
  =
  fun env  ->
    fun hidden  ->
      fun se  ->
        let is_abstract quals =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___377_12916  ->
                  match uu___377_12916 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____12919 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____12930) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____12938 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____12948 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____12953 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____12969 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____12995 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13021) ->
            let uu____13030 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13030
            then
              let for_export_bundle se1 uu____13067 =
                match uu____13067 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____13106,uu____13107) ->
                         let dec =
                           let uu___428_13117 = se1  in
                           let uu____13118 =
                             let uu____13119 =
                               let uu____13126 =
                                 let uu____13127 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____13127  in
                               (l, us, uu____13126)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____13119
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____13118;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___428_13117.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___428_13117.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___428_13117.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____13137,uu____13138,uu____13139) ->
                         let dec =
                           let uu___429_13147 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___429_13147.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___429_13147.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___429_13147.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____13152 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____13175,uu____13176,uu____13177) ->
            let uu____13178 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13178 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____13202 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____13202
            then
              ([(let uu___430_13221 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___430_13221.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___430_13221.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___430_13221.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____13224 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___378_13230  ->
                         match uu___378_13230 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____13233 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____13239 ->
                             true
                         | uu____13241 -> false))
                  in
               if uu____13224 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____13262 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____13267 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____13272 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13277 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13295) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____13309 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____13309
            then ([], hidden)
            else
              (let dec =
                 let uu____13330 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____13330;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____13341 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13341
            then
              let uu____13352 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___431_13366 = se  in
                        let uu____13367 =
                          let uu____13368 =
                            let uu____13375 =
                              let uu____13376 =
                                let uu____13379 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____13379.FStar_Syntax_Syntax.fv_name  in
                              uu____13376.FStar_Syntax_Syntax.v  in
                            (uu____13375, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____13368  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____13367;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___431_13366.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___431_13366.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___431_13366.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____13352, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____13402 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____13402
       then
         let uu____13405 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____13405
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____13410 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____13428 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____13445) -> z3_reset_options env
       | FStar_Syntax_Syntax.Sig_pragma uu____13449 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____13459 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____13459) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____13460,uu____13461,uu____13462) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_13467  ->
                   match uu___379_13467 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13470 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____13472,uu____13473) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_13482  ->
                   match uu___379_13482 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13485 -> false))
           -> env
       | uu____13487 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____13556 se =
        match uu____13556 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____13609 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____13609
              then
                let uu____13612 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____13612
              else ());
             (let uu____13617 = tc_decl env1 se  in
              match uu____13617 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____13670 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____13670
                             then
                               let uu____13674 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____13674
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____13690 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____13690
                             then
                               let uu____13694 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____13694
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  (FStar_TypeChecker_Env.promote_id_info env2
                     (fun t  ->
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.AllowUnboundUniverses;
                          FStar_TypeChecker_Env.CheckNoUvars;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                          FStar_TypeChecker_Env.CompressUvars;
                          FStar_TypeChecker_Env.Exclude
                            FStar_TypeChecker_Env.Zeta;
                          FStar_TypeChecker_Env.Exclude
                            FStar_TypeChecker_Env.Iota;
                          FStar_TypeChecker_Env.NoFullNorm] env2 t);
                   (let env3 =
                      FStar_All.pipe_right ses'1
                        (FStar_List.fold_left
                           (fun env3  ->
                              fun se1  -> add_sigelt_to_env env3 se1) env2)
                       in
                    FStar_Syntax_Unionfind.reset ();
                    (let uu____13711 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____13711
                     then
                       let uu____13716 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____13725 =
                                  let uu____13727 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____13727 "\n"  in
                                Prims.strcat s uu____13725) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____13716
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____13737 =
                       let uu____13746 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____13746
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____13788 se1 =
                            match uu____13788 with
                            | (exports1,hidden1) ->
                                let uu____13816 = for_export env3 hidden1 se1
                                   in
                                (match uu____13816 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____13737 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____13970 = acc  in
        match uu____13970 with
        | (uu____14005,uu____14006,env1,uu____14008) ->
            let uu____14021 =
              FStar_Util.record_time
                (fun uu____14068  -> process_one_decl acc se)
               in
            (match uu____14021 with
             | (r,ms_elapsed) ->
                 ((let uu____14134 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____14134
                   then
                     let uu____14138 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____14140 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____14138 uu____14140
                   else ());
                  r))
         in
      let uu____14145 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____14145 with
      | (ses1,exports,env1,uu____14193) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
  
let (check_exports :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> unit)
  =
  fun env  ->
    fun modul  ->
      fun exports  ->
        let env1 =
          let uu___432_14231 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___432_14231.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___432_14231.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___432_14231.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___432_14231.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___432_14231.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___432_14231.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___432_14231.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___432_14231.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___432_14231.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___432_14231.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___432_14231.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___432_14231.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___432_14231.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___432_14231.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___432_14231.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___432_14231.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___432_14231.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___432_14231.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___432_14231.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___432_14231.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___432_14231.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___432_14231.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___432_14231.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___432_14231.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___432_14231.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___432_14231.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___432_14231.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___432_14231.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___432_14231.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___432_14231.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___432_14231.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___432_14231.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___432_14231.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___432_14231.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___432_14231.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___432_14231.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___432_14231.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___432_14231.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___432_14231.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___432_14231.FStar_TypeChecker_Env.nbe)
          }  in
        let check_term lid univs1 t =
          let uu____14251 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____14251 with
          | (univs2,t1) ->
              ((let uu____14259 =
                  let uu____14261 =
                    let uu____14267 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____14267  in
                  FStar_All.pipe_left uu____14261
                    (FStar_Options.Other "Exports")
                   in
                if uu____14259
                then
                  let uu____14271 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____14273 =
                    let uu____14275 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____14275
                      (FStar_String.concat ", ")
                     in
                  let uu____14292 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____14271 uu____14273 uu____14292
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____14298 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____14298 (fun a1  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____14324 =
             let uu____14326 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____14328 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____14326 uu____14328
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____14324);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14339) ->
              let uu____14348 =
                let uu____14350 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14350  in
              if uu____14348
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____14364,uu____14365) ->
              let t =
                let uu____14377 =
                  let uu____14384 =
                    let uu____14385 =
                      let uu____14400 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____14400)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____14385  in
                  FStar_Syntax_Syntax.mk uu____14384  in
                uu____14377 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____14419,uu____14420,uu____14421) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____14431 =
                let uu____14433 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14433  in
              if uu____14431 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____14441,lbs),uu____14443) ->
              let uu____14454 =
                let uu____14456 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14456  in
              if uu____14454
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        check_term1
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l,univs1,binders,comp,flags1) ->
              let uu____14479 =
                let uu____14481 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14481  in
              if uu____14479
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____14502 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____14503 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14510 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____14511 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____14512 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____14519 -> ()  in
        let uu____14520 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____14520 then () else FStar_List.iter check_sigelt exports
  
let (extract_interface :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul)
  =
  fun en  ->
    fun m  ->
      let is_abstract = FStar_List.contains FStar_Syntax_Syntax.Abstract  in
      let is_irreducible1 =
        FStar_List.contains FStar_Syntax_Syntax.Irreducible  in
      let is_assume = FStar_List.contains FStar_Syntax_Syntax.Assumption  in
      let filter_out_abstract =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               (((q = FStar_Syntax_Syntax.Abstract) ||
                   (q = FStar_Syntax_Syntax.Irreducible))
                  || (q = FStar_Syntax_Syntax.Visible_default)))
         in
      let filter_out_abstract_and_noeq =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               (((((q = FStar_Syntax_Syntax.Abstract) ||
                     (q = FStar_Syntax_Syntax.Noeq))
                    || (q = FStar_Syntax_Syntax.Unopteq))
                   || (q = FStar_Syntax_Syntax.Irreducible))
                  || (q = FStar_Syntax_Syntax.Visible_default)))
         in
      let filter_out_abstract_and_inline =
        FStar_List.filter
          (fun q  ->
             Prims.op_Negation
               (((((q = FStar_Syntax_Syntax.Abstract) ||
                     (q = FStar_Syntax_Syntax.Irreducible))
                    || (q = FStar_Syntax_Syntax.Visible_default))
                   || (q = FStar_Syntax_Syntax.Inline_for_extraction))
                  ||
                  (q = FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)))
         in
      let abstract_inductive_tycons = FStar_Util.mk_ref []  in
      let abstract_inductive_datacons = FStar_Util.mk_ref []  in
      let is_projector_or_discriminator_of_an_abstract_inductive quals =
        FStar_List.existsML
          (fun q  ->
             match q with
             | FStar_Syntax_Syntax.Discriminator l -> true
             | FStar_Syntax_Syntax.Projector (l,uu____14626) -> true
             | uu____14628 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____14658 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____14697 ->
                   let uu____14698 =
                     let uu____14705 =
                       let uu____14706 =
                         let uu____14721 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____14721)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____14706  in
                     FStar_Syntax_Syntax.mk uu____14705  in
                   uu____14698 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____14741,uu____14742) ->
            let s1 =
              let uu___433_14752 = s  in
              let uu____14753 =
                let uu____14754 =
                  let uu____14761 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____14761)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____14754  in
              let uu____14762 =
                let uu____14765 =
                  let uu____14768 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____14768  in
                FStar_Syntax_Syntax.Assumption :: uu____14765  in
              {
                FStar_Syntax_Syntax.sigel = uu____14753;
                FStar_Syntax_Syntax.sigrng =
                  (uu___433_14752.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____14762;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___433_14752.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___433_14752.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____14771 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____14796 lbdef =
        match uu____14796 with
        | (uvs,t) ->
            let attrs =
              let uu____14807 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____14807
              then
                let uu____14812 =
                  let uu____14813 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____14813
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____14812 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___434_14816 = s  in
            let uu____14817 =
              let uu____14820 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____14820  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___434_14816.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____14817;
              FStar_Syntax_Syntax.sigmeta =
                (uu___434_14816.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____14838 -> failwith "Impossible!"  in
        let c_opt =
          let uu____14845 = FStar_Syntax_Util.is_unit t  in
          if uu____14845
          then
            let uu____14852 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____14852
          else
            (let uu____14859 =
               let uu____14860 = FStar_Syntax_Subst.compress t  in
               uu____14860.FStar_Syntax_Syntax.n  in
             match uu____14859 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____14867,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____14891 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____14903 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____14903
            then false
            else
              (let uu____14910 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____14910
               then true
               else
                 (let uu____14917 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____14917))
         in
      let extract_sigelt s =
        (let uu____14929 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____14929
         then
           let uu____14932 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____14932
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____14939 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____14959 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____14978 ->
             failwith
               "Impossible! extract_interface: trying to extract splice"
         | FStar_Syntax_Syntax.Sig_bundle (sigelts,lidents1) ->
             if is_abstract s.FStar_Syntax_Syntax.sigquals
             then
               FStar_All.pipe_right sigelts
                 (FStar_List.fold_left
                    (fun sigelts1  ->
                       fun s1  ->
                         match s1.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_inductive_typ
                             (lid,uu____15024,uu____15025,uu____15026,uu____15027,uu____15028)
                             ->
                             ((let uu____15038 =
                                 let uu____15041 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____15041  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____15038);
                              (let uu____15134 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____15134 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____15138,uu____15139,uu____15140,uu____15141,uu____15142)
                             ->
                             ((let uu____15150 =
                                 let uu____15153 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____15153  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____15150);
                              sigelts1)
                         | uu____15246 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____15255 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15255
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____15265 =
                    let uu___435_15266 = s  in
                    let uu____15267 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___435_15266.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___435_15266.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15267;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___435_15266.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___435_15266.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15265])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____15278 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15278
             then []
             else
               (let uu____15285 = lbs  in
                match uu____15285 with
                | (flbs,slbs) ->
                    let typs_and_defs =
                      FStar_All.pipe_right slbs
                        (FStar_List.map
                           (fun lb  ->
                              ((lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp),
                                (lb.FStar_Syntax_Syntax.lbdef))))
                       in
                    let is_lemma1 =
                      FStar_List.existsML
                        (fun uu____15347  ->
                           match uu____15347 with
                           | (uu____15355,t,uu____15357) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____15374  ->
                             match uu____15374 with
                             | (u,t,d) -> val_of_lb s lid (u, t) d) lids
                        typs_and_defs
                       in
                    if
                      ((is_abstract s.FStar_Syntax_Syntax.sigquals) ||
                         (is_irreducible1 s.FStar_Syntax_Syntax.sigquals))
                        || is_lemma1
                    then vals
                    else
                      (let should_keep_defs =
                         FStar_List.existsML
                           (fun uu____15401  ->
                              match uu____15401 with
                              | (uu____15409,t,uu____15411) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____15423,uu____15424) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____15432 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____15483 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____15483) uu____15432
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____15487 =
                    let uu___436_15488 = s  in
                    let uu____15489 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___436_15488.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___436_15488.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15489;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___436_15488.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___436_15488.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15487]
                else [])
             else
               (let uu____15496 =
                  let uu___437_15497 = s  in
                  let uu____15498 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___437_15497.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___437_15497.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____15498;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___437_15497.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___437_15497.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____15496])
         | FStar_Syntax_Syntax.Sig_new_effect uu____15501 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____15502 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15503 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____15516 -> [s])
         in
      let uu___438_15517 = m  in
      let uu____15518 =
        let uu____15519 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____15519 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___438_15517.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____15518;
        FStar_Syntax_Syntax.exports =
          (uu___438_15517.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
  
let (snapshot_context :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15570  -> FStar_TypeChecker_Env.snapshot env msg)
  
let (rollback_context :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      (Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____15618  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             solver.FStar_TypeChecker_Env.refresh (); env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____15634 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____15634
  
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      rollback_context env.FStar_TypeChecker_Env.solver msg
        FStar_Pervasives_Native.None
  
let (tc_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
        FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun modul  ->
      let verify =
        FStar_Options.should_verify
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      let action = if verify then "Verifying" else "Lax-checking"  in
      let label1 =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation"  in
      (let uu____15723 = FStar_Options.debug_any ()  in
       if uu____15723
       then
         FStar_Util.print3 "%s %s of %s\n" action label1
           (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
       else ());
      (let name =
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
          in
       let env1 =
         let uu___439_15739 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___439_15739.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___439_15739.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___439_15739.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___439_15739.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___439_15739.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___439_15739.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___439_15739.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___439_15739.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___439_15739.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___439_15739.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___439_15739.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___439_15739.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___439_15739.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___439_15739.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___439_15739.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___439_15739.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___439_15739.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___439_15739.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___439_15739.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___439_15739.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___439_15739.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___439_15739.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___439_15739.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___439_15739.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___439_15739.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___439_15739.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___439_15739.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___439_15739.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___439_15739.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___439_15739.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___439_15739.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___439_15739.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___439_15739.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___439_15739.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___439_15739.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___439_15739.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___439_15739.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___439_15739.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___439_15739.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___439_15739.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___439_15739.FStar_TypeChecker_Env.nbe)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____15741 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____15741 with
       | (ses,exports,env3) ->
           ((let uu___440_15774 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___440_15774.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___440_15774.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___440_15774.FStar_Syntax_Syntax.is_interface)
             }), exports, env3))
  
let (tc_more_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
          FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun modul  ->
      fun decls  ->
        let uu____15803 = tc_decls env decls  in
        match uu____15803 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___441_15834 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___441_15834.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___441_15834.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___441_15834.FStar_Syntax_Syntax.is_interface)
              }  in
            (modul1, exports, env1)
  
let rec (tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env0  ->
    fun m  ->
      fun iface_exists  ->
        let msg =
          Prims.strcat "Internals for "
            (m.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        let env01 = push_context env0 msg  in
        let uu____15895 = tc_partial_modul env01 m  in
        match uu____15895 with
        | (modul,non_private_decls,env) ->
            finish_partial_modul false iface_exists env modul
              non_private_decls

and (finish_partial_modul :
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.modul ->
          FStar_Syntax_Syntax.sigelt Prims.list ->
            (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun loading_from_cache  ->
    fun iface_exists  ->
      fun en  ->
        fun m  ->
          fun exports  ->
            let should_extract_interface =
              ((((Prims.op_Negation loading_from_cache) &&
                   (Prims.op_Negation iface_exists))
                  && (FStar_Options.use_extracted_interfaces ()))
                 && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
                &&
                (let uu____15932 = FStar_Errors.get_err_count ()  in
                 uu____15932 = (Prims.parse_int "0"))
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____15943 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____15943
                then
                  let uu____15947 =
                    let uu____15949 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____15949 then "" else " (in lax mode) "  in
                  let uu____15957 =
                    let uu____15959 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____15959
                    then
                      let uu____15963 =
                        let uu____15965 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.strcat uu____15965 "\n"  in
                      Prims.strcat "\nfrom: " uu____15963
                    else ""  in
                  let uu____15972 =
                    let uu____15974 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____15974
                    then
                      let uu____15978 =
                        let uu____15980 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.strcat uu____15980 "\n"  in
                      Prims.strcat "\nto: " uu____15978
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____15947
                    uu____15957 uu____15972
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.strcat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___442_15994 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___442_15994.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___442_15994.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___442_15994.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___442_15994.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___442_15994.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___442_15994.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___442_15994.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___442_15994.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___442_15994.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___442_15994.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___442_15994.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___442_15994.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___442_15994.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___442_15994.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___442_15994.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___442_15994.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___442_15994.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___442_15994.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___442_15994.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___442_15994.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___442_15994.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___442_15994.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___442_15994.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___442_15994.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___442_15994.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___442_15994.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___442_15994.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___442_15994.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___442_15994.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___442_15994.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___442_15994.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___442_15994.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___442_15994.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___442_15994.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___442_15994.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___442_15994.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___442_15994.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___442_15994.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___442_15994.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___442_15994.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___442_15994.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___442_15994.FStar_TypeChecker_Env.nbe)
                    }  in
                  let en02 =
                    let uu___443_15996 = en01  in
                    let uu____15997 =
                      let uu____16012 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____16012, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___443_15996.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___443_15996.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___443_15996.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___443_15996.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___443_15996.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___443_15996.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___443_15996.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___443_15996.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___443_15996.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___443_15996.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___443_15996.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___443_15996.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___443_15996.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___443_15996.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___443_15996.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___443_15996.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___443_15996.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___443_15996.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___443_15996.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___443_15996.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___443_15996.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___443_15996.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___443_15996.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___443_15996.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___443_15996.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___443_15996.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___443_15996.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___443_15996.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___443_15996.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___443_15996.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___443_15996.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____15997;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___443_15996.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___443_15996.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___443_15996.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___443_15996.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___443_15996.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___443_15996.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___443_15996.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___443_15996.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___443_15996.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___443_15996.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___443_15996.FStar_TypeChecker_Env.nbe)
                    }  in
                  let uu____16058 =
                    let uu____16060 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____16060  in
                  if uu____16058
                  then
                    ((let uu____16064 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____16064 (fun a2  -> ()));
                     z3_reset_options en02)
                  else en02  in
                let uu____16068 = tc_modul en0 modul_iface true  in
                match uu____16068 with
                | (modul_iface1,env) ->
                    ((let uu___444_16081 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___444_16081.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___444_16081.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___444_16081.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___445_16085 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___445_16085.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___445_16085.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___445_16085.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____16088 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____16088 FStar_Util.smap_clear);
               (let uu____16124 =
                  ((let uu____16128 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____16128) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____16131 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____16131)
                   in
                if uu____16124 then check_exports env modul exports else ());
               (let uu____16137 =
                  pop_context env
                    (Prims.strcat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____16137 (fun a3  -> ()));
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
                 env modul;
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ();
               (let uu____16142 =
                  let uu____16144 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____16144  in
                if uu____16142
                then
                  let uu____16147 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____16147 (fun a4  -> ())
                else ());
               (modul, env))

let (load_checked_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_TypeChecker_Env.env)
  =
  fun en  ->
    fun m  ->
      let env =
        FStar_TypeChecker_Env.set_current_module en
          m.FStar_Syntax_Syntax.name
         in
      let env1 =
        let uu____16164 =
          let uu____16166 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____16166  in
        push_context env uu____16164  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____16187 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____16198 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____16198 with | (uu____16205,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____16230 = FStar_Options.debug_any ()  in
         if uu____16230
         then
           let uu____16233 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____16233
         else ());
        (let uu____16245 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____16245
         then
           let uu____16248 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____16248
         else ());
        (let env1 =
           let uu___446_16254 = env  in
           let uu____16255 =
             let uu____16257 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____16257  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___446_16254.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___446_16254.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___446_16254.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___446_16254.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___446_16254.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___446_16254.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___446_16254.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___446_16254.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___446_16254.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___446_16254.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___446_16254.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___446_16254.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___446_16254.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___446_16254.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___446_16254.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___446_16254.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___446_16254.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___446_16254.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___446_16254.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___446_16254.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____16255;
             FStar_TypeChecker_Env.lax_universes =
               (uu___446_16254.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___446_16254.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___446_16254.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___446_16254.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___446_16254.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___446_16254.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___446_16254.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___446_16254.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___446_16254.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___446_16254.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___446_16254.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___446_16254.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___446_16254.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___446_16254.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___446_16254.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___446_16254.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___446_16254.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___446_16254.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___446_16254.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___446_16254.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___446_16254.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___446_16254.FStar_TypeChecker_Env.nbe)
           }  in
         let uu____16259 = tc_modul env1 m b  in
         match uu____16259 with
         | (m1,env2) ->
             ((let uu____16271 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____16271
               then
                 let uu____16274 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____16274
               else ());
              (let uu____16280 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____16280
               then
                 let normalize_toplevel_lets se =
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_let ((b1,lbs),ids) ->
                       let n1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Reify;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.AllowUnboundUniverses]
                          in
                       let update lb =
                         let uu____16318 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____16318 with
                         | (univnames1,e) ->
                             let uu___447_16325 = lb  in
                             let uu____16326 =
                               let uu____16329 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____16329 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___447_16325.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___447_16325.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___447_16325.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___447_16325.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16326;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___447_16325.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___447_16325.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___448_16330 = se  in
                       let uu____16331 =
                         let uu____16332 =
                           let uu____16339 =
                             let uu____16340 = FStar_List.map update lbs  in
                             (b1, uu____16340)  in
                           (uu____16339, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____16332  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____16331;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___448_16330.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___448_16330.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___448_16330.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___448_16330.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____16348 -> se  in
                 let normalized_module =
                   let uu___449_16350 = m1  in
                   let uu____16351 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___449_16350.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____16351;
                     FStar_Syntax_Syntax.exports =
                       (uu___449_16350.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___449_16350.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____16352 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____16352
               else ());
              (m1, env2)))
  
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
                    ((let uu____713 =
                        FStar_Syntax_Print.eff_decl_to_string ed  in
                      FStar_Util.print1 "GG cps_and_elaborate (%s)\n"
                        uu____713);
                     (let raise_error1 uu____731 =
                        match uu____731 with
                        | (e,err_msg) ->
                            FStar_Errors.raise_error (e, err_msg)
                              signature1.FStar_Syntax_Syntax.pos
                         in
                      let effect_binders1 =
                        FStar_List.map
                          (fun uu____767  ->
                             match uu____767 with
                             | (bv,qual) ->
                                 let uu____786 =
                                   let uu___382_787 = bv  in
                                   let uu____788 =
                                     FStar_TypeChecker_Normalize.normalize
                                       [FStar_TypeChecker_Env.EraseUniverses]
                                       env1 bv.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___382_787.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___382_787.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____788
                                   }  in
                                 (uu____786, qual)) effect_binders
                         in
                      (let uu____794 =
                         FStar_Syntax_Print.term_to_string signature1  in
                       FStar_Util.print1 "GG sig = %s\n" uu____794);
                      (let uu____797 =
                         let uu____804 =
                           let uu____805 =
                             FStar_Syntax_Subst.compress signature_un  in
                           uu____805.FStar_Syntax_Syntax.n  in
                         match uu____804 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             ((a,uu____815)::[],effect_marker) ->
                             (a, effect_marker)
                         | uu____847 ->
                             raise_error1
                               (FStar_Errors.Fatal_BadSignatureShape,
                                 "bad shape for effect-for-free signature")
                          in
                       match uu____797 with
                       | (a,effect_marker) ->
                           let a1 =
                             let uu____873 = FStar_Syntax_Syntax.is_null_bv a
                                in
                             if uu____873
                             then
                               let uu____876 =
                                 let uu____879 =
                                   FStar_Syntax_Syntax.range_of_bv a  in
                                 FStar_Pervasives_Native.Some uu____879  in
                               FStar_Syntax_Syntax.gen_bv "a" uu____876
                                 a.FStar_Syntax_Syntax.sort
                             else a  in
                           let mk1 x =
                             FStar_Syntax_Syntax.mk x
                               FStar_Pervasives_Native.None
                               signature1.FStar_Syntax_Syntax.pos
                              in
                           let uu____891 =
                             open_and_check env1 effect_binders1 []
                               (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                              in
                           (match uu____891 with
                            | (repr,_comp) ->
                                ((let uu____915 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____915);
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env1
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env1 FStar_Range.dummyRange)
                                     in
                                  let wp_type =
                                    FStar_TypeChecker_DMFF.star_type dmff_env
                                      repr
                                     in
                                  let uu____920 =
                                    recheck_debug "*" env1 wp_type  in
                                  let wp_a =
                                    let uu____923 =
                                      let uu____924 =
                                        let uu____925 =
                                          let uu____942 =
                                            let uu____953 =
                                              let uu____962 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a1
                                                 in
                                              let uu____965 =
                                                FStar_Syntax_Syntax.as_implicit
                                                  false
                                                 in
                                              (uu____962, uu____965)  in
                                            [uu____953]  in
                                          (wp_type, uu____942)  in
                                        FStar_Syntax_Syntax.Tm_app uu____925
                                         in
                                      mk1 uu____924  in
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1
                                      uu____923
                                     in
                                  let effect_signature =
                                    let binders =
                                      let uu____1013 =
                                        let uu____1020 =
                                          FStar_Syntax_Syntax.as_implicit
                                            false
                                           in
                                        (a1, uu____1020)  in
                                      let uu____1026 =
                                        let uu____1035 =
                                          let uu____1042 =
                                            FStar_Syntax_Syntax.gen_bv
                                              "dijkstra_wp"
                                              FStar_Pervasives_Native.None
                                              wp_a
                                             in
                                          FStar_All.pipe_right uu____1042
                                            FStar_Syntax_Syntax.mk_binder
                                           in
                                        [uu____1035]  in
                                      uu____1013 :: uu____1026  in
                                    let binders1 =
                                      FStar_Syntax_Subst.close_binders
                                        binders
                                       in
                                    mk1
                                      (FStar_Syntax_Syntax.Tm_arrow
                                         (binders1, effect_marker))
                                     in
                                  let uu____1079 =
                                    recheck_debug
                                      "turned into the effect signature" env1
                                      effect_signature
                                     in
                                  let sigelts = FStar_Util.mk_ref []  in
                                  let mk_lid name =
                                    FStar_Syntax_Util.dm4f_lid ed name  in
                                  FStar_Util.print_string "GG2\n";
                                  (let uu____1098 =
                                     elaborate_and_star dmff_env
                                       effect_binders1 []
                                       (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                      in
                                   match uu____1098 with
                                   | (dmff_env1,uu____1124,bind_wp,bind_elab)
                                       ->
                                       (FStar_Util.print_string "GG3\n";
                                        (let uu____1129 =
                                           elaborate_and_star dmff_env1
                                             effect_binders1 []
                                             (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                            in
                                         match uu____1129 with
                                         | (dmff_env2,uu____1155,return_wp,return_elab)
                                             ->
                                             let rc_gtot =
                                               {
                                                 FStar_Syntax_Syntax.residual_effect
                                                   =
                                                   FStar_Parser_Const.effect_GTot_lid;
                                                 FStar_Syntax_Syntax.residual_typ
                                                   =
                                                   FStar_Pervasives_Native.None;
                                                 FStar_Syntax_Syntax.residual_flags
                                                   = []
                                               }  in
                                             let lift_from_pure_wp =
                                               let uu____1164 =
                                                 let uu____1165 =
                                                   FStar_Syntax_Subst.compress
                                                     return_wp
                                                    in
                                                 uu____1165.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____1164 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (b1::b2::bs,body,what) ->
                                                   let uu____1223 =
                                                     let uu____1242 =
                                                       let uu____1247 =
                                                         FStar_Syntax_Util.abs
                                                           bs body
                                                           FStar_Pervasives_Native.None
                                                          in
                                                       FStar_Syntax_Subst.open_term
                                                         [b1; b2] uu____1247
                                                        in
                                                     match uu____1242 with
                                                     | (b11::b21::[],body1)
                                                         -> (b11, b21, body1)
                                                     | uu____1329 ->
                                                         failwith
                                                           "Impossible : open_term not preserving binders arity"
                                                      in
                                                   (match uu____1223 with
                                                    | (b11,b21,body1) ->
                                                        let env0 =
                                                          let uu____1383 =
                                                            FStar_TypeChecker_DMFF.get_env
                                                              dmff_env2
                                                             in
                                                          FStar_TypeChecker_Env.push_binders
                                                            uu____1383
                                                            [b11; b21]
                                                           in
                                                        let wp_b1 =
                                                          let raw_wp_b1 =
                                                            let uu____1406 =
                                                              let uu____1407
                                                                =
                                                                let uu____1424
                                                                  =
                                                                  let uu____1435
                                                                    =
                                                                    let uu____1444
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (FStar_Pervasives_Native.fst
                                                                    b11)  in
                                                                    let uu____1449
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____1444,
                                                                    uu____1449)
                                                                     in
                                                                  [uu____1435]
                                                                   in
                                                                (wp_type,
                                                                  uu____1424)
                                                                 in
                                                              FStar_Syntax_Syntax.Tm_app
                                                                uu____1407
                                                               in
                                                            mk1 uu____1406
                                                             in
                                                          FStar_TypeChecker_Normalize.normalize
                                                            [FStar_TypeChecker_Env.Beta]
                                                            env0 raw_wp_b1
                                                           in
                                                        let uu____1485 =
                                                          let uu____1494 =
                                                            let uu____1495 =
                                                              FStar_Syntax_Util.unascribe
                                                                wp_b1
                                                               in
                                                            FStar_TypeChecker_Normalize.eta_expand_with_type
                                                              env0 body1
                                                              uu____1495
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Util.abs_formals
                                                            uu____1494
                                                           in
                                                        (match uu____1485
                                                         with
                                                         | (bs1,body2,what')
                                                             ->
                                                             let fail1
                                                               uu____1518 =
                                                               let error_msg
                                                                 =
                                                                 let uu____1521
                                                                   =
                                                                   FStar_Syntax_Print.term_to_string
                                                                    body2
                                                                    in
                                                                 let uu____1523
                                                                   =
                                                                   match what'
                                                                   with
                                                                   | 
                                                                   FStar_Pervasives_Native.None
                                                                     ->
                                                                    "None"
                                                                   | 
                                                                   FStar_Pervasives_Native.Some
                                                                    rc ->
                                                                    FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                    in
                                                                 FStar_Util.format2
                                                                   "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                                   uu____1521
                                                                   uu____1523
                                                                  in
                                                               raise_error1
                                                                 (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                                   error_msg)
                                                                in
                                                             ((match what'
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                    ->
                                                                   fail1 ()
                                                               | FStar_Pervasives_Native.Some
                                                                   rc ->
                                                                   ((
                                                                    let uu____1533
                                                                    =
                                                                    let uu____1535
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____1535
                                                                     in
                                                                    if
                                                                    uu____1533
                                                                    then
                                                                    fail1 ()
                                                                    else ());
                                                                    (
                                                                    let uu____1540
                                                                    =
                                                                    FStar_Util.map_opt
                                                                    rc.FStar_Syntax_Syntax.residual_typ
                                                                    (fun rt 
                                                                    ->
                                                                    let g_opt
                                                                    =
                                                                    FStar_TypeChecker_Rel.try_teq
                                                                    true env1
                                                                    rt
                                                                    FStar_Syntax_Util.ktype0
                                                                     in
                                                                    match g_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g' ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1 g'
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail1 ())
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____1540
                                                                    (fun a1 
                                                                    -> ()))));
                                                              (let wp =
                                                                 let t2 =
                                                                   (FStar_Pervasives_Native.fst
                                                                    b21).FStar_Syntax_Syntax.sort
                                                                    in
                                                                 let pure_wp_type
                                                                   =
                                                                   FStar_TypeChecker_DMFF.double_star
                                                                    t2
                                                                    in
                                                                 FStar_Syntax_Syntax.gen_bv
                                                                   "wp"
                                                                   FStar_Pervasives_Native.None
                                                                   pure_wp_type
                                                                  in
                                                               let body3 =
                                                                 let uu____1569
                                                                   =
                                                                   let uu____1574
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp  in
                                                                   let uu____1575
                                                                    =
                                                                    let uu____1576
                                                                    =
                                                                    let uu____1585
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                    (uu____1585,
                                                                    FStar_Pervasives_Native.None)
                                                                     in
                                                                    [uu____1576]
                                                                     in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____1574
                                                                    uu____1575
                                                                    in
                                                                 uu____1569
                                                                   FStar_Pervasives_Native.None
                                                                   FStar_Range.dummyRange
                                                                  in
                                                               let uu____1622
                                                                 =
                                                                 let uu____1623
                                                                   =
                                                                   let uu____1632
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp  in
                                                                   [uu____1632]
                                                                    in
                                                                 b11 ::
                                                                   uu____1623
                                                                  in
                                                               let uu____1657
                                                                 =
                                                                 FStar_Syntax_Util.abs
                                                                   bs1 body3
                                                                   what
                                                                  in
                                                               FStar_Syntax_Util.abs
                                                                 uu____1622
                                                                 uu____1657
                                                                 (FStar_Pervasives_Native.Some
                                                                    rc_gtot)))))
                                               | uu____1660 ->
                                                   raise_error1
                                                     (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                       "unexpected shape for return")
                                                in
                                             let return_wp1 =
                                               let uu____1668 =
                                                 let uu____1669 =
                                                   FStar_Syntax_Subst.compress
                                                     return_wp
                                                    in
                                                 uu____1669.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____1668 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (b1::b2::bs,body,what) ->
                                                   let uu____1727 =
                                                     FStar_Syntax_Util.abs bs
                                                       body what
                                                      in
                                                   FStar_Syntax_Util.abs
                                                     [b1; b2] uu____1727
                                                     (FStar_Pervasives_Native.Some
                                                        rc_gtot)
                                               | uu____1748 ->
                                                   raise_error1
                                                     (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                       "unexpected shape for return")
                                                in
                                             let bind_wp1 =
                                               let uu____1756 =
                                                 let uu____1757 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_wp
                                                    in
                                                 uu____1757.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____1756 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (binders,body,what) ->
                                                   let r =
                                                     FStar_Syntax_Syntax.lid_as_fv
                                                       FStar_Parser_Const.range_lid
                                                       (FStar_Syntax_Syntax.Delta_constant_at_level
                                                          (Prims.parse_int "1"))
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   let uu____1791 =
                                                     let uu____1792 =
                                                       let uu____1801 =
                                                         let uu____1808 =
                                                           mk1
                                                             (FStar_Syntax_Syntax.Tm_fvar
                                                                r)
                                                            in
                                                         FStar_Syntax_Syntax.null_binder
                                                           uu____1808
                                                          in
                                                       [uu____1801]  in
                                                     FStar_List.append
                                                       uu____1792 binders
                                                      in
                                                   FStar_Syntax_Util.abs
                                                     uu____1791 body what
                                               | uu____1827 ->
                                                   raise_error1
                                                     (FStar_Errors.Fatal_UnexpectedBindShape,
                                                       "unexpected shape for bind")
                                                in
                                             let apply_close t =
                                               if
                                                 (FStar_List.length
                                                    effect_binders1)
                                                   = (Prims.parse_int "0")
                                               then t
                                               else
                                                 (let uu____1857 =
                                                    let uu____1858 =
                                                      let uu____1859 =
                                                        let uu____1876 =
                                                          let uu____1887 =
                                                            FStar_Syntax_Util.args_of_binders
                                                              effect_binders1
                                                             in
                                                          FStar_Pervasives_Native.snd
                                                            uu____1887
                                                           in
                                                        (t, uu____1876)  in
                                                      FStar_Syntax_Syntax.Tm_app
                                                        uu____1859
                                                       in
                                                    mk1 uu____1858  in
                                                  FStar_Syntax_Subst.close
                                                    effect_binders1
                                                    uu____1857)
                                                in
                                             let rec apply_last1 f l =
                                               match l with
                                               | [] ->
                                                   failwith "empty path.."
                                               | a2::[] ->
                                                   let uu____1945 = f a2  in
                                                   [uu____1945]
                                               | x::xs ->
                                                   let uu____1956 =
                                                     apply_last1 f xs  in
                                                   x :: uu____1956
                                                in
                                             let register name item =
                                               let p =
                                                 FStar_Ident.path_of_lid
                                                   ed.FStar_Syntax_Syntax.mname
                                                  in
                                               let p' =
                                                 apply_last1
                                                   (fun s  ->
                                                      Prims.strcat "__"
                                                        (Prims.strcat s
                                                           (Prims.strcat
                                                              "_eff_override_"
                                                              name))) p
                                                  in
                                               let l' =
                                                 FStar_Ident.lid_of_path p'
                                                   FStar_Range.dummyRange
                                                  in
                                               let uu____1990 =
                                                 FStar_TypeChecker_Env.try_lookup_lid
                                                   env1 l'
                                                  in
                                               match uu____1990 with
                                               | FStar_Pervasives_Native.Some
                                                   (_us,_t) ->
                                                   ((let uu____2020 =
                                                       FStar_Options.debug_any
                                                         ()
                                                        in
                                                     if uu____2020
                                                     then
                                                       let uu____2023 =
                                                         FStar_Ident.string_of_lid
                                                           l'
                                                          in
                                                       FStar_Util.print1
                                                         "DM4F: Applying override %s\n"
                                                         uu____2023
                                                     else ());
                                                    (let uu____2028 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         l'
                                                         FStar_Syntax_Syntax.delta_equational
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Syntax_Syntax.fv_to_tm
                                                       uu____2028))
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   let uu____2037 =
                                                     let uu____2042 =
                                                       mk_lid name  in
                                                     let uu____2043 =
                                                       FStar_Syntax_Util.abs
                                                         effect_binders1 item
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_TypeChecker_Util.mk_toplevel_definition
                                                       env1 uu____2042
                                                       uu____2043
                                                      in
                                                   (match uu____2037 with
                                                    | (sigelt,fv) ->
                                                        ((let uu____2047 =
                                                            let uu____2050 =
                                                              FStar_ST.op_Bang
                                                                sigelts
                                                               in
                                                            sigelt ::
                                                              uu____2050
                                                             in
                                                          FStar_ST.op_Colon_Equals
                                                            sigelts
                                                            uu____2047);
                                                         fv))
                                                in
                                             let lift_from_pure_wp1 =
                                               register "lift_from_pure"
                                                 lift_from_pure_wp
                                                in
                                             let return_wp2 =
                                               register "return_wp"
                                                 return_wp1
                                                in
                                             ((let uu____2148 =
                                                 let uu____2151 =
                                                   FStar_Syntax_Syntax.mk_sigelt
                                                     (FStar_Syntax_Syntax.Sig_pragma
                                                        (FStar_Syntax_Syntax.PushOptions
                                                           (FStar_Pervasives_Native.Some
                                                              "--admit_smt_queries true")))
                                                    in
                                                 let uu____2154 =
                                                   FStar_ST.op_Bang sigelts
                                                    in
                                                 uu____2151 :: uu____2154  in
                                               FStar_ST.op_Colon_Equals
                                                 sigelts uu____2148);
                                              (let return_elab1 =
                                                 register "return_elab"
                                                   return_elab
                                                  in
                                               (let uu____2250 =
                                                  let uu____2253 =
                                                    FStar_Syntax_Syntax.mk_sigelt
                                                      (FStar_Syntax_Syntax.Sig_pragma
                                                         FStar_Syntax_Syntax.PopOptions)
                                                     in
                                                  let uu____2254 =
                                                    FStar_ST.op_Bang sigelts
                                                     in
                                                  uu____2253 :: uu____2254
                                                   in
                                                FStar_ST.op_Colon_Equals
                                                  sigelts uu____2250);
                                               (let bind_wp2 =
                                                  register "bind_wp" bind_wp1
                                                   in
                                                (let uu____2350 =
                                                   let uu____2353 =
                                                     FStar_Syntax_Syntax.mk_sigelt
                                                       (FStar_Syntax_Syntax.Sig_pragma
                                                          (FStar_Syntax_Syntax.PushOptions
                                                             (FStar_Pervasives_Native.Some
                                                                "--admit_smt_queries true")))
                                                      in
                                                   let uu____2356 =
                                                     FStar_ST.op_Bang sigelts
                                                      in
                                                   uu____2353 :: uu____2356
                                                    in
                                                 FStar_ST.op_Colon_Equals
                                                   sigelts uu____2350);
                                                (let bind_elab1 =
                                                   register "bind_elab"
                                                     bind_elab
                                                    in
                                                 (let uu____2452 =
                                                    let uu____2455 =
                                                      FStar_Syntax_Syntax.mk_sigelt
                                                        (FStar_Syntax_Syntax.Sig_pragma
                                                           FStar_Syntax_Syntax.PopOptions)
                                                       in
                                                    let uu____2456 =
                                                      FStar_ST.op_Bang
                                                        sigelts
                                                       in
                                                    uu____2455 :: uu____2456
                                                     in
                                                  FStar_ST.op_Colon_Equals
                                                    sigelts uu____2452);
                                                 (let uu____2549 =
                                                    FStar_List.fold_left
                                                      (fun uu____2591  ->
                                                         fun action  ->
                                                           match uu____2591
                                                           with
                                                           | (dmff_env3,actions)
                                                               ->
                                                               ((let uu____2612
                                                                   =
                                                                   FStar_Ident.string_of_lid
                                                                    action.FStar_Syntax_Syntax.action_name
                                                                    in
                                                                 FStar_Util.print1
                                                                   "GG proc action %s\n"
                                                                   uu____2612);
                                                                (let params_un
                                                                   =
                                                                   FStar_Syntax_Subst.open_binders
                                                                    action.FStar_Syntax_Syntax.action_params
                                                                    in
                                                                 let uu____2616
                                                                   =
                                                                   let uu____2623
                                                                    =
                                                                    FStar_TypeChecker_DMFF.get_env
                                                                    dmff_env3
                                                                     in
                                                                   FStar_TypeChecker_TcTerm.tc_tparams
                                                                    uu____2623
                                                                    params_un
                                                                    in
                                                                 match uu____2616
                                                                 with
                                                                 | (action_params,env',uu____2632)
                                                                    ->
                                                                    let action_params1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____2658
                                                                     ->
                                                                    match uu____2658
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2677
                                                                    =
                                                                    let uu___383_2678
                                                                    = bv  in
                                                                    let uu____2679
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___383_2678.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___383_2678.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2679
                                                                    }  in
                                                                    (uu____2677,
                                                                    qual))
                                                                    action_params
                                                                     in
                                                                    let dmff_env'
                                                                    =
                                                                    FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'  in
                                                                    (FStar_Util.print_string
                                                                    "GG1\n";
                                                                    (let uu____2687
                                                                    =
                                                                    elaborate_and_star
                                                                    dmff_env'
                                                                    effect_binders1
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                     in
                                                                    match uu____2687
                                                                    with
                                                                    | 
                                                                    (dmff_env4,action_t,action_wp,action_elab)
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
                                                                    uu____2730
                                                                    ->
                                                                    let uu____2731
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2731
                                                                     in
                                                                    ((
                                                                    let uu____2735
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____2738
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____2741
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____2743
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2735
                                                                    uu____2738
                                                                    uu____2741
                                                                    uu____2743);
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
                                                                    let uu____2750
                                                                    =
                                                                    let uu____2753
                                                                    =
                                                                    let uu___384_2754
                                                                    = action
                                                                     in
                                                                    let uu____2755
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____2756
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___384_2754.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___384_2754.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___384_2754.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2755;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2756
                                                                    }  in
                                                                    uu____2753
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____2750))))))))
                                                      (dmff_env2, [])
                                                      ed.FStar_Syntax_Syntax.actions
                                                     in
                                                  match uu____2549 with
                                                  | (dmff_env3,actions) ->
                                                      let actions1 =
                                                        FStar_List.rev
                                                          actions
                                                         in
                                                      let repr1 =
                                                        let wp =
                                                          FStar_Syntax_Syntax.gen_bv
                                                            "wp_a"
                                                            FStar_Pervasives_Native.None
                                                            wp_a
                                                           in
                                                        let binders =
                                                          let uu____2800 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a1
                                                             in
                                                          let uu____2807 =
                                                            let uu____2816 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp
                                                               in
                                                            [uu____2816]  in
                                                          uu____2800 ::
                                                            uu____2807
                                                           in
                                                        let uu____2841 =
                                                          let uu____2844 =
                                                            let uu____2845 =
                                                              let uu____2846
                                                                =
                                                                let uu____2863
                                                                  =
                                                                  let uu____2874
                                                                    =
                                                                    let uu____2883
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    a1  in
                                                                    let uu____2886
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____2883,
                                                                    uu____2886)
                                                                     in
                                                                  [uu____2874]
                                                                   in
                                                                (repr,
                                                                  uu____2863)
                                                                 in
                                                              FStar_Syntax_Syntax.Tm_app
                                                                uu____2846
                                                               in
                                                            mk1 uu____2845
                                                             in
                                                          let uu____2922 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp
                                                             in
                                                          FStar_TypeChecker_DMFF.trans_F
                                                            dmff_env3
                                                            uu____2844
                                                            uu____2922
                                                           in
                                                        FStar_Syntax_Util.abs
                                                          binders uu____2841
                                                          FStar_Pervasives_Native.None
                                                         in
                                                      let uu____2923 =
                                                        recheck_debug "FC"
                                                          env1 repr1
                                                         in
                                                      let repr2 =
                                                        register "repr" repr1
                                                         in
                                                      let uu____2927 =
                                                        let uu____2936 =
                                                          let uu____2937 =
                                                            let uu____2940 =
                                                              FStar_Syntax_Subst.compress
                                                                wp_type
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Util.unascribe
                                                              uu____2940
                                                             in
                                                          uu____2937.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____2936 with
                                                        | FStar_Syntax_Syntax.Tm_abs
                                                            (type_param::effect_param,arrow1,uu____2954)
                                                            ->
                                                            let uu____2991 =
                                                              let uu____3012
                                                                =
                                                                FStar_Syntax_Subst.open_term
                                                                  (type_param
                                                                  ::
                                                                  effect_param)
                                                                  arrow1
                                                                 in
                                                              match uu____3012
                                                              with
                                                              | (b::bs,body)
                                                                  ->
                                                                  (b, bs,
                                                                    body)
                                                              | uu____3080 ->
                                                                  failwith
                                                                    "Impossible : open_term nt preserving binders arity"
                                                               in
                                                            (match uu____2991
                                                             with
                                                             | (type_param1,effect_param1,arrow2)
                                                                 ->
                                                                 let uu____3145
                                                                   =
                                                                   let uu____3146
                                                                    =
                                                                    let uu____3149
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____3149
                                                                     in
                                                                   uu____3146.FStar_Syntax_Syntax.n
                                                                    in
                                                                 (match uu____3145
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    let uu____3182
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                    (match uu____3182
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____3197
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3228
                                                                     ->
                                                                    match uu____3228
                                                                    with
                                                                    | 
                                                                    (bv,uu____3237)
                                                                    ->
                                                                    let uu____3242
                                                                    =
                                                                    let uu____3244
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3244
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3242
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____3197
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
                                                                    let uu____3336
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____3336
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____3346
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____3357
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____3357
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____3367
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____3370
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____3367,
                                                                    uu____3370)))
                                                                  | uu____3385
                                                                    ->
                                                                    let uu____3386
                                                                    =
                                                                    let uu____3392
                                                                    =
                                                                    let uu____3394
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____3394
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____3392)
                                                                     in
                                                                    raise_error1
                                                                    uu____3386))
                                                        | uu____3406 ->
                                                            let uu____3407 =
                                                              let uu____3413
                                                                =
                                                                let uu____3415
                                                                  =
                                                                  FStar_Syntax_Print.term_to_string
                                                                    wp_type
                                                                   in
                                                                FStar_Util.format1
                                                                  "Impossible: pre/post abs %s"
                                                                  uu____3415
                                                                 in
                                                              (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                uu____3413)
                                                               in
                                                            raise_error1
                                                              uu____3407
                                                         in
                                                      (match uu____2927 with
                                                       | (pre,post) ->
                                                           ((let uu____3448 =
                                                               register "pre"
                                                                 pre
                                                                in
                                                             ());
                                                            (let uu____3451 =
                                                               register
                                                                 "post" post
                                                                in
                                                             ());
                                                            (let uu____3454 =
                                                               register "wp"
                                                                 wp_type
                                                                in
                                                             ());
                                                            (let ed1 =
                                                               let uu___385_3457
                                                                 = ed  in
                                                               let uu____3458
                                                                 =
                                                                 FStar_Syntax_Subst.close_binders
                                                                   effect_binders1
                                                                  in
                                                               let uu____3459
                                                                 =
                                                                 let uu____3460
                                                                   =
                                                                   let uu____3461
                                                                    =
                                                                    apply_close
                                                                    return_wp2
                                                                     in
                                                                   ([],
                                                                    uu____3461)
                                                                    in
                                                                 let uu____3468
                                                                   =
                                                                   let uu____3469
                                                                    =
                                                                    apply_close
                                                                    bind_wp2
                                                                     in
                                                                   ([],
                                                                    uu____3469)
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.monad_m
                                                                    =
                                                                    FStar_Syntax_Syntax.tun;
                                                                   FStar_Syntax_Syntax.monad_ret
                                                                    =
                                                                    uu____3460;
                                                                   FStar_Syntax_Syntax.monad_bind
                                                                    =
                                                                    uu____3468
                                                                 }  in
                                                               let uu____3476
                                                                 =
                                                                 FStar_Syntax_Subst.close
                                                                   effect_binders1
                                                                   effect_signature
                                                                  in
                                                               let uu____3477
                                                                 =
                                                                 let uu____3478
                                                                   =
                                                                   apply_close
                                                                    repr2
                                                                    in
                                                                 let uu____3479
                                                                   =
                                                                   let uu____3480
                                                                    =
                                                                    apply_close
                                                                    return_elab1
                                                                     in
                                                                   ([],
                                                                    uu____3480)
                                                                    in
                                                                 let uu____3487
                                                                   =
                                                                   let uu____3488
                                                                    =
                                                                    apply_close
                                                                    bind_elab1
                                                                     in
                                                                   ([],
                                                                    uu____3488)
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.monad_m
                                                                    =
                                                                    uu____3478;
                                                                   FStar_Syntax_Syntax.monad_ret
                                                                    =
                                                                    uu____3479;
                                                                   FStar_Syntax_Syntax.monad_bind
                                                                    =
                                                                    uu____3487
                                                                 }  in
                                                               {
                                                                 FStar_Syntax_Syntax.cattributes
                                                                   =
                                                                   (uu___385_3457.FStar_Syntax_Syntax.cattributes);
                                                                 FStar_Syntax_Syntax.mname
                                                                   =
                                                                   (uu___385_3457.FStar_Syntax_Syntax.mname);
                                                                 FStar_Syntax_Syntax.univs
                                                                   =
                                                                   (uu___385_3457.FStar_Syntax_Syntax.univs);
                                                                 FStar_Syntax_Syntax.binders
                                                                   =
                                                                   uu____3458;
                                                                 FStar_Syntax_Syntax.spec
                                                                   =
                                                                   uu____3459;
                                                                 FStar_Syntax_Syntax.signature
                                                                   =
                                                                   uu____3476;
                                                                 FStar_Syntax_Syntax.if_then_else
                                                                   =
                                                                   (uu___385_3457.FStar_Syntax_Syntax.if_then_else);
                                                                 FStar_Syntax_Syntax.ite_wp
                                                                   =
                                                                   (uu___385_3457.FStar_Syntax_Syntax.ite_wp);
                                                                 FStar_Syntax_Syntax.stronger
                                                                   =
                                                                   (uu___385_3457.FStar_Syntax_Syntax.stronger);
                                                                 FStar_Syntax_Syntax.close_wp
                                                                   =
                                                                   (uu___385_3457.FStar_Syntax_Syntax.close_wp);
                                                                 FStar_Syntax_Syntax.assert_p
                                                                   =
                                                                   (uu___385_3457.FStar_Syntax_Syntax.assert_p);
                                                                 FStar_Syntax_Syntax.assume_p
                                                                   =
                                                                   (uu___385_3457.FStar_Syntax_Syntax.assume_p);
                                                                 FStar_Syntax_Syntax.null_wp
                                                                   =
                                                                   (uu___385_3457.FStar_Syntax_Syntax.null_wp);
                                                                 FStar_Syntax_Syntax.trivial
                                                                   =
                                                                   (uu___385_3457.FStar_Syntax_Syntax.trivial);
                                                                 FStar_Syntax_Syntax.repr
                                                                   =
                                                                   uu____3477;
                                                                 FStar_Syntax_Syntax.elaborated
                                                                   =
                                                                   (uu___385_3457.FStar_Syntax_Syntax.elaborated);
                                                                 FStar_Syntax_Syntax.actions
                                                                   = actions1;
                                                                 FStar_Syntax_Syntax.eff_attrs
                                                                   =
                                                                   (uu___385_3457.FStar_Syntax_Syntax.eff_attrs)
                                                               }  in
                                                             let uu____3495 =
                                                               FStar_TypeChecker_DMFF.gen_wps_for_free
                                                                 env1
                                                                 effect_binders1
                                                                 a1 wp_a ed1
                                                                in
                                                             match uu____3495
                                                             with
                                                             | (sigelts',ed2)
                                                                 ->
                                                                 ((let uu____3513
                                                                    =
                                                                    FStar_Syntax_Print.eff_decl_to_string
                                                                    ed2  in
                                                                   FStar_Util.print_string
                                                                    uu____3513);
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
                                                                    let uu____3530
                                                                    =
                                                                    let uu____3533
                                                                    =
                                                                    let uu____3534
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____3534)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3533
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
                                                                    uu____3530;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                    let uu____3541
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3541
                                                                    else
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                   let uu____3544
                                                                    =
                                                                    let uu____3547
                                                                    =
                                                                    let uu____3550
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                    FStar_List.rev
                                                                    uu____3550
                                                                     in
                                                                    FStar_List.append
                                                                    uu____3547
                                                                    sigelts'
                                                                     in
                                                                   (uu____3544,
                                                                    ed2,
                                                                    lift_from_pure_opt))))))))))))))))))))))
  
let tc_eff_decl :
  'Auu____3611 .
    FStar_TypeChecker_Env.env ->
      'Auu____3611 ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun se  ->
      fun ed  ->
        (let uu____3628 =
           FStar_TypeChecker_Env.debug env0 (FStar_Options.Other "ED")  in
         if uu____3628
         then
           let uu____3632 = FStar_Syntax_Print.eff_decl_to_string ed  in
           FStar_Util.print1 "initial eff_decl :\n\t%s\n" uu____3632
         else ());
        (let uu____3637 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____3637 with
         | (open_annotated_univs,annotated_univ_names) ->
             let open_univs n_binders t =
               let uu____3669 =
                 FStar_Syntax_Subst.shift_subst n_binders
                   open_annotated_univs
                  in
               FStar_Syntax_Subst.subst uu____3669 t  in
             let open_univs_binders n_binders bs =
               let uu____3685 =
                 FStar_Syntax_Subst.shift_subst n_binders
                   open_annotated_univs
                  in
               FStar_Syntax_Subst.subst_binders uu____3685 bs  in
             let n_effect_params =
               FStar_List.length ed.FStar_Syntax_Syntax.binders  in
             let signature = ed.FStar_Syntax_Syntax.signature  in
             let uu____3696 =
               let uu____3703 =
                 open_univs_binders (Prims.parse_int "0")
                   ed.FStar_Syntax_Syntax.binders
                  in
               let uu____3705 = open_univs n_effect_params signature  in
               FStar_Syntax_Subst.open_term' uu____3703 uu____3705  in
             (match uu____3696 with
              | (effect_params_un,signature_un,opening) ->
                  let env =
                    FStar_TypeChecker_Env.push_univ_vars env0
                      annotated_univ_names
                     in
                  let uu____3716 =
                    FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un
                     in
                  (match uu____3716 with
                   | (effect_params,env1,uu____3725) ->
                       let uu____3726 =
                         FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                           signature_un
                          in
                       (match uu____3726 with
                        | (signature1,uu____3732) ->
                            let ed1 =
                              let uu___386_3734 = ed  in
                              {
                                FStar_Syntax_Syntax.cattributes =
                                  (uu___386_3734.FStar_Syntax_Syntax.cattributes);
                                FStar_Syntax_Syntax.mname =
                                  (uu___386_3734.FStar_Syntax_Syntax.mname);
                                FStar_Syntax_Syntax.univs =
                                  (uu___386_3734.FStar_Syntax_Syntax.univs);
                                FStar_Syntax_Syntax.binders = effect_params;
                                FStar_Syntax_Syntax.spec =
                                  (uu___386_3734.FStar_Syntax_Syntax.spec);
                                FStar_Syntax_Syntax.signature = signature1;
                                FStar_Syntax_Syntax.if_then_else =
                                  (uu___386_3734.FStar_Syntax_Syntax.if_then_else);
                                FStar_Syntax_Syntax.ite_wp =
                                  (uu___386_3734.FStar_Syntax_Syntax.ite_wp);
                                FStar_Syntax_Syntax.stronger =
                                  (uu___386_3734.FStar_Syntax_Syntax.stronger);
                                FStar_Syntax_Syntax.close_wp =
                                  (uu___386_3734.FStar_Syntax_Syntax.close_wp);
                                FStar_Syntax_Syntax.assert_p =
                                  (uu___386_3734.FStar_Syntax_Syntax.assert_p);
                                FStar_Syntax_Syntax.assume_p =
                                  (uu___386_3734.FStar_Syntax_Syntax.assume_p);
                                FStar_Syntax_Syntax.null_wp =
                                  (uu___386_3734.FStar_Syntax_Syntax.null_wp);
                                FStar_Syntax_Syntax.trivial =
                                  (uu___386_3734.FStar_Syntax_Syntax.trivial);
                                FStar_Syntax_Syntax.repr =
                                  (uu___386_3734.FStar_Syntax_Syntax.repr);
                                FStar_Syntax_Syntax.elaborated =
                                  (uu___386_3734.FStar_Syntax_Syntax.elaborated);
                                FStar_Syntax_Syntax.actions =
                                  (uu___386_3734.FStar_Syntax_Syntax.actions);
                                FStar_Syntax_Syntax.eff_attrs =
                                  (uu___386_3734.FStar_Syntax_Syntax.eff_attrs)
                              }  in
                            let ed2 =
                              match (effect_params, annotated_univ_names)
                              with
                              | ([],[]) -> ed1
                              | uu____3762 ->
                                  let op uu____3794 =
                                    match uu____3794 with
                                    | (us,t) ->
                                        let n_us = FStar_List.length us  in
                                        let uu____3814 =
                                          let uu____3815 =
                                            FStar_Syntax_Subst.shift_subst
                                              n_us opening
                                             in
                                          let uu____3824 = open_univs n_us t
                                             in
                                          FStar_Syntax_Subst.subst uu____3815
                                            uu____3824
                                           in
                                        (us, uu____3814)
                                     in
                                  let uu___387_3833 = ed1  in
                                  let uu____3834 =
                                    let uu____3835 =
                                      let uu____3836 =
                                        op
                                          ([],
                                            ((ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m))
                                         in
                                      FStar_Pervasives_Native.snd uu____3836
                                       in
                                    let uu____3847 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                       in
                                    let uu____3848 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                       in
                                    {
                                      FStar_Syntax_Syntax.monad_m =
                                        uu____3835;
                                      FStar_Syntax_Syntax.monad_ret =
                                        uu____3847;
                                      FStar_Syntax_Syntax.monad_bind =
                                        uu____3848
                                    }  in
                                  let uu____3849 =
                                    op ed1.FStar_Syntax_Syntax.if_then_else
                                     in
                                  let uu____3850 =
                                    op ed1.FStar_Syntax_Syntax.ite_wp  in
                                  let uu____3851 =
                                    op ed1.FStar_Syntax_Syntax.stronger  in
                                  let uu____3852 =
                                    op ed1.FStar_Syntax_Syntax.close_wp  in
                                  let uu____3853 =
                                    op ed1.FStar_Syntax_Syntax.assert_p  in
                                  let uu____3854 =
                                    op ed1.FStar_Syntax_Syntax.assume_p  in
                                  let uu____3855 =
                                    op ed1.FStar_Syntax_Syntax.null_wp  in
                                  let uu____3856 =
                                    op ed1.FStar_Syntax_Syntax.trivial  in
                                  let uu____3857 =
                                    let uu____3858 =
                                      let uu____3859 =
                                        op
                                          ([],
                                            ((ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m))
                                         in
                                      FStar_Pervasives_Native.snd uu____3859
                                       in
                                    let uu____3870 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                       in
                                    let uu____3871 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                       in
                                    {
                                      FStar_Syntax_Syntax.monad_m =
                                        uu____3858;
                                      FStar_Syntax_Syntax.monad_ret =
                                        uu____3870;
                                      FStar_Syntax_Syntax.monad_bind =
                                        uu____3871
                                    }  in
                                  let uu____3872 =
                                    FStar_List.map
                                      (fun a  ->
                                         let uu___388_3880 = a  in
                                         let uu____3881 =
                                           let uu____3882 =
                                             op
                                               ((a.FStar_Syntax_Syntax.action_univs),
                                                 (a.FStar_Syntax_Syntax.action_defn))
                                              in
                                           FStar_Pervasives_Native.snd
                                             uu____3882
                                            in
                                         let uu____3893 =
                                           let uu____3894 =
                                             op
                                               ((a.FStar_Syntax_Syntax.action_univs),
                                                 (a.FStar_Syntax_Syntax.action_typ))
                                              in
                                           FStar_Pervasives_Native.snd
                                             uu____3894
                                            in
                                         {
                                           FStar_Syntax_Syntax.action_name =
                                             (uu___388_3880.FStar_Syntax_Syntax.action_name);
                                           FStar_Syntax_Syntax.action_unqualified_name
                                             =
                                             (uu___388_3880.FStar_Syntax_Syntax.action_unqualified_name);
                                           FStar_Syntax_Syntax.action_univs =
                                             (uu___388_3880.FStar_Syntax_Syntax.action_univs);
                                           FStar_Syntax_Syntax.action_params
                                             =
                                             (uu___388_3880.FStar_Syntax_Syntax.action_params);
                                           FStar_Syntax_Syntax.action_defn =
                                             uu____3881;
                                           FStar_Syntax_Syntax.action_typ =
                                             uu____3893
                                         }) ed1.FStar_Syntax_Syntax.actions
                                     in
                                  {
                                    FStar_Syntax_Syntax.cattributes =
                                      (uu___387_3833.FStar_Syntax_Syntax.cattributes);
                                    FStar_Syntax_Syntax.mname =
                                      (uu___387_3833.FStar_Syntax_Syntax.mname);
                                    FStar_Syntax_Syntax.univs =
                                      annotated_univ_names;
                                    FStar_Syntax_Syntax.binders =
                                      (uu___387_3833.FStar_Syntax_Syntax.binders);
                                    FStar_Syntax_Syntax.spec = uu____3834;
                                    FStar_Syntax_Syntax.signature =
                                      (uu___387_3833.FStar_Syntax_Syntax.signature);
                                    FStar_Syntax_Syntax.if_then_else =
                                      uu____3849;
                                    FStar_Syntax_Syntax.ite_wp = uu____3850;
                                    FStar_Syntax_Syntax.stronger = uu____3851;
                                    FStar_Syntax_Syntax.close_wp = uu____3852;
                                    FStar_Syntax_Syntax.assert_p = uu____3853;
                                    FStar_Syntax_Syntax.assume_p = uu____3854;
                                    FStar_Syntax_Syntax.null_wp = uu____3855;
                                    FStar_Syntax_Syntax.trivial = uu____3856;
                                    FStar_Syntax_Syntax.repr = uu____3857;
                                    FStar_Syntax_Syntax.elaborated =
                                      (uu___387_3833.FStar_Syntax_Syntax.elaborated);
                                    FStar_Syntax_Syntax.actions = uu____3872;
                                    FStar_Syntax_Syntax.eff_attrs =
                                      (uu___387_3833.FStar_Syntax_Syntax.eff_attrs)
                                  }
                               in
                            ((let uu____3906 =
                                FStar_TypeChecker_Env.debug env0
                                  (FStar_Options.Other "ED")
                                 in
                              if uu____3906
                              then
                                let uu____3910 =
                                  FStar_Syntax_Print.eff_decl_to_string ed2
                                   in
                                FStar_Util.print1
                                  "eff_decl after opening:\n\t%s\n"
                                  uu____3910
                              else ());
                             (let wp_with_fresh_result_type env2 mname
                                signature2 =
                                let fail1 t =
                                  let uu____3949 =
                                    FStar_TypeChecker_Err.unexpected_signature_for_monad
                                      env2 mname t
                                     in
                                  let uu____3955 =
                                    FStar_Ident.range_of_lid mname  in
                                  FStar_Errors.raise_error uu____3949
                                    uu____3955
                                   in
                                let uu____3962 =
                                  let uu____3963 =
                                    FStar_Syntax_Subst.compress signature2
                                     in
                                  uu____3963.FStar_Syntax_Syntax.n  in
                                match uu____3962 with
                                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                    let bs1 =
                                      FStar_Syntax_Subst.open_binders bs  in
                                    (match bs1 with
                                     | (a,uu____4002)::(wp,uu____4004)::[] ->
                                         (a, (wp.FStar_Syntax_Syntax.sort))
                                     | uu____4033 -> fail1 signature2)
                                | uu____4034 -> fail1 signature2  in
                              let uu____4035 =
                                wp_with_fresh_result_type env1
                                  ed2.FStar_Syntax_Syntax.mname signature1
                                 in
                              match uu____4035 with
                              | (a,wp_a) ->
                                  let fresh_effect_signature uu____4059 =
                                    match annotated_univ_names with
                                    | [] ->
                                        let uu____4066 =
                                          FStar_TypeChecker_TcTerm.tc_trivial_guard
                                            env1 signature_un
                                           in
                                        (match uu____4066 with
                                         | (signature2,uu____4078) ->
                                             wp_with_fresh_result_type env1
                                               ed2.FStar_Syntax_Syntax.mname
                                               signature2)
                                    | uu____4079 ->
                                        let uu____4082 =
                                          let uu____4087 =
                                            let uu____4088 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                annotated_univ_names
                                                signature1
                                               in
                                            (annotated_univ_names,
                                              uu____4088)
                                             in
                                          FStar_TypeChecker_Env.inst_tscheme
                                            uu____4087
                                           in
                                        (match uu____4082 with
                                         | (uu____4101,signature2) ->
                                             wp_with_fresh_result_type env1
                                               ed2.FStar_Syntax_Syntax.mname
                                               signature2)
                                     in
                                  let env2 =
                                    let uu____4104 =
                                      FStar_Syntax_Syntax.new_bv
                                        FStar_Pervasives_Native.None
                                        signature1
                                       in
                                    FStar_TypeChecker_Env.push_bv env1
                                      uu____4104
                                     in
                                  ((let uu____4106 =
                                      FStar_Syntax_Print.lid_to_string
                                        ed2.FStar_Syntax_Syntax.mname
                                       in
                                    let uu____4108 =
                                      FStar_Syntax_Print.binders_to_string
                                        " " ed2.FStar_Syntax_Syntax.binders
                                       in
                                    let uu____4111 =
                                      FStar_Syntax_Print.term_to_string
                                        signature1
                                       in
                                    let uu____4113 =
                                      let uu____4115 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____4115
                                       in
                                    let uu____4116 =
                                      FStar_Syntax_Print.term_to_string
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    FStar_Util.print5
                                      "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                      uu____4106 uu____4108 uu____4111
                                      uu____4113 uu____4116);
                                   (let check_and_gen' env3 uu____4149 k =
                                      match uu____4149 with
                                      | (us,t) ->
                                          (match annotated_univ_names with
                                           | [] -> check_and_gen env3 t k
                                           | uu____4185::uu____4186 ->
                                               let uu____4189 =
                                                 FStar_Syntax_Subst.subst_tscheme
                                                   open_annotated_univs
                                                   (us, t)
                                                  in
                                               (match uu____4189 with
                                                | (us1,t1) ->
                                                    let uu____4212 =
                                                      FStar_Syntax_Subst.open_univ_vars
                                                        us1 t1
                                                       in
                                                    (match uu____4212 with
                                                     | (us2,t2) ->
                                                         let uu____4227 =
                                                           let uu____4228 =
                                                             FStar_TypeChecker_Env.push_univ_vars
                                                               env3 us2
                                                              in
                                                           tc_check_trivial_guard
                                                             uu____4228 t2 k
                                                            in
                                                         let uu____4229 =
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             us2 t2
                                                            in
                                                         (us2, uu____4229))))
                                       in
                                    let return_wp =
                                      let expected_k =
                                        let uu____4248 =
                                          let uu____4257 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4264 =
                                            let uu____4273 =
                                              let uu____4280 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4280
                                               in
                                            [uu____4273]  in
                                          uu____4257 :: uu____4264  in
                                        let uu____4299 =
                                          FStar_Syntax_Syntax.mk_GTotal wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4248
                                          uu____4299
                                         in
                                      check_and_gen' env2
                                        (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                        expected_k
                                       in
                                    let bind_wp =
                                      let uu____4303 =
                                        fresh_effect_signature ()  in
                                      match uu____4303 with
                                      | (b,wp_b) ->
                                          let a_wp_b =
                                            let uu____4319 =
                                              let uu____4328 =
                                                let uu____4335 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____4335
                                                 in
                                              [uu____4328]  in
                                            let uu____4348 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_b
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4319 uu____4348
                                             in
                                          let expected_k =
                                            let uu____4354 =
                                              let uu____4363 =
                                                FStar_Syntax_Syntax.null_binder
                                                  FStar_Syntax_Syntax.t_range
                                                 in
                                              let uu____4370 =
                                                let uu____4379 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____4386 =
                                                  let uu____4395 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____4402 =
                                                    let uu____4411 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_a
                                                       in
                                                    let uu____4418 =
                                                      let uu____4427 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          a_wp_b
                                                         in
                                                      [uu____4427]  in
                                                    uu____4411 :: uu____4418
                                                     in
                                                  uu____4395 :: uu____4402
                                                   in
                                                uu____4379 :: uu____4386  in
                                              uu____4363 :: uu____4370  in
                                            let uu____4470 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_b
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4354 uu____4470
                                             in
                                          check_and_gen' env2
                                            (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                            expected_k
                                       in
                                    let if_then_else1 =
                                      let p =
                                        let uu____4483 =
                                          let uu____4486 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4486
                                           in
                                        let uu____4487 =
                                          let uu____4488 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4488
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4483
                                          uu____4487
                                         in
                                      let expected_k =
                                        let uu____4500 =
                                          let uu____4509 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4516 =
                                            let uu____4525 =
                                              FStar_Syntax_Syntax.mk_binder p
                                               in
                                            let uu____4532 =
                                              let uu____4541 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              let uu____4548 =
                                                let uu____4557 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____4557]  in
                                              uu____4541 :: uu____4548  in
                                            uu____4525 :: uu____4532  in
                                          uu____4509 :: uu____4516  in
                                        let uu____4594 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4500
                                          uu____4594
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.if_then_else
                                        expected_k
                                       in
                                    let ite_wp =
                                      let expected_k =
                                        let uu____4609 =
                                          let uu____4618 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4625 =
                                            let uu____4634 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____4634]  in
                                          uu____4618 :: uu____4625  in
                                        let uu____4659 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4609
                                          uu____4659
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.ite_wp
                                        expected_k
                                       in
                                    let stronger =
                                      let uu____4663 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____4663 with
                                      | (t,uu____4669) ->
                                          let expected_k =
                                            let uu____4673 =
                                              let uu____4682 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4689 =
                                                let uu____4698 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____4705 =
                                                  let uu____4714 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____4714]  in
                                                uu____4698 :: uu____4705  in
                                              uu____4682 :: uu____4689  in
                                            let uu____4745 =
                                              FStar_Syntax_Syntax.mk_Total t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4673 uu____4745
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.stronger
                                            expected_k
                                       in
                                    let close_wp =
                                      let b =
                                        let uu____4758 =
                                          let uu____4761 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4761
                                           in
                                        let uu____4762 =
                                          let uu____4763 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4763
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4758
                                          uu____4762
                                         in
                                      let b_wp_a =
                                        let uu____4775 =
                                          let uu____4784 =
                                            let uu____4791 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                b
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____4791
                                             in
                                          [uu____4784]  in
                                        let uu____4804 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4775
                                          uu____4804
                                         in
                                      let expected_k =
                                        let uu____4810 =
                                          let uu____4819 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4826 =
                                            let uu____4835 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4842 =
                                              let uu____4851 =
                                                FStar_Syntax_Syntax.null_binder
                                                  b_wp_a
                                                 in
                                              [uu____4851]  in
                                            uu____4835 :: uu____4842  in
                                          uu____4819 :: uu____4826  in
                                        let uu____4882 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4810
                                          uu____4882
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.close_wp
                                        expected_k
                                       in
                                    let assert_p =
                                      let expected_k =
                                        let uu____4897 =
                                          let uu____4906 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4913 =
                                            let uu____4922 =
                                              let uu____4929 =
                                                let uu____4930 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____4930
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4929
                                               in
                                            let uu____4939 =
                                              let uu____4948 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____4948]  in
                                            uu____4922 :: uu____4939  in
                                          uu____4906 :: uu____4913  in
                                        let uu____4979 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4897
                                          uu____4979
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.assert_p
                                        expected_k
                                       in
                                    let assume_p =
                                      let expected_k =
                                        let uu____4994 =
                                          let uu____5003 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____5010 =
                                            let uu____5019 =
                                              let uu____5026 =
                                                let uu____5027 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____5027
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____5026
                                               in
                                            let uu____5036 =
                                              let uu____5045 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____5045]  in
                                            uu____5019 :: uu____5036  in
                                          uu____5003 :: uu____5010  in
                                        let uu____5076 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4994
                                          uu____5076
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.assume_p
                                        expected_k
                                       in
                                    let null_wp =
                                      let expected_k =
                                        let uu____5091 =
                                          let uu____5100 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          [uu____5100]  in
                                        let uu____5119 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____5091
                                          uu____5119
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.null_wp
                                        expected_k
                                       in
                                    let trivial_wp =
                                      let uu____5123 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____5123 with
                                      | (t,uu____5129) ->
                                          let expected_k =
                                            let uu____5133 =
                                              let uu____5142 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____5149 =
                                                let uu____5158 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____5158]  in
                                              uu____5142 :: uu____5149  in
                                            let uu____5183 =
                                              FStar_Syntax_Syntax.mk_GTotal t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5133 uu____5183
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.trivial
                                            expected_k
                                       in
                                    let uu____5186 =
                                      let uu____5199 =
                                        let uu____5200 =
                                          FStar_Syntax_Subst.compress
                                            (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                           in
                                        uu____5200.FStar_Syntax_Syntax.n  in
                                      match uu____5199 with
                                      | FStar_Syntax_Syntax.Tm_unknown  ->
                                          (((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m),
                                            ((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind),
                                            ((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret),
                                            (ed2.FStar_Syntax_Syntax.actions))
                                      | uu____5219 ->
                                          let repr =
                                            let uu____5221 =
                                              FStar_Syntax_Util.type_u ()  in
                                            match uu____5221 with
                                            | (t,uu____5227) ->
                                                let expected_k =
                                                  let uu____5231 =
                                                    let uu____5240 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a
                                                       in
                                                    let uu____5247 =
                                                      let uu____5256 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          wp_a
                                                         in
                                                      [uu____5256]  in
                                                    uu____5240 :: uu____5247
                                                     in
                                                  let uu____5281 =
                                                    FStar_Syntax_Syntax.mk_GTotal
                                                      t
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____5231 uu____5281
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
                                            let uu____5298 =
                                              let uu____5305 =
                                                let uu____5306 =
                                                  let uu____5323 =
                                                    let uu____5334 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        t
                                                       in
                                                    let uu____5343 =
                                                      let uu____5354 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          wp
                                                         in
                                                      [uu____5354]  in
                                                    uu____5334 :: uu____5343
                                                     in
                                                  (repr1, uu____5323)  in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____5306
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____5305
                                               in
                                            uu____5298
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          let mk_repr a1 wp =
                                            let uu____5415 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            mk_repr' uu____5415 wp  in
                                          let destruct_repr t =
                                            let uu____5430 =
                                              let uu____5431 =
                                                FStar_Syntax_Subst.compress t
                                                 in
                                              uu____5431.FStar_Syntax_Syntax.n
                                               in
                                            match uu____5430 with
                                            | FStar_Syntax_Syntax.Tm_app
                                                (uu____5442,(t1,uu____5444)::
                                                 (wp,uu____5446)::[])
                                                -> (t1, wp)
                                            | uu____5505 ->
                                                failwith
                                                  "Unexpected repr type"
                                             in
                                          let bind_repr =
                                            let r =
                                              let uu____5517 =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  FStar_Parser_Const.range_0
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              FStar_All.pipe_right uu____5517
                                                FStar_Syntax_Syntax.fv_to_tm
                                               in
                                            let uu____5518 =
                                              fresh_effect_signature ()  in
                                            match uu____5518 with
                                            | (b,wp_b) ->
                                                let a_wp_b =
                                                  let uu____5534 =
                                                    let uu____5543 =
                                                      let uu____5550 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.null_binder
                                                        uu____5550
                                                       in
                                                    [uu____5543]  in
                                                  let uu____5563 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      wp_b
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____5534 uu____5563
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
                                                  let uu____5571 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "x_a"
                                                    FStar_Pervasives_Native.None
                                                    uu____5571
                                                   in
                                                let wp_g_x =
                                                  let uu____5576 =
                                                    let uu____5581 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        wp_g
                                                       in
                                                    let uu____5582 =
                                                      let uu____5583 =
                                                        let uu____5592 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Syntax.as_arg
                                                          uu____5592
                                                         in
                                                      [uu____5583]  in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____5581 uu____5582
                                                     in
                                                  uu____5576
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                let res =
                                                  let wp =
                                                    let uu____5625 =
                                                      let uu____5630 =
                                                        let uu____5631 =
                                                          FStar_TypeChecker_Env.inst_tscheme
                                                            bind_wp
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____5631
                                                          FStar_Pervasives_Native.snd
                                                         in
                                                      let uu____5640 =
                                                        let uu____5641 =
                                                          let uu____5644 =
                                                            let uu____5647 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                a
                                                               in
                                                            let uu____5648 =
                                                              let uu____5651
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  b
                                                                 in
                                                              let uu____5652
                                                                =
                                                                let uu____5655
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f
                                                                   in
                                                                let uu____5656
                                                                  =
                                                                  let uu____5659
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                  [uu____5659]
                                                                   in
                                                                uu____5655 ::
                                                                  uu____5656
                                                                 in
                                                              uu____5651 ::
                                                                uu____5652
                                                               in
                                                            uu____5647 ::
                                                              uu____5648
                                                             in
                                                          r :: uu____5644  in
                                                        FStar_List.map
                                                          FStar_Syntax_Syntax.as_arg
                                                          uu____5641
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____5630 uu____5640
                                                       in
                                                    uu____5625
                                                      FStar_Pervasives_Native.None
                                                      FStar_Range.dummyRange
                                                     in
                                                  mk_repr b wp  in
                                                let maybe_range_arg =
                                                  let uu____5679 =
                                                    FStar_Util.for_some
                                                      (FStar_Syntax_Util.attr_eq
                                                         FStar_Syntax_Util.dm4f_bind_range_attr)
                                                      ed2.FStar_Syntax_Syntax.eff_attrs
                                                     in
                                                  if uu____5679
                                                  then
                                                    let uu____5690 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        FStar_Syntax_Syntax.t_range
                                                       in
                                                    let uu____5697 =
                                                      let uu____5706 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          FStar_Syntax_Syntax.t_range
                                                         in
                                                      [uu____5706]  in
                                                    uu____5690 :: uu____5697
                                                  else []  in
                                                let expected_k =
                                                  let uu____5742 =
                                                    let uu____5751 =
                                                      let uu____5760 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a
                                                         in
                                                      let uu____5767 =
                                                        let uu____5776 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            b
                                                           in
                                                        [uu____5776]  in
                                                      uu____5760 ::
                                                        uu____5767
                                                       in
                                                    let uu____5801 =
                                                      let uu____5810 =
                                                        let uu____5819 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_f
                                                           in
                                                        let uu____5826 =
                                                          let uu____5835 =
                                                            let uu____5842 =
                                                              let uu____5843
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_f
                                                                 in
                                                              mk_repr a
                                                                uu____5843
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____5842
                                                             in
                                                          let uu____5844 =
                                                            let uu____5853 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_g
                                                               in
                                                            let uu____5860 =
                                                              let uu____5869
                                                                =
                                                                let uu____5876
                                                                  =
                                                                  let uu____5877
                                                                    =
                                                                    let uu____5886
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____5886]
                                                                     in
                                                                  let uu____5905
                                                                    =
                                                                    let uu____5908
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____5908
                                                                     in
                                                                  FStar_Syntax_Util.arrow
                                                                    uu____5877
                                                                    uu____5905
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____5876
                                                                 in
                                                              [uu____5869]
                                                               in
                                                            uu____5853 ::
                                                              uu____5860
                                                             in
                                                          uu____5835 ::
                                                            uu____5844
                                                           in
                                                        uu____5819 ::
                                                          uu____5826
                                                         in
                                                      FStar_List.append
                                                        maybe_range_arg
                                                        uu____5810
                                                       in
                                                    FStar_List.append
                                                      uu____5751 uu____5801
                                                     in
                                                  let uu____5953 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      res
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____5742 uu____5953
                                                   in
                                                let uu____5956 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env2 expected_k
                                                   in
                                                (match uu____5956 with
                                                 | (expected_k1,uu____5964,uu____5965)
                                                     ->
                                                     let env3 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env2
                                                         (FStar_Pervasives_Native.snd
                                                            (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind).FStar_Syntax_Syntax.pos
                                                        in
                                                     let env4 =
                                                       let uu___389_5972 =
                                                         env3  in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.is_pattern
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.is_pattern);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.instantiate_imp);
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           = true;
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___389_5972.FStar_TypeChecker_Env.nbe)
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
                                              let uu____5985 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____5985
                                               in
                                            let res =
                                              let wp =
                                                let uu____5993 =
                                                  let uu____5998 =
                                                    let uu____5999 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        return_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____5999
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____6008 =
                                                    let uu____6009 =
                                                      let uu____6012 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      let uu____6013 =
                                                        let uu____6016 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        [uu____6016]  in
                                                      uu____6012 ::
                                                        uu____6013
                                                       in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____6009
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____5998 uu____6008
                                                   in
                                                uu____5993
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr a wp  in
                                            let expected_k =
                                              let uu____6030 =
                                                let uu____6039 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____6046 =
                                                  let uu____6055 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x_a
                                                     in
                                                  [uu____6055]  in
                                                uu____6039 :: uu____6046  in
                                              let uu____6080 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____6030 uu____6080
                                               in
                                            let uu____6083 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k
                                               in
                                            match uu____6083 with
                                            | (expected_k1,uu____6091,uu____6092)
                                                ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env2
                                                    (FStar_Pervasives_Native.snd
                                                       (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret).FStar_Syntax_Syntax.pos
                                                   in
                                                let uu____6098 =
                                                  check_and_gen' env3
                                                    (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                                    expected_k1
                                                   in
                                                (match uu____6098 with
                                                 | (univs1,repr1) ->
                                                     (match univs1 with
                                                      | [] -> ([], repr1)
                                                      | uu____6121 ->
                                                          FStar_Errors.raise_error
                                                            (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                              "Unexpected universe-polymorphic return for effect")
                                                            repr1.FStar_Syntax_Syntax.pos))
                                             in
                                          let actions =
                                            let check_action act =
                                              let uu____6136 =
                                                if
                                                  act.FStar_Syntax_Syntax.action_univs
                                                    = []
                                                then (env2, act)
                                                else
                                                  (let uu____6150 =
                                                     FStar_Syntax_Subst.univ_var_opening
                                                       act.FStar_Syntax_Syntax.action_univs
                                                      in
                                                   match uu____6150 with
                                                   | (usubst,uvs) ->
                                                       let uu____6173 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env2 uvs
                                                          in
                                                       let uu____6174 =
                                                         let uu___390_6175 =
                                                           act  in
                                                         let uu____6176 =
                                                           FStar_Syntax_Subst.subst_binders
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_params
                                                            in
                                                         let uu____6177 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____6178 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_typ
                                                            in
                                                         {
                                                           FStar_Syntax_Syntax.action_name
                                                             =
                                                             (uu___390_6175.FStar_Syntax_Syntax.action_name);
                                                           FStar_Syntax_Syntax.action_unqualified_name
                                                             =
                                                             (uu___390_6175.FStar_Syntax_Syntax.action_unqualified_name);
                                                           FStar_Syntax_Syntax.action_univs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.action_params
                                                             = uu____6176;
                                                           FStar_Syntax_Syntax.action_defn
                                                             = uu____6177;
                                                           FStar_Syntax_Syntax.action_typ
                                                             = uu____6178
                                                         }  in
                                                       (uu____6173,
                                                         uu____6174))
                                                 in
                                              match uu____6136 with
                                              | (env3,act1) ->
                                                  let act_typ =
                                                    let uu____6182 =
                                                      let uu____6183 =
                                                        FStar_Syntax_Subst.compress
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                         in
                                                      uu____6183.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____6182 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,c) ->
                                                        let c1 =
                                                          FStar_Syntax_Util.comp_to_comp_typ
                                                            c
                                                           in
                                                        let uu____6209 =
                                                          FStar_Ident.lid_equals
                                                            c1.FStar_Syntax_Syntax.effect_name
                                                            ed2.FStar_Syntax_Syntax.mname
                                                           in
                                                        if uu____6209
                                                        then
                                                          let uu____6212 =
                                                            let uu____6215 =
                                                              let uu____6216
                                                                =
                                                                let uu____6217
                                                                  =
                                                                  FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____6217
                                                                 in
                                                              mk_repr'
                                                                c1.FStar_Syntax_Syntax.result_typ
                                                                uu____6216
                                                               in
                                                            FStar_Syntax_Syntax.mk_Total
                                                              uu____6215
                                                             in
                                                          FStar_Syntax_Util.arrow
                                                            bs uu____6212
                                                        else
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                    | uu____6240 ->
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  let uu____6241 =
                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                      env3 act_typ
                                                     in
                                                  (match uu____6241 with
                                                   | (act_typ1,uu____6249,g_t)
                                                       ->
                                                       let env' =
                                                         let uu___391_6252 =
                                                           FStar_TypeChecker_Env.set_expected_typ
                                                             env3 act_typ1
                                                            in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             = false;
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.lax);
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___391_6252.FStar_TypeChecker_Env.nbe)
                                                         }  in
                                                       ((let uu____6255 =
                                                           FStar_Ident.text_of_lid
                                                             act1.FStar_Syntax_Syntax.action_name
                                                            in
                                                         let uu____6257 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____6259 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act_typ1
                                                            in
                                                         FStar_Util.print3
                                                           "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                           uu____6255
                                                           uu____6257
                                                           uu____6259);
                                                        (let uu____6262 =
                                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                             env'
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         match uu____6262
                                                         with
                                                         | (act_defn,uu____6270,g_a)
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
                                                             let uu____6274 =
                                                               let act_typ3 =
                                                                 FStar_Syntax_Subst.compress
                                                                   act_typ2
                                                                  in
                                                               match 
                                                                 act_typ3.FStar_Syntax_Syntax.n
                                                               with
                                                               | FStar_Syntax_Syntax.Tm_arrow
                                                                   (bs,c) ->
                                                                   let uu____6310
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                   (match uu____6310
                                                                    with
                                                                    | 
                                                                    (bs1,uu____6322)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6329
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____6329
                                                                     in
                                                                    let uu____6332
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____6332
                                                                    with
                                                                    | 
                                                                    (k1,uu____6346,g)
                                                                    ->
                                                                    (k1, g)))
                                                               | uu____6350
                                                                   ->
                                                                   let uu____6351
                                                                    =
                                                                    let uu____6357
                                                                    =
                                                                    let uu____6359
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____6361
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____6359
                                                                    uu____6361
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____6357)
                                                                     in
                                                                   FStar_Errors.raise_error
                                                                    uu____6351
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                in
                                                             (match uu____6274
                                                              with
                                                              | (expected_k,g_k)
                                                                  ->
                                                                  let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env3
                                                                    act_typ2
                                                                    expected_k
                                                                     in
                                                                  ((let uu____6379
                                                                    =
                                                                    let uu____6380
                                                                    =
                                                                    let uu____6381
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____6381
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____6380
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env3
                                                                    uu____6379);
                                                                   (let act_typ3
                                                                    =
                                                                    let uu____6383
                                                                    =
                                                                    let uu____6384
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____6384.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____6383
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____6409
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____6409
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____6416
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____6416
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____6436
                                                                    =
                                                                    let uu____6437
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____6437]
                                                                     in
                                                                    let uu____6438
                                                                    =
                                                                    let uu____6449
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____6449]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6436;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6438;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____6474
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____6474))
                                                                    | 
                                                                    uu____6477
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____6479
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                    else
                                                                    (let uu____6501
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____6501))
                                                                     in
                                                                    match uu____6479
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
                                                                    let uu___392_6520
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___392_6520.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___392_6520.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___392_6520.FStar_Syntax_Syntax.action_params);
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
                                    match uu____5186 with
                                    | (repr,bind_repr,return_repr,actions) ->
                                        let t0 =
                                          let uu____6544 =
                                            FStar_Syntax_Syntax.mk_Total
                                              signature1
                                             in
                                          FStar_Syntax_Util.arrow
                                            ed2.FStar_Syntax_Syntax.binders
                                            uu____6544
                                           in
                                        let uu____6547 =
                                          let uu____6552 =
                                            FStar_TypeChecker_Util.generalize_universes
                                              env0 t0
                                             in
                                          match uu____6552 with
                                          | (gen_univs,t) ->
                                              (match annotated_univ_names
                                               with
                                               | [] -> (gen_univs, t)
                                               | uu____6571 ->
                                                   let uu____6574 =
                                                     ((FStar_List.length
                                                         gen_univs)
                                                        =
                                                        (FStar_List.length
                                                           annotated_univ_names))
                                                       &&
                                                       (FStar_List.forall2
                                                          (fun u1  ->
                                                             fun u2  ->
                                                               let uu____6581
                                                                 =
                                                                 FStar_Syntax_Syntax.order_univ_name
                                                                   u1 u2
                                                                  in
                                                               uu____6581 =
                                                                 (Prims.parse_int "0"))
                                                          gen_univs
                                                          annotated_univ_names)
                                                      in
                                                   if uu____6574
                                                   then (gen_univs, t)
                                                   else
                                                     (let uu____6592 =
                                                        let uu____6598 =
                                                          let uu____6600 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 annotated_univ_names)
                                                             in
                                                          let uu____6602 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 gen_univs)
                                                             in
                                                          FStar_Util.format2
                                                            "Expected an effect definition with %s universes; but found %s"
                                                            uu____6600
                                                            uu____6602
                                                           in
                                                        (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                          uu____6598)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____6592
                                                        signature1.FStar_Syntax_Syntax.pos))
                                           in
                                        (match uu____6547 with
                                         | (univs1,t) ->
                                             let signature2 =
                                               let uu____6613 =
                                                 let uu____6626 =
                                                   let uu____6627 =
                                                     FStar_Syntax_Subst.compress
                                                       t
                                                      in
                                                   uu____6627.FStar_Syntax_Syntax.n
                                                    in
                                                 (effect_params, uu____6626)
                                                  in
                                               match uu____6613 with
                                               | ([],uu____6638) -> t
                                               | (uu____6653,FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____6654,c)) ->
                                                   FStar_Syntax_Util.comp_result
                                                     c
                                               | uu____6692 ->
                                                   failwith
                                                     "Impossible : t is an arrow"
                                                in
                                             let close1 n1 ts =
                                               let ts1 =
                                                 let uu____6720 =
                                                   FStar_Syntax_Subst.close_tscheme
                                                     effect_params ts
                                                    in
                                                 FStar_Syntax_Subst.close_univ_vars_tscheme
                                                   univs1 uu____6720
                                                  in
                                               let m =
                                                 FStar_List.length
                                                   (FStar_Pervasives_Native.fst
                                                      ts1)
                                                  in
                                               (let uu____6727 =
                                                  ((n1 >=
                                                      (Prims.parse_int "0"))
                                                     &&
                                                     (let uu____6731 =
                                                        FStar_Syntax_Util.is_unknown
                                                          (FStar_Pervasives_Native.snd
                                                             ts1)
                                                         in
                                                      Prims.op_Negation
                                                        uu____6731))
                                                    && (m <> n1)
                                                   in
                                                if uu____6727
                                                then
                                                  let error =
                                                    if m < n1
                                                    then
                                                      "not universe-polymorphic enough"
                                                    else
                                                      "too universe-polymorphic"
                                                     in
                                                  let err_msg =
                                                    let uu____6759 =
                                                      FStar_Util.string_of_int
                                                        m
                                                       in
                                                    let uu____6767 =
                                                      FStar_Util.string_of_int
                                                        n1
                                                       in
                                                    let uu____6769 =
                                                      FStar_Syntax_Print.tscheme_to_string
                                                        ts1
                                                       in
                                                    FStar_Util.format4
                                                      "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                      error uu____6759
                                                      uu____6767 uu____6769
                                                     in
                                                  FStar_Errors.raise_error
                                                    (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                      err_msg)
                                                    (FStar_Pervasives_Native.snd
                                                       ts1).FStar_Syntax_Syntax.pos
                                                else ());
                                               ts1  in
                                             let close_action act =
                                               let uu____6785 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               match uu____6785 with
                                               | (univs2,defn) ->
                                                   let uu____6801 =
                                                     close1
                                                       (~-
                                                          (Prims.parse_int "1"))
                                                       ((act.FStar_Syntax_Syntax.action_univs),
                                                         (act.FStar_Syntax_Syntax.action_typ))
                                                      in
                                                   (match uu____6801 with
                                                    | (univs',typ) ->
                                                        let uu___393_6818 =
                                                          act  in
                                                        {
                                                          FStar_Syntax_Syntax.action_name
                                                            =
                                                            (uu___393_6818.FStar_Syntax_Syntax.action_name);
                                                          FStar_Syntax_Syntax.action_unqualified_name
                                                            =
                                                            (uu___393_6818.FStar_Syntax_Syntax.action_unqualified_name);
                                                          FStar_Syntax_Syntax.action_univs
                                                            = univs2;
                                                          FStar_Syntax_Syntax.action_params
                                                            =
                                                            (uu___393_6818.FStar_Syntax_Syntax.action_params);
                                                          FStar_Syntax_Syntax.action_defn
                                                            = defn;
                                                          FStar_Syntax_Syntax.action_typ
                                                            = typ
                                                        })
                                                in
                                             let ed3 =
                                               let uu___394_6821 = ed2  in
                                               let uu____6822 =
                                                 let uu____6823 =
                                                   close1
                                                     (Prims.parse_int "0")
                                                     return_wp
                                                    in
                                                 let uu____6825 =
                                                   close1
                                                     (Prims.parse_int "1")
                                                     bind_wp
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     =
                                                     FStar_Syntax_Syntax.tun;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____6823;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____6825
                                                 }  in
                                               let uu____6827 =
                                                 close1 (Prims.parse_int "0")
                                                   if_then_else1
                                                  in
                                               let uu____6829 =
                                                 close1 (Prims.parse_int "0")
                                                   ite_wp
                                                  in
                                               let uu____6831 =
                                                 close1 (Prims.parse_int "0")
                                                   stronger
                                                  in
                                               let uu____6833 =
                                                 close1 (Prims.parse_int "1")
                                                   close_wp
                                                  in
                                               let uu____6835 =
                                                 close1 (Prims.parse_int "0")
                                                   assert_p
                                                  in
                                               let uu____6837 =
                                                 close1 (Prims.parse_int "0")
                                                   assume_p
                                                  in
                                               let uu____6839 =
                                                 close1 (Prims.parse_int "0")
                                                   null_wp
                                                  in
                                               let uu____6841 =
                                                 close1 (Prims.parse_int "0")
                                                   trivial_wp
                                                  in
                                               let uu____6843 =
                                                 let uu____6844 =
                                                   let uu____6845 =
                                                     close1
                                                       (Prims.parse_int "0")
                                                       ([], repr)
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____6845
                                                    in
                                                 let uu____6863 =
                                                   close1
                                                     (Prims.parse_int "0")
                                                     return_repr
                                                    in
                                                 let uu____6865 =
                                                   close1
                                                     (Prims.parse_int "1")
                                                     bind_repr
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     = uu____6844;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____6863;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____6865
                                                 }  in
                                               let uu____6867 =
                                                 FStar_List.map close_action
                                                   actions
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.cattributes
                                                   =
                                                   (uu___394_6821.FStar_Syntax_Syntax.cattributes);
                                                 FStar_Syntax_Syntax.mname =
                                                   (uu___394_6821.FStar_Syntax_Syntax.mname);
                                                 FStar_Syntax_Syntax.univs =
                                                   univs1;
                                                 FStar_Syntax_Syntax.binders
                                                   = effect_params;
                                                 FStar_Syntax_Syntax.spec =
                                                   uu____6822;
                                                 FStar_Syntax_Syntax.signature
                                                   = signature2;
                                                 FStar_Syntax_Syntax.if_then_else
                                                   = uu____6827;
                                                 FStar_Syntax_Syntax.ite_wp =
                                                   uu____6829;
                                                 FStar_Syntax_Syntax.stronger
                                                   = uu____6831;
                                                 FStar_Syntax_Syntax.close_wp
                                                   = uu____6833;
                                                 FStar_Syntax_Syntax.assert_p
                                                   = uu____6835;
                                                 FStar_Syntax_Syntax.assume_p
                                                   = uu____6837;
                                                 FStar_Syntax_Syntax.null_wp
                                                   = uu____6839;
                                                 FStar_Syntax_Syntax.trivial
                                                   = uu____6841;
                                                 FStar_Syntax_Syntax.repr =
                                                   uu____6843;
                                                 FStar_Syntax_Syntax.elaborated
                                                   =
                                                   (uu___394_6821.FStar_Syntax_Syntax.elaborated);
                                                 FStar_Syntax_Syntax.actions
                                                   = uu____6867;
                                                 FStar_Syntax_Syntax.eff_attrs
                                                   =
                                                   (uu___394_6821.FStar_Syntax_Syntax.eff_attrs)
                                               }  in
                                             ((let uu____6871 =
                                                 FStar_Syntax_Print.eff_decl_to_string
                                                   ed3
                                                  in
                                               FStar_Util.print_string
                                                 uu____6871);
                                              ed3))))))))))
  
let tc_lex_t :
  'Auu____6884 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____6884 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____6919 = FStar_List.hd ses  in
            uu____6919.FStar_Syntax_Syntax.sigrng  in
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
           | uu____6924 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____6930,[],t,uu____6932,uu____6933);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____6935;
               FStar_Syntax_Syntax.sigattrs = uu____6936;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____6938,_t_top,_lex_t_top,_0_1,uu____6941);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____6943;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____6944;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____6946,_t_cons,_lex_t_cons,_0_2,uu____6949);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____6951;
                 FStar_Syntax_Syntax.sigattrs = uu____6952;_}::[]
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
                 let uu____7003 =
                   let uu____7010 =
                     let uu____7011 =
                       let uu____7018 =
                         let uu____7021 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____7021
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____7018, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____7011  in
                   FStar_Syntax_Syntax.mk uu____7010  in
                 uu____7003 FStar_Pervasives_Native.None r1  in
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
                   let uu____7039 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7039
                    in
                 let hd1 =
                   let uu____7041 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7041
                    in
                 let tl1 =
                   let uu____7043 =
                     let uu____7044 =
                       let uu____7051 =
                         let uu____7052 =
                           let uu____7059 =
                             let uu____7062 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____7062
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____7059, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____7052  in
                       FStar_Syntax_Syntax.mk uu____7051  in
                     uu____7044 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7043
                    in
                 let res =
                   let uu____7071 =
                     let uu____7078 =
                       let uu____7079 =
                         let uu____7086 =
                           let uu____7089 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____7089
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____7086,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____7079  in
                     FStar_Syntax_Syntax.mk uu____7078  in
                   uu____7071 FStar_Pervasives_Native.None r2  in
                 let uu____7095 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____7095
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
               let uu____7134 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____7134;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____7139 ->
               let err_msg =
                 let uu____7144 =
                   let uu____7146 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____7146  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____7144
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
    fun uu____7171  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____7171 with
          | (uvs,t) ->
              let uu____7184 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____7184 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____7196 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____7196 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____7214 =
                        let uu____7217 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____7217
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____7214)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7240 =
          let uu____7241 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7241 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7240 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7266 =
          let uu____7267 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7267 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7266 r
  
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
          (let uu____7316 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____7316
           then
             let uu____7319 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____7319
           else ());
          (let uu____7324 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____7324 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____7355 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____7355 FStar_List.flatten  in
               ((let uu____7369 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____7372 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____7372)
                    in
                 if uu____7369
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
                           let uu____7388 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____7398,uu____7399,uu____7400,uu____7401,uu____7402)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____7411 -> failwith "Impossible!"  in
                           match uu____7388 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.strcat "Inductive type "
                                      (Prims.strcat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____7430 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____7440,uu____7441,ty_lid,uu____7443,uu____7444)
                               -> (data_lid, ty_lid)
                           | uu____7451 -> failwith "Impossible"  in
                         match uu____7430 with
                         | (data_lid,ty_lid) ->
                             let uu____7459 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____7462 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____7462)
                                in
                             if uu____7459
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.strcat "Exception "
                                      (Prims.strcat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____7476 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____7481,uu____7482,uu____7483,uu____7484,uu____7485)
                         -> lid
                     | uu____7494 -> failwith "Impossible"  in
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
                   let uu____7512 =
                     (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____7512
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
          let pop1 uu____7587 =
            let uu____7588 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___396_7598  ->
               match () with
               | () ->
                   let uu____7605 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____7605 (fun r  -> pop1 (); r)) ()
          with | uu___395_7636 -> (pop1 (); FStar_Exn.raise uu___395_7636)
  
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en  ->
    let env =
      let uu____7657 = FStar_Options.using_facts_from ()  in
      FStar_TypeChecker_Env.set_proof_ns uu____7657 en  in
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
      | uu____7961 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____8019 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____8019 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____8044 .
    'Auu____8044 FStar_Pervasives_Native.option -> 'Auu____8044 Prims.list
  =
  fun uu___374_8053  ->
    match uu___374_8053 with
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
            let uu____8133 = collect1 tl1  in
            (match uu____8133 with
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
        | ((e,n1)::uu____8371,[]) ->
            FStar_Pervasives_Native.Some (e, n1, (Prims.parse_int "0"))
        | ([],(e,n1)::uu____8427) ->
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
          let uu____8655 =
            let uu____8657 = FStar_Options.ide ()  in
            Prims.op_Negation uu____8657  in
          if uu____8655
          then
            let uu____8660 =
              let uu____8665 = FStar_TypeChecker_Env.dsenv env  in
              let uu____8666 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____8665 uu____8666  in
            (match uu____8660 with
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
                              let uu____8699 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____8700 =
                                let uu____8706 =
                                  let uu____8708 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____8710 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____8708 uu____8710
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____8706)
                                 in
                              FStar_Errors.log_issue uu____8699 uu____8700
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____8717 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____8718 =
                                   let uu____8724 =
                                     let uu____8726 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____8726
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____8724)
                                    in
                                 FStar_Errors.log_issue uu____8717 uu____8718)
                              else ())
                         else ())))
          else ()
      | uu____8736 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____8781 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____8809 ->
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
             let uu____8869 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____8869
             then
               let ses1 =
                 let uu____8877 =
                   let uu____8878 =
                     let uu____8879 =
                       tc_inductive
                         (let uu___397_8888 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___397_8888.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___397_8888.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___397_8888.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___397_8888.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___397_8888.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___397_8888.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___397_8888.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___397_8888.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___397_8888.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___397_8888.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___397_8888.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___397_8888.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___397_8888.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___397_8888.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___397_8888.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___397_8888.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___397_8888.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___397_8888.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___397_8888.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___397_8888.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___397_8888.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___397_8888.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___397_8888.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___397_8888.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___397_8888.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___397_8888.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___397_8888.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___397_8888.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___397_8888.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___397_8888.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___397_8888.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___397_8888.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___397_8888.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___397_8888.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___397_8888.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___397_8888.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___397_8888.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___397_8888.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___397_8888.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___397_8888.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___397_8888.FStar_TypeChecker_Env.nbe)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____8879
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____8878
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____8877
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____8902 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____8902
                 then
                   let uu____8907 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___398_8911 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___398_8911.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___398_8911.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___398_8911.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___398_8911.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____8907
                 else ());
                ses1)
             else ses  in
           let uu____8921 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____8921 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___399_8945 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___399_8945.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___399_8945.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___399_8945.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___399_8945.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let forfree =
             let uu____8959 =
               let uu____8960 =
                 FStar_Syntax_Subst.compress
                   (ne.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                  in
               uu____8960.FStar_Syntax_Syntax.n  in
             match uu____8959 with
             | FStar_Syntax_Syntax.Tm_unknown  -> false
             | uu____8965 ->
                 Prims.op_Negation ne.FStar_Syntax_Syntax.elaborated
              in
           if forfree
           then
             let uu____8977 = cps_and_elaborate_ed env0 ne  in
             (match uu____8977 with
              | (ses,ne1,lift_from_pure_opt) ->
                  let ne2 =
                    let uu___400_9010 = ne1  in
                    {
                      FStar_Syntax_Syntax.cattributes =
                        (uu___400_9010.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.mname =
                        (uu___400_9010.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.univs =
                        (uu___400_9010.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___400_9010.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.spec =
                        (uu___400_9010.FStar_Syntax_Syntax.spec);
                      FStar_Syntax_Syntax.signature =
                        (uu___400_9010.FStar_Syntax_Syntax.signature);
                      FStar_Syntax_Syntax.if_then_else =
                        (uu___400_9010.FStar_Syntax_Syntax.if_then_else);
                      FStar_Syntax_Syntax.ite_wp =
                        (uu___400_9010.FStar_Syntax_Syntax.ite_wp);
                      FStar_Syntax_Syntax.stronger =
                        (uu___400_9010.FStar_Syntax_Syntax.stronger);
                      FStar_Syntax_Syntax.close_wp =
                        (uu___400_9010.FStar_Syntax_Syntax.close_wp);
                      FStar_Syntax_Syntax.assert_p =
                        (uu___400_9010.FStar_Syntax_Syntax.assert_p);
                      FStar_Syntax_Syntax.assume_p =
                        (uu___400_9010.FStar_Syntax_Syntax.assume_p);
                      FStar_Syntax_Syntax.null_wp =
                        (uu___400_9010.FStar_Syntax_Syntax.null_wp);
                      FStar_Syntax_Syntax.trivial =
                        (uu___400_9010.FStar_Syntax_Syntax.trivial);
                      FStar_Syntax_Syntax.repr =
                        (uu___400_9010.FStar_Syntax_Syntax.repr);
                      FStar_Syntax_Syntax.elaborated = true;
                      FStar_Syntax_Syntax.actions =
                        (uu___400_9010.FStar_Syntax_Syntax.actions);
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___400_9010.FStar_Syntax_Syntax.eff_attrs)
                    }  in
                  let effect_and_lift_ses =
                    match lift_from_pure_opt with
                    | FStar_Pervasives_Native.Some lift ->
                        [(let uu___401_9019 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne2);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___401_9019.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___401_9019.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___401_9019.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___401_9019.FStar_Syntax_Syntax.sigattrs)
                          });
                        lift]
                    | FStar_Pervasives_Native.None  ->
                        [(let uu___402_9021 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_new_effect ne2);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___402_9021.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___402_9021.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___402_9021.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___402_9021.FStar_Syntax_Syntax.sigattrs)
                          })]
                     in
                  ([], (FStar_List.append ses effect_and_lift_ses), env0))
           else
             (let ne1 =
                let uu____9029 =
                  (FStar_Options.use_two_phase_tc ()) &&
                    (FStar_TypeChecker_Env.should_verify env)
                   in
                if uu____9029
                then
                  let ne1 =
                    let uu____9033 =
                      let uu____9034 =
                        let uu____9035 =
                          tc_eff_decl
                            (let uu___403_9037 = env  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___403_9037.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___403_9037.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___403_9037.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___403_9037.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___403_9037.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___403_9037.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___403_9037.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___403_9037.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___403_9037.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___403_9037.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___403_9037.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___403_9037.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___403_9037.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___403_9037.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___403_9037.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___403_9037.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___403_9037.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___403_9037.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___403_9037.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___403_9037.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___403_9037.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 = true;
                               FStar_TypeChecker_Env.failhard =
                                 (uu___403_9037.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___403_9037.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___403_9037.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___403_9037.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___403_9037.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___403_9037.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___403_9037.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___403_9037.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___403_9037.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___403_9037.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___403_9037.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___403_9037.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___403_9037.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___403_9037.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___403_9037.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___403_9037.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___403_9037.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___403_9037.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___403_9037.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___403_9037.FStar_TypeChecker_Env.nbe)
                             }) se ne
                           in
                        FStar_All.pipe_right uu____9035
                          (fun ne1  ->
                             let uu___404_9043 = se  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___404_9043.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___404_9043.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___404_9043.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___404_9043.FStar_Syntax_Syntax.sigattrs)
                             })
                         in
                      FStar_All.pipe_right uu____9034
                        (FStar_TypeChecker_Normalize.elim_uvars env)
                       in
                    FStar_All.pipe_right uu____9033
                      FStar_Syntax_Util.eff_decl_of_new_effect
                     in
                  ((let uu____9045 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "TwoPhases")
                       in
                    if uu____9045
                    then
                      let uu____9050 =
                        FStar_Syntax_Print.sigelt_to_string
                          (let uu___405_9054 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne1);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___405_9054.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___405_9054.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___405_9054.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___405_9054.FStar_Syntax_Syntax.sigattrs)
                           })
                         in
                      FStar_Util.print1 "Effect decl after phase 1: %s\n"
                        uu____9050
                    else ());
                   ne1)
                else ne  in
              let ne2 = tc_eff_decl env se ne1  in
              let se1 =
                let uu___406_9062 = se  in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_new_effect ne2);
                  FStar_Syntax_Syntax.sigrng =
                    (uu___406_9062.FStar_Syntax_Syntax.sigrng);
                  FStar_Syntax_Syntax.sigquals =
                    (uu___406_9062.FStar_Syntax_Syntax.sigquals);
                  FStar_Syntax_Syntax.sigmeta =
                    (uu___406_9062.FStar_Syntax_Syntax.sigmeta);
                  FStar_Syntax_Syntax.sigattrs =
                    (uu___406_9062.FStar_Syntax_Syntax.sigattrs)
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
           let uu____9070 =
             let uu____9077 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9077
              in
           (match uu____9070 with
            | (a,wp_a_src) ->
                let uu____9094 =
                  let uu____9101 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____9101
                   in
                (match uu____9094 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____9119 =
                         let uu____9122 =
                           let uu____9123 =
                             let uu____9130 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____9130)  in
                           FStar_Syntax_Syntax.NT uu____9123  in
                         [uu____9122]  in
                       FStar_Syntax_Subst.subst uu____9119 wp_b_tgt  in
                     let expected_k =
                       let uu____9138 =
                         let uu____9147 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____9154 =
                           let uu____9163 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____9163]  in
                         uu____9147 :: uu____9154  in
                       let uu____9188 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____9138 uu____9188  in
                     let repr_type eff_name a1 wp =
                       (let uu____9210 =
                          let uu____9212 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____9212  in
                        if uu____9210
                        then
                          let uu____9215 =
                            let uu____9221 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____9221)
                             in
                          let uu____9225 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____9215 uu____9225
                        else ());
                       (let uu____9228 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____9228 with
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
                            let uu____9265 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____9266 =
                              let uu____9273 =
                                let uu____9274 =
                                  let uu____9291 =
                                    let uu____9302 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____9311 =
                                      let uu____9322 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____9322]  in
                                    uu____9302 :: uu____9311  in
                                  (repr, uu____9291)  in
                                FStar_Syntax_Syntax.Tm_app uu____9274  in
                              FStar_Syntax_Syntax.mk uu____9273  in
                            uu____9266 FStar_Pervasives_Native.None
                              uu____9265)
                        in
                     let uu____9370 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____9543 =
                             if
                               (FStar_List.length uvs) >
                                 (Prims.parse_int "0")
                             then
                               let uu____9554 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____9554 with
                               | (usubst,uvs1) ->
                                   let uu____9577 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____9578 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____9577, uu____9578)
                             else (env, lift_wp)  in
                           (match uu____9543 with
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
                                     let uu____9628 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____9628))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____9699 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____9714 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____9714 with
                               | (usubst,uvs) ->
                                   let uu____9739 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____9739)
                             else ([], lift)  in
                           (match uu____9699 with
                            | (uvs,lift1) ->
                                ((let uu____9775 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____9775
                                  then
                                    let uu____9779 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____9779
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____9785 =
                                    let uu____9792 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____9792 lift1
                                     in
                                  match uu____9785 with
                                  | (lift2,comp,uu____9817) ->
                                      let uu____9818 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____9818 with
                                       | (uu____9847,lift_wp,lift_elab) ->
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
                                             let uu____9879 =
                                               let uu____9890 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____9890
                                                in
                                             let uu____9907 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____9879, uu____9907)
                                           else
                                             (let uu____9936 =
                                                let uu____9947 =
                                                  let uu____9956 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____9956)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____9947
                                                 in
                                              let uu____9971 =
                                                let uu____9980 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____9980)  in
                                              (uu____9936, uu____9971))))))
                        in
                     (match uu____9370 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___407_10054 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___407_10054.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___407_10054.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___407_10054.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___407_10054.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___407_10054.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___407_10054.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___407_10054.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___407_10054.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___407_10054.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___407_10054.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___407_10054.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___407_10054.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___407_10054.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___407_10054.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___407_10054.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___407_10054.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___407_10054.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___407_10054.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___407_10054.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___407_10054.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___407_10054.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___407_10054.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___407_10054.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___407_10054.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___407_10054.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___407_10054.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___407_10054.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___407_10054.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___407_10054.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___407_10054.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___407_10054.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___407_10054.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___407_10054.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___407_10054.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___407_10054.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___407_10054.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___407_10054.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___407_10054.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___407_10054.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___407_10054.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___407_10054.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___407_10054.FStar_TypeChecker_Env.nbe)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____10087 =
                                  let uu____10092 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____10092 with
                                  | (usubst,uvs1) ->
                                      let uu____10115 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____10116 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____10115, uu____10116)
                                   in
                                (match uu____10087 with
                                 | (env2,lift2) ->
                                     let uu____10121 =
                                       let uu____10128 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____10128
                                        in
                                     (match uu____10121 with
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
                                              let uu____10154 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____10155 =
                                                let uu____10162 =
                                                  let uu____10163 =
                                                    let uu____10180 =
                                                      let uu____10191 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____10200 =
                                                        let uu____10211 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____10211]  in
                                                      uu____10191 ::
                                                        uu____10200
                                                       in
                                                    (lift_wp1, uu____10180)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10163
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____10162
                                                 in
                                              uu____10155
                                                FStar_Pervasives_Native.None
                                                uu____10154
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____10262 =
                                              let uu____10271 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____10278 =
                                                let uu____10287 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____10294 =
                                                  let uu____10303 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____10303]  in
                                                uu____10287 :: uu____10294
                                                 in
                                              uu____10271 :: uu____10278  in
                                            let uu____10334 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____10262 uu____10334
                                             in
                                          let uu____10337 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____10337 with
                                           | (expected_k2,uu____10347,uu____10348)
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
                                                    let uu____10356 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____10356))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____10364 =
                              let uu____10366 =
                                let uu____10368 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____10368
                                  FStar_List.length
                                 in
                              uu____10366 <> (Prims.parse_int "1")  in
                            if uu____10364
                            then
                              let uu____10390 =
                                let uu____10396 =
                                  let uu____10398 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10400 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10402 =
                                    let uu____10404 =
                                      let uu____10406 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10406
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10404
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10398 uu____10400 uu____10402
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10396)
                                 in
                              FStar_Errors.raise_error uu____10390 r
                            else ());
                           (let uu____10433 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____10436 =
                                   let uu____10438 =
                                     let uu____10441 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____10441
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____10438
                                     FStar_List.length
                                    in
                                 uu____10436 <> (Prims.parse_int "1"))
                               in
                            if uu____10433
                            then
                              let uu____10479 =
                                let uu____10485 =
                                  let uu____10487 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10489 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10491 =
                                    let uu____10493 =
                                      let uu____10495 =
                                        let uu____10498 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____10498
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10495
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10493
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10487 uu____10489 uu____10491
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10485)
                                 in
                              FStar_Errors.raise_error uu____10479 r
                            else ());
                           (let sub2 =
                              let uu___408_10541 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___408_10541.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___408_10541.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___409_10543 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___409_10543.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___409_10543.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___409_10543.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___409_10543.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let uu____10557 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (env, uvs, tps, c)
             else
               (let uu____10585 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____10585 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____10616 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____10616 c  in
                    let uu____10625 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____10625, uvs1, tps1, c1))
              in
           (match uu____10557 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____10647 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____10647 with
                 | (tps2,c2) ->
                     let uu____10664 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____10664 with
                      | (tps3,env3,us) ->
                          let uu____10684 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____10684 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____10712)::uu____10713 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____10732 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____10740 =
                                   let uu____10742 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____10742  in
                                 if uu____10740
                                 then
                                   let uu____10745 =
                                     let uu____10751 =
                                       let uu____10753 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____10755 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____10753 uu____10755
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____10751)
                                      in
                                   FStar_Errors.raise_error uu____10745 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____10763 =
                                   let uu____10764 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____10764
                                    in
                                 match uu____10763 with
                                 | (uvs2,t) ->
                                     let uu____10795 =
                                       let uu____10800 =
                                         let uu____10813 =
                                           let uu____10814 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10814.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____10813)  in
                                       match uu____10800 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____10829,c5)) -> ([], c5)
                                       | (uu____10871,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____10910 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____10795 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____10944 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____10944 with
                                              | (uu____10949,t1) ->
                                                  let uu____10951 =
                                                    let uu____10957 =
                                                      let uu____10959 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____10961 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____10965 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____10959
                                                        uu____10961
                                                        uu____10965
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____10957)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____10951 r)
                                           else ();
                                           (let se1 =
                                              let uu___410_10972 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags1));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___410_10972.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___410_10972.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___410_10972.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___410_10972.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____10979,uu____10980,uu____10981) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___375_10986  ->
                   match uu___375_10986 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____10989 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____10995,uu____10996) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___375_11005  ->
                   match uu___375_11005 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11008 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____11019 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____11019
             then
               let uu____11022 =
                 let uu____11028 =
                   let uu____11030 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____11030
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____11028)
                  in
               FStar_Errors.raise_error uu____11022 r
             else ());
            (let uu____11036 =
               let uu____11045 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____11045
               then
                 let uu____11056 =
                   tc_declare_typ
                     (let uu___411_11059 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___411_11059.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___411_11059.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___411_11059.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___411_11059.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___411_11059.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___411_11059.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___411_11059.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___411_11059.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___411_11059.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___411_11059.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___411_11059.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___411_11059.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___411_11059.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___411_11059.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___411_11059.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___411_11059.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___411_11059.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___411_11059.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___411_11059.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___411_11059.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___411_11059.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___411_11059.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___411_11059.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___411_11059.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___411_11059.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___411_11059.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___411_11059.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___411_11059.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___411_11059.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___411_11059.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___411_11059.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___411_11059.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___411_11059.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___411_11059.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___411_11059.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___411_11059.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___411_11059.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___411_11059.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___411_11059.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___411_11059.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___411_11059.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___411_11059.FStar_TypeChecker_Env.nbe)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____11056 with
                 | (uvs1,t1) ->
                     ((let uu____11084 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____11084
                       then
                         let uu____11089 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____11091 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____11089 uu____11091
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____11036 with
             | (uvs1,t1) ->
                 let uu____11126 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____11126 with
                  | (uvs2,t2) ->
                      ([(let uu___412_11156 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___412_11156.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___412_11156.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___412_11156.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___412_11156.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____11161 =
             let uu____11170 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____11170
             then
               let uu____11181 =
                 tc_assume
                   (let uu___413_11184 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___413_11184.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___413_11184.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___413_11184.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___413_11184.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___413_11184.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___413_11184.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___413_11184.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___413_11184.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___413_11184.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___413_11184.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___413_11184.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___413_11184.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___413_11184.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___413_11184.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___413_11184.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___413_11184.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___413_11184.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___413_11184.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___413_11184.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___413_11184.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___413_11184.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___413_11184.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___413_11184.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___413_11184.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___413_11184.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___413_11184.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___413_11184.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___413_11184.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___413_11184.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___413_11184.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___413_11184.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___413_11184.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___413_11184.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___413_11184.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___413_11184.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___413_11184.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___413_11184.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___413_11184.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___413_11184.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___413_11184.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___413_11184.FStar_TypeChecker_Env.nbe)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____11181 with
               | (uvs1,t1) ->
                   ((let uu____11210 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____11210
                     then
                       let uu____11215 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____11217 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____11215
                         uu____11217
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____11161 with
            | (uvs1,t1) ->
                let uu____11252 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____11252 with
                 | (uvs2,t2) ->
                     ([(let uu___414_11282 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___414_11282.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___414_11282.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___414_11282.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___414_11282.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____11286 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____11286 with
            | (e1,c,g1) ->
                let uu____11306 =
                  let uu____11313 =
                    let uu____11316 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____11316  in
                  let uu____11317 =
                    let uu____11322 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____11322)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____11313 uu____11317
                   in
                (match uu____11306 with
                 | (e2,uu____11334,g) ->
                     ((let uu____11337 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____11337);
                      (let se1 =
                         let uu___415_11339 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___415_11339.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___415_11339.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___415_11339.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___415_11339.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____11351 = FStar_Options.debug_any ()  in
             if uu____11351
             then
               let uu____11354 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____11356 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____11354
                 uu____11356
             else ());
            (let uu____11361 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____11361 with
             | (t1,uu____11379,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____11393 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____11393 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____11396 =
                              let uu____11402 =
                                let uu____11404 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____11406 =
                                  let uu____11408 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____11408
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____11404 uu____11406
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____11402)
                               in
                            FStar_Errors.raise_error uu____11396 r
                        | uu____11420 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___416_11425 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___416_11425.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___416_11425.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___416_11425.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___416_11425.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___416_11425.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___416_11425.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___416_11425.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___416_11425.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___416_11425.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___416_11425.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___416_11425.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___416_11425.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___416_11425.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___416_11425.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___416_11425.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___416_11425.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___416_11425.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___416_11425.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___416_11425.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___416_11425.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___416_11425.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___416_11425.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___416_11425.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___416_11425.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___416_11425.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___416_11425.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___416_11425.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___416_11425.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___416_11425.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___416_11425.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___416_11425.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___416_11425.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___416_11425.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___416_11425.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___416_11425.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___416_11425.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___416_11425.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___416_11425.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___416_11425.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___416_11425.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___416_11425.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___416_11425.FStar_TypeChecker_Env.nbe)
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
                 let uu____11493 =
                   let uu____11495 =
                     let uu____11504 = drop_logic val_q  in
                     let uu____11507 = drop_logic q'  in
                     (uu____11504, uu____11507)  in
                   match uu____11495 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____11493
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____11534 =
                      let uu____11540 =
                        let uu____11542 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____11544 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____11546 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____11542 uu____11544 uu____11546
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____11540)
                       in
                    FStar_Errors.raise_error uu____11534 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____11583 =
                   let uu____11584 = FStar_Syntax_Subst.compress def  in
                   uu____11584.FStar_Syntax_Syntax.n  in
                 match uu____11583 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____11596,uu____11597) -> binders
                 | uu____11622 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____11634;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____11739) -> val_bs1
                     | (uu____11770,[]) -> val_bs1
                     | ((body_bv,uu____11802)::bt,(val_bv,aqual)::vt) ->
                         let uu____11859 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____11883) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___417_11897 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___418_11900 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___418_11900.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___417_11897.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___417_11897.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____11859
                      in
                   let uu____11907 =
                     let uu____11914 =
                       let uu____11915 =
                         let uu____11930 = rename_binders1 def_bs val_bs  in
                         (uu____11930, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____11915  in
                     FStar_Syntax_Syntax.mk uu____11914  in
                   uu____11907 FStar_Pervasives_Native.None r1
               | uu____11952 -> typ1  in
             let uu___419_11953 = lb  in
             let uu____11954 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___419_11953.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___419_11953.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____11954;
               FStar_Syntax_Syntax.lbeff =
                 (uu___419_11953.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___419_11953.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___419_11953.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___419_11953.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____11957 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____12012  ->
                     fun lb  ->
                       match uu____12012 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____12058 =
                             let uu____12070 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____12070 with
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
                                   | uu____12150 ->
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
                                  (let uu____12197 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____12197, quals_opt1)))
                              in
                           (match uu____12058 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____11957 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____12301 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___376_12307  ->
                                match uu___376_12307 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____12312 -> false))
                         in
                      if uu____12301
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____12325 =
                    let uu____12332 =
                      let uu____12333 =
                        let uu____12347 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____12347)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____12333  in
                    FStar_Syntax_Syntax.mk uu____12332  in
                  uu____12325 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___420_12369 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___420_12369.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___420_12369.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___420_12369.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___420_12369.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___420_12369.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___420_12369.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___420_12369.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___420_12369.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___420_12369.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___420_12369.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___420_12369.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___420_12369.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___420_12369.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___420_12369.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___420_12369.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___420_12369.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___420_12369.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___420_12369.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___420_12369.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___420_12369.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___420_12369.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___420_12369.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___420_12369.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___420_12369.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___420_12369.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___420_12369.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___420_12369.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___420_12369.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___420_12369.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___420_12369.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___420_12369.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___420_12369.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___420_12369.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___420_12369.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___420_12369.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___420_12369.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___420_12369.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___420_12369.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___420_12369.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___420_12369.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___420_12369.FStar_TypeChecker_Env.nbe)
                  }  in
                let e1 =
                  let uu____12372 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____12372
                  then
                    let drop_lbtyp e_lax =
                      let uu____12381 =
                        let uu____12382 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____12382.FStar_Syntax_Syntax.n  in
                      match uu____12381 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____12404 =
                              let uu____12405 = FStar_Syntax_Subst.compress e
                                 in
                              uu____12405.FStar_Syntax_Syntax.n  in
                            match uu____12404 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____12409,lb1::[]),uu____12411) ->
                                let uu____12427 =
                                  let uu____12428 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____12428.FStar_Syntax_Syntax.n  in
                                (match uu____12427 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____12433 -> false)
                            | uu____12435 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___421_12439 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___422_12454 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___422_12454.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___422_12454.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___422_12454.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___422_12454.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___422_12454.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___422_12454.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___421_12439.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___421_12439.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____12457 -> e_lax  in
                    let e1 =
                      let uu____12459 =
                        let uu____12460 =
                          let uu____12461 =
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              (let uu___423_12470 = env'  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___423_12470.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___423_12470.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___423_12470.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___423_12470.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___423_12470.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___423_12470.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___423_12470.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___423_12470.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___423_12470.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___423_12470.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___423_12470.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___423_12470.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___423_12470.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___423_12470.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___423_12470.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___423_12470.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___423_12470.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___423_12470.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___423_12470.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___423_12470.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___423_12470.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 = true;
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___423_12470.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___423_12470.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___423_12470.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___423_12470.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___423_12470.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___423_12470.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___423_12470.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___423_12470.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___423_12470.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___423_12470.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___423_12470.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___423_12470.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___423_12470.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___423_12470.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___423_12470.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___423_12470.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___423_12470.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___423_12470.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___423_12470.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___423_12470.FStar_TypeChecker_Env.nbe)
                               }) e
                             in
                          FStar_All.pipe_right uu____12461
                            (fun uu____12483  ->
                               match uu____12483 with
                               | (e1,uu____12491,uu____12492) -> e1)
                           in
                        FStar_All.pipe_right uu____12460
                          (FStar_TypeChecker_Normalize.remove_uvar_solutions
                             env')
                         in
                      FStar_All.pipe_right uu____12459 drop_lbtyp  in
                    ((let uu____12494 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "TwoPhases")
                         in
                      if uu____12494
                      then
                        let uu____12499 =
                          FStar_Syntax_Print.term_to_string e1  in
                        FStar_Util.print1 "Let binding after phase 1: %s\n"
                          uu____12499
                      else ());
                     e1)
                  else e  in
                let uu____12506 =
                  let uu____12515 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____12515 with
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
                (match uu____12506 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___424_12620 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___424_12620.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___424_12620.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___424_12620.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___424_12620.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___425_12633 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___425_12633.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___425_12633.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___425_12633.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___425_12633.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___425_12633.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___425_12633.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____12634 =
                       let uu____12646 =
                         FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env'
                           e1
                          in
                       match uu____12646 with
                       | ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                            FStar_Syntax_Syntax.pos = uu____12666;
                            FStar_Syntax_Syntax.vars = uu____12667;_},uu____12668,g)
                           when FStar_TypeChecker_Env.is_trivial g ->
                           let lbs2 =
                             let uu____12698 =
                               FStar_All.pipe_right
                                 (FStar_Pervasives_Native.snd lbs1)
                                 (FStar_List.map rename_parameters)
                                in
                             ((FStar_Pervasives_Native.fst lbs1),
                               uu____12698)
                              in
                           let lbs3 =
                             let uu____12722 =
                               match post_tau with
                               | FStar_Pervasives_Native.Some tau ->
                                   FStar_List.map (postprocess_lb tau)
                                     (FStar_Pervasives_Native.snd lbs2)
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.snd lbs2
                                in
                             ((FStar_Pervasives_Native.fst lbs2),
                               uu____12722)
                              in
                           let quals1 =
                             match e2.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_meta
                                 (uu____12745,FStar_Syntax_Syntax.Meta_desugared
                                  (FStar_Syntax_Syntax.Masked_effect ))
                                 -> FStar_Syntax_Syntax.HasMaskedEffect ::
                                 quals
                             | uu____12750 -> quals  in
                           ((let uu___426_12759 = se1  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_let (lbs3, lids));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___426_12759.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals = quals1;
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___426_12759.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___426_12759.FStar_Syntax_Syntax.sigattrs)
                             }), lbs3)
                       | uu____12762 ->
                           failwith
                             "impossible (typechecking should preserve Tm_let)"
                        in
                     (match uu____12634 with
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
                           (let uu____12818 = log env1  in
                            if uu____12818
                            then
                              let uu____12821 =
                                let uu____12823 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs1)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let should_log =
                                            let uu____12843 =
                                              let uu____12852 =
                                                let uu____12853 =
                                                  let uu____12856 =
                                                    FStar_Util.right
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  uu____12856.FStar_Syntax_Syntax.fv_name
                                                   in
                                                uu____12853.FStar_Syntax_Syntax.v
                                                 in
                                              FStar_TypeChecker_Env.try_lookup_val_decl
                                                env1 uu____12852
                                               in
                                            match uu____12843 with
                                            | FStar_Pervasives_Native.None 
                                                -> true
                                            | uu____12865 -> false  in
                                          if should_log
                                          then
                                            let uu____12877 =
                                              FStar_Syntax_Print.lbname_to_string
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            let uu____12879 =
                                              FStar_Syntax_Print.term_to_string
                                                lb.FStar_Syntax_Syntax.lbtyp
                                               in
                                            FStar_Util.format2 "let %s : %s"
                                              uu____12877 uu____12879
                                          else ""))
                                   in
                                FStar_All.pipe_right uu____12823
                                  (FStar_String.concat "\n")
                                 in
                              FStar_Util.print1 "%s\n" uu____12821
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
      (let uu____12931 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____12931
       then
         let uu____12934 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____12934
       else ());
      (let uu____12939 = get_fail_se se  in
       match uu____12939 with
       | FStar_Pervasives_Native.Some (uu____12960,false ) when
           let uu____12977 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____12977 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___427_13003 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___427_13003.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___427_13003.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___427_13003.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___427_13003.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___427_13003.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___427_13003.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___427_13003.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___427_13003.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___427_13003.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___427_13003.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___427_13003.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___427_13003.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___427_13003.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___427_13003.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___427_13003.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___427_13003.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___427_13003.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___427_13003.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___427_13003.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___427_13003.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___427_13003.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___427_13003.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___427_13003.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___427_13003.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___427_13003.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___427_13003.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___427_13003.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___427_13003.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___427_13003.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___427_13003.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___427_13003.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___427_13003.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___427_13003.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___427_13003.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___427_13003.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___427_13003.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___427_13003.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___427_13003.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___427_13003.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___427_13003.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___427_13003.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___427_13003.FStar_TypeChecker_Env.nbe)
               }
             else env1  in
           ((let uu____13008 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____13008
             then
               let uu____13011 =
                 let uu____13013 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____13013
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____13011
             else ());
            (let uu____13027 =
               FStar_Errors.catch_errors
                 (fun uu____13057  ->
                    FStar_Options.with_saved_options
                      (fun uu____13069  -> tc_decl' env' se))
                in
             match uu____13027 with
             | (errs,uu____13081) ->
                 ((let uu____13111 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____13111
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____13146 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____13146  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____13158 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____13169 =
                            let uu____13179 =
                              check_multi_contained errnos1 actual  in
                            match uu____13179 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")))
                             in
                          (match uu____13169 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____13244 =
                                   let uu____13250 =
                                     let uu____13252 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____13255 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____13258 =
                                       FStar_Util.string_of_int e  in
                                     let uu____13260 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____13262 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____13252 uu____13255 uu____13258
                                       uu____13260 uu____13262
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____13250)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____13244)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____13289 .
    'Auu____13289 ->
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
               (fun uu___377_13332  ->
                  match uu___377_13332 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____13335 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____13346) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____13354 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____13364 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____13369 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____13385 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____13411 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13437) ->
            let uu____13446 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13446
            then
              let for_export_bundle se1 uu____13483 =
                match uu____13483 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____13522,uu____13523) ->
                         let dec =
                           let uu___428_13533 = se1  in
                           let uu____13534 =
                             let uu____13535 =
                               let uu____13542 =
                                 let uu____13543 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____13543  in
                               (l, us, uu____13542)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____13535
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____13534;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___428_13533.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___428_13533.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___428_13533.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____13553,uu____13554,uu____13555) ->
                         let dec =
                           let uu___429_13563 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___429_13563.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___429_13563.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___429_13563.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____13568 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____13591,uu____13592,uu____13593) ->
            let uu____13594 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13594 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____13618 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____13618
            then
              ([(let uu___430_13637 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___430_13637.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___430_13637.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___430_13637.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____13640 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___378_13646  ->
                         match uu___378_13646 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____13649 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____13655 ->
                             true
                         | uu____13657 -> false))
                  in
               if uu____13640 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____13678 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____13683 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____13688 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13693 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13711) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____13725 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____13725
            then ([], hidden)
            else
              (let dec =
                 let uu____13746 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____13746;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____13757 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13757
            then
              let uu____13768 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___431_13782 = se  in
                        let uu____13783 =
                          let uu____13784 =
                            let uu____13791 =
                              let uu____13792 =
                                let uu____13795 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____13795.FStar_Syntax_Syntax.fv_name  in
                              uu____13792.FStar_Syntax_Syntax.v  in
                            (uu____13791, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____13784  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____13783;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___431_13782.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___431_13782.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___431_13782.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____13768, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____13818 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____13818
       then
         let uu____13821 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____13821
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____13826 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____13844 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____13861) -> z3_reset_options env
       | FStar_Syntax_Syntax.Sig_pragma uu____13865 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____13875 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____13875) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____13876,uu____13877,uu____13878) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_13883  ->
                   match uu___379_13883 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13886 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____13888,uu____13889) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_13898  ->
                   match uu___379_13898 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13901 -> false))
           -> env
       | uu____13903 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____13972 se =
        match uu____13972 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____14025 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____14025
              then
                let uu____14028 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____14028
              else ());
             (let uu____14033 = tc_decl env1 se  in
              match uu____14033 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14086 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14086
                             then
                               let uu____14090 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____14090
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14106 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14106
                             then
                               let uu____14110 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____14110
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
                    (let uu____14127 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____14127
                     then
                       let uu____14132 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____14141 =
                                  let uu____14143 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____14143 "\n"  in
                                Prims.strcat s uu____14141) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____14132
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____14153 =
                       let uu____14162 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____14162
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____14204 se1 =
                            match uu____14204 with
                            | (exports1,hidden1) ->
                                let uu____14232 = for_export env3 hidden1 se1
                                   in
                                (match uu____14232 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____14153 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____14386 = acc  in
        match uu____14386 with
        | (uu____14421,uu____14422,env1,uu____14424) ->
            let uu____14437 =
              FStar_Util.record_time
                (fun uu____14484  -> process_one_decl acc se)
               in
            (match uu____14437 with
             | (r,ms_elapsed) ->
                 ((let uu____14550 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____14550
                   then
                     let uu____14554 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____14556 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____14554 uu____14556
                   else ());
                  r))
         in
      let uu____14561 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____14561 with
      | (ses1,exports,env1,uu____14609) ->
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
          let uu___432_14647 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___432_14647.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___432_14647.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___432_14647.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___432_14647.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___432_14647.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___432_14647.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___432_14647.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___432_14647.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___432_14647.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___432_14647.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___432_14647.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___432_14647.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___432_14647.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___432_14647.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___432_14647.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___432_14647.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___432_14647.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___432_14647.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___432_14647.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___432_14647.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___432_14647.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___432_14647.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___432_14647.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___432_14647.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___432_14647.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___432_14647.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___432_14647.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___432_14647.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___432_14647.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___432_14647.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___432_14647.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___432_14647.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___432_14647.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___432_14647.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___432_14647.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___432_14647.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___432_14647.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___432_14647.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___432_14647.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___432_14647.FStar_TypeChecker_Env.nbe)
          }  in
        let check_term lid univs1 t =
          let uu____14667 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____14667 with
          | (univs2,t1) ->
              ((let uu____14675 =
                  let uu____14677 =
                    let uu____14683 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____14683  in
                  FStar_All.pipe_left uu____14677
                    (FStar_Options.Other "Exports")
                   in
                if uu____14675
                then
                  let uu____14687 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____14689 =
                    let uu____14691 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____14691
                      (FStar_String.concat ", ")
                     in
                  let uu____14708 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____14687 uu____14689 uu____14708
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____14714 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____14714 (fun a2  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____14740 =
             let uu____14742 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____14744 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____14742 uu____14744
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____14740);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14755) ->
              let uu____14764 =
                let uu____14766 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14766  in
              if uu____14764
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____14780,uu____14781) ->
              let t =
                let uu____14793 =
                  let uu____14800 =
                    let uu____14801 =
                      let uu____14816 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____14816)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____14801  in
                  FStar_Syntax_Syntax.mk uu____14800  in
                uu____14793 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____14835,uu____14836,uu____14837) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____14847 =
                let uu____14849 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14849  in
              if uu____14847 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____14857,lbs),uu____14859) ->
              let uu____14870 =
                let uu____14872 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14872  in
              if uu____14870
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
              let uu____14895 =
                let uu____14897 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14897  in
              if uu____14895
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____14918 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____14919 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14926 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____14927 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____14928 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____14935 -> ()  in
        let uu____14936 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____14936 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____15042) -> true
             | uu____15044 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____15074 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____15113 ->
                   let uu____15114 =
                     let uu____15121 =
                       let uu____15122 =
                         let uu____15137 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____15137)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____15122  in
                     FStar_Syntax_Syntax.mk uu____15121  in
                   uu____15114 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____15157,uu____15158) ->
            let s1 =
              let uu___433_15168 = s  in
              let uu____15169 =
                let uu____15170 =
                  let uu____15177 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____15177)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____15170  in
              let uu____15178 =
                let uu____15181 =
                  let uu____15184 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____15184  in
                FStar_Syntax_Syntax.Assumption :: uu____15181  in
              {
                FStar_Syntax_Syntax.sigel = uu____15169;
                FStar_Syntax_Syntax.sigrng =
                  (uu___433_15168.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____15178;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___433_15168.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___433_15168.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____15187 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____15212 lbdef =
        match uu____15212 with
        | (uvs,t) ->
            let attrs =
              let uu____15223 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____15223
              then
                let uu____15228 =
                  let uu____15229 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____15229
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____15228 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___434_15232 = s  in
            let uu____15233 =
              let uu____15236 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____15236  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___434_15232.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____15233;
              FStar_Syntax_Syntax.sigmeta =
                (uu___434_15232.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____15254 -> failwith "Impossible!"  in
        let c_opt =
          let uu____15261 = FStar_Syntax_Util.is_unit t  in
          if uu____15261
          then
            let uu____15268 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____15268
          else
            (let uu____15275 =
               let uu____15276 = FStar_Syntax_Subst.compress t  in
               uu____15276.FStar_Syntax_Syntax.n  in
             match uu____15275 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____15283,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____15307 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____15319 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____15319
            then false
            else
              (let uu____15326 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____15326
               then true
               else
                 (let uu____15333 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____15333))
         in
      let extract_sigelt s =
        (let uu____15345 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____15345
         then
           let uu____15348 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____15348
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____15355 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____15375 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____15394 ->
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
                             (lid,uu____15440,uu____15441,uu____15442,uu____15443,uu____15444)
                             ->
                             ((let uu____15454 =
                                 let uu____15457 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____15457  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____15454);
                              (let uu____15550 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____15550 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____15554,uu____15555,uu____15556,uu____15557,uu____15558)
                             ->
                             ((let uu____15566 =
                                 let uu____15569 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____15569  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____15566);
                              sigelts1)
                         | uu____15662 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____15671 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15671
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____15681 =
                    let uu___435_15682 = s  in
                    let uu____15683 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___435_15682.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___435_15682.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15683;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___435_15682.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___435_15682.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15681])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____15694 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15694
             then []
             else
               (let uu____15701 = lbs  in
                match uu____15701 with
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
                        (fun uu____15763  ->
                           match uu____15763 with
                           | (uu____15771,t,uu____15773) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____15790  ->
                             match uu____15790 with
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
                           (fun uu____15817  ->
                              match uu____15817 with
                              | (uu____15825,t,uu____15827) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____15839,uu____15840) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____15848 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____15899 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____15899) uu____15848
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____15903 =
                    let uu___436_15904 = s  in
                    let uu____15905 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___436_15904.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___436_15904.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15905;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___436_15904.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___436_15904.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15903]
                else [])
             else
               (let uu____15912 =
                  let uu___437_15913 = s  in
                  let uu____15914 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___437_15913.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___437_15913.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____15914;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___437_15913.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___437_15913.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____15912])
         | FStar_Syntax_Syntax.Sig_new_effect uu____15917 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____15918 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15919 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____15932 -> [s])
         in
      let uu___438_15933 = m  in
      let uu____15934 =
        let uu____15935 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____15935 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___438_15933.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____15934;
        FStar_Syntax_Syntax.exports =
          (uu___438_15933.FStar_Syntax_Syntax.exports);
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
        (fun uu____15986  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____16034  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             solver.FStar_TypeChecker_Env.refresh (); env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____16050 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____16050
  
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
      (let uu____16139 = FStar_Options.debug_any ()  in
       if uu____16139
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
         let uu___439_16155 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___439_16155.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___439_16155.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___439_16155.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___439_16155.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___439_16155.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___439_16155.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___439_16155.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___439_16155.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___439_16155.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___439_16155.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___439_16155.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___439_16155.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___439_16155.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___439_16155.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___439_16155.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___439_16155.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___439_16155.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___439_16155.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___439_16155.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___439_16155.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___439_16155.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___439_16155.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___439_16155.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___439_16155.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___439_16155.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___439_16155.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___439_16155.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___439_16155.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___439_16155.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___439_16155.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___439_16155.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___439_16155.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___439_16155.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___439_16155.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___439_16155.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___439_16155.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___439_16155.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___439_16155.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___439_16155.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___439_16155.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___439_16155.FStar_TypeChecker_Env.nbe)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____16157 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____16157 with
       | (ses,exports,env3) ->
           ((let uu___440_16190 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___440_16190.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___440_16190.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___440_16190.FStar_Syntax_Syntax.is_interface)
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
        let uu____16219 = tc_decls env decls  in
        match uu____16219 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___441_16250 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___441_16250.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___441_16250.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___441_16250.FStar_Syntax_Syntax.is_interface)
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
        let uu____16311 = tc_partial_modul env01 m  in
        match uu____16311 with
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
                (let uu____16348 = FStar_Errors.get_err_count ()  in
                 uu____16348 = (Prims.parse_int "0"))
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____16359 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____16359
                then
                  let uu____16363 =
                    let uu____16365 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16365 then "" else " (in lax mode) "  in
                  let uu____16373 =
                    let uu____16375 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16375
                    then
                      let uu____16379 =
                        let uu____16381 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.strcat uu____16381 "\n"  in
                      Prims.strcat "\nfrom: " uu____16379
                    else ""  in
                  let uu____16388 =
                    let uu____16390 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16390
                    then
                      let uu____16394 =
                        let uu____16396 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.strcat uu____16396 "\n"  in
                      Prims.strcat "\nto: " uu____16394
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____16363
                    uu____16373 uu____16388
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.strcat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___442_16410 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___442_16410.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___442_16410.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___442_16410.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___442_16410.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___442_16410.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___442_16410.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___442_16410.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___442_16410.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___442_16410.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___442_16410.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___442_16410.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___442_16410.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___442_16410.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___442_16410.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___442_16410.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___442_16410.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___442_16410.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___442_16410.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___442_16410.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___442_16410.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___442_16410.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___442_16410.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___442_16410.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___442_16410.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___442_16410.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___442_16410.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___442_16410.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___442_16410.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___442_16410.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___442_16410.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___442_16410.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___442_16410.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___442_16410.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___442_16410.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___442_16410.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___442_16410.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___442_16410.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___442_16410.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___442_16410.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___442_16410.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___442_16410.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___442_16410.FStar_TypeChecker_Env.nbe)
                    }  in
                  let en02 =
                    let uu___443_16412 = en01  in
                    let uu____16413 =
                      let uu____16428 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____16428, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___443_16412.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___443_16412.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___443_16412.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___443_16412.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___443_16412.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___443_16412.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___443_16412.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___443_16412.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___443_16412.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___443_16412.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___443_16412.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___443_16412.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___443_16412.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___443_16412.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___443_16412.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___443_16412.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___443_16412.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___443_16412.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___443_16412.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___443_16412.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___443_16412.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___443_16412.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___443_16412.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___443_16412.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___443_16412.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___443_16412.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___443_16412.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___443_16412.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___443_16412.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___443_16412.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___443_16412.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____16413;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___443_16412.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___443_16412.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___443_16412.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___443_16412.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___443_16412.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___443_16412.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___443_16412.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___443_16412.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___443_16412.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___443_16412.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___443_16412.FStar_TypeChecker_Env.nbe)
                    }  in
                  let uu____16474 =
                    let uu____16476 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____16476  in
                  if uu____16474
                  then
                    ((let uu____16480 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____16480 (fun a3  -> ()));
                     z3_reset_options en02)
                  else en02  in
                let uu____16484 = tc_modul en0 modul_iface true  in
                match uu____16484 with
                | (modul_iface1,env) ->
                    ((let uu___444_16497 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___444_16497.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___444_16497.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___444_16497.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___445_16501 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___445_16501.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___445_16501.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___445_16501.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____16504 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____16504 FStar_Util.smap_clear);
               (let uu____16540 =
                  ((let uu____16544 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____16544) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____16547 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____16547)
                   in
                if uu____16540 then check_exports env modul exports else ());
               (let uu____16553 =
                  pop_context env
                    (Prims.strcat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____16553 (fun a4  -> ()));
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
                 env modul;
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ();
               (let uu____16558 =
                  let uu____16560 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____16560  in
                if uu____16558
                then
                  let uu____16563 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____16563 (fun a5  -> ())
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
        let uu____16580 =
          let uu____16582 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____16582  in
        push_context env uu____16580  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____16603 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____16614 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____16614 with | (uu____16621,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____16646 = FStar_Options.debug_any ()  in
         if uu____16646
         then
           let uu____16649 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____16649
         else ());
        (let uu____16661 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____16661
         then
           let uu____16664 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____16664
         else ());
        (let env1 =
           let uu___446_16670 = env  in
           let uu____16671 =
             let uu____16673 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____16673  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___446_16670.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___446_16670.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___446_16670.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___446_16670.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___446_16670.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___446_16670.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___446_16670.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___446_16670.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___446_16670.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___446_16670.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___446_16670.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___446_16670.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___446_16670.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___446_16670.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___446_16670.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___446_16670.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___446_16670.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___446_16670.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___446_16670.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___446_16670.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____16671;
             FStar_TypeChecker_Env.lax_universes =
               (uu___446_16670.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___446_16670.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___446_16670.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___446_16670.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___446_16670.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___446_16670.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___446_16670.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___446_16670.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___446_16670.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___446_16670.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___446_16670.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___446_16670.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___446_16670.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___446_16670.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___446_16670.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___446_16670.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___446_16670.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___446_16670.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___446_16670.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___446_16670.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___446_16670.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___446_16670.FStar_TypeChecker_Env.nbe)
           }  in
         let uu____16675 = tc_modul env1 m b  in
         match uu____16675 with
         | (m1,env2) ->
             ((let uu____16687 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____16687
               then
                 let uu____16690 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____16690
               else ());
              (let uu____16696 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____16696
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
                         let uu____16734 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____16734 with
                         | (univnames1,e) ->
                             let uu___447_16741 = lb  in
                             let uu____16742 =
                               let uu____16745 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____16745 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___447_16741.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___447_16741.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___447_16741.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___447_16741.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16742;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___447_16741.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___447_16741.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___448_16746 = se  in
                       let uu____16747 =
                         let uu____16748 =
                           let uu____16755 =
                             let uu____16756 = FStar_List.map update lbs  in
                             (b1, uu____16756)  in
                           (uu____16755, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____16748  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____16747;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___448_16746.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___448_16746.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___448_16746.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___448_16746.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____16764 -> se  in
                 let normalized_module =
                   let uu___449_16766 = m1  in
                   let uu____16767 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___449_16766.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____16767;
                     FStar_Syntax_Syntax.exports =
                       (uu___449_16766.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___449_16766.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____16768 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____16768
               else ());
              (m1, env2)))
  
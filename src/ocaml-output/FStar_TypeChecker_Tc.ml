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
                                  let is_unk t =
                                    let uu____1103 =
                                      let uu____1104 =
                                        FStar_Syntax_Subst.compress t  in
                                      uu____1104.FStar_Syntax_Syntax.n  in
                                    match uu____1103 with
                                    | FStar_Syntax_Syntax.Tm_unknown  -> true
                                    | uu____1109 -> false  in
                                  FStar_Util.print_string "GG2\n";
                                  (let uu____1113 =
                                     elaborate_and_star dmff_env
                                       effect_binders1 []
                                       (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                      in
                                   match uu____1113 with
                                   | (dmff_env1,uu____1139,bind_wp,bind_elab)
                                       ->
                                       let bind_wp1 =
                                         let uu____1145 =
                                           is_unk
                                             (FStar_Pervasives_Native.snd
                                                (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind)
                                            in
                                         if uu____1145
                                         then
                                           let uu____1154 =
                                             let uu____1155 =
                                               let uu____1162 =
                                                 FStar_Syntax_Syntax.tabbrev
                                                   FStar_Parser_Const.range_lid
                                                  in
                                               FStar_Syntax_Syntax.null_binder
                                                 uu____1162
                                                in
                                             [uu____1155]  in
                                           FStar_Syntax_Util.abs uu____1154
                                             bind_wp
                                             FStar_Pervasives_Native.None
                                         else
                                           FStar_Pervasives_Native.snd
                                             (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                          in
                                       (FStar_Util.print_string "GG3\n";
                                        (let uu____1183 =
                                           elaborate_and_star dmff_env1
                                             effect_binders1 []
                                             (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                            in
                                         match uu____1183 with
                                         | (dmff_env2,uu____1209,return_wp,return_elab)
                                             ->
                                             let return_wp1 =
                                               let uu____1215 =
                                                 is_unk
                                                   (FStar_Pervasives_Native.snd
                                                      (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret)
                                                  in
                                               if uu____1215
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
                                                   =
                                                   FStar_Pervasives_Native.None;
                                                 FStar_Syntax_Syntax.residual_flags
                                                   = []
                                               }  in
                                             let lift_from_pure_wp =
                                               let uu____1236 =
                                                 let uu____1237 =
                                                   FStar_Syntax_Subst.compress
                                                     return_wp1
                                                    in
                                                 uu____1237.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____1236 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (b1::b2::bs,body,what) ->
                                                   let uu____1295 =
                                                     let uu____1314 =
                                                       let uu____1319 =
                                                         FStar_Syntax_Util.abs
                                                           bs body
                                                           FStar_Pervasives_Native.None
                                                          in
                                                       FStar_Syntax_Subst.open_term
                                                         [b1; b2] uu____1319
                                                        in
                                                     match uu____1314 with
                                                     | (b11::b21::[],body1)
                                                         -> (b11, b21, body1)
                                                     | uu____1401 ->
                                                         failwith
                                                           "Impossible : open_term not preserving binders arity"
                                                      in
                                                   (match uu____1295 with
                                                    | (b11,b21,body1) ->
                                                        let env0 =
                                                          let uu____1455 =
                                                            FStar_TypeChecker_DMFF.get_env
                                                              dmff_env2
                                                             in
                                                          FStar_TypeChecker_Env.push_binders
                                                            uu____1455
                                                            [b11; b21]
                                                           in
                                                        let wp_b1 =
                                                          let raw_wp_b1 =
                                                            let uu____1478 =
                                                              let uu____1479
                                                                =
                                                                let uu____1496
                                                                  =
                                                                  let uu____1507
                                                                    =
                                                                    let uu____1516
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    (FStar_Pervasives_Native.fst
                                                                    b11)  in
                                                                    let uu____1521
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____1516,
                                                                    uu____1521)
                                                                     in
                                                                  [uu____1507]
                                                                   in
                                                                (wp_type,
                                                                  uu____1496)
                                                                 in
                                                              FStar_Syntax_Syntax.Tm_app
                                                                uu____1479
                                                               in
                                                            mk1 uu____1478
                                                             in
                                                          FStar_TypeChecker_Normalize.normalize
                                                            [FStar_TypeChecker_Env.Beta]
                                                            env0 raw_wp_b1
                                                           in
                                                        let uu____1557 =
                                                          let uu____1566 =
                                                            let uu____1567 =
                                                              FStar_Syntax_Util.unascribe
                                                                wp_b1
                                                               in
                                                            FStar_TypeChecker_Normalize.eta_expand_with_type
                                                              env0 body1
                                                              uu____1567
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Util.abs_formals
                                                            uu____1566
                                                           in
                                                        (match uu____1557
                                                         with
                                                         | (bs1,body2,what')
                                                             ->
                                                             let fail1
                                                               uu____1590 =
                                                               let error_msg
                                                                 =
                                                                 let uu____1593
                                                                   =
                                                                   FStar_Syntax_Print.term_to_string
                                                                    body2
                                                                    in
                                                                 let uu____1595
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
                                                                   uu____1593
                                                                   uu____1595
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
                                                                    let uu____1605
                                                                    =
                                                                    let uu____1607
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____1607
                                                                     in
                                                                    if
                                                                    uu____1605
                                                                    then
                                                                    fail1 ()
                                                                    else ());
                                                                    (
                                                                    let uu____1612
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
                                                                    uu____1612
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
                                                                 let uu____1641
                                                                   =
                                                                   let uu____1646
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp  in
                                                                   let uu____1647
                                                                    =
                                                                    let uu____1648
                                                                    =
                                                                    let uu____1657
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                    (uu____1657,
                                                                    FStar_Pervasives_Native.None)
                                                                     in
                                                                    [uu____1648]
                                                                     in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    uu____1646
                                                                    uu____1647
                                                                    in
                                                                 uu____1641
                                                                   FStar_Pervasives_Native.None
                                                                   FStar_Range.dummyRange
                                                                  in
                                                               let uu____1694
                                                                 =
                                                                 let uu____1695
                                                                   =
                                                                   let uu____1704
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp  in
                                                                   [uu____1704]
                                                                    in
                                                                 b11 ::
                                                                   uu____1695
                                                                  in
                                                               let uu____1729
                                                                 =
                                                                 FStar_Syntax_Util.abs
                                                                   bs1 body3
                                                                   what
                                                                  in
                                                               FStar_Syntax_Util.abs
                                                                 uu____1694
                                                                 uu____1729
                                                                 (FStar_Pervasives_Native.Some
                                                                    rc_gtot)))))
                                               | uu____1732 ->
                                                   raise_error1
                                                     (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                       "unexpected shape for return")
                                                in
                                             let apply_close t =
                                               if
                                                 (FStar_List.length
                                                    effect_binders1)
                                                   = (Prims.parse_int "0")
                                               then t
                                               else
                                                 (let uu____1762 =
                                                    let uu____1763 =
                                                      let uu____1764 =
                                                        let uu____1781 =
                                                          let uu____1792 =
                                                            FStar_Syntax_Util.args_of_binders
                                                              effect_binders1
                                                             in
                                                          FStar_Pervasives_Native.snd
                                                            uu____1792
                                                           in
                                                        (t, uu____1781)  in
                                                      FStar_Syntax_Syntax.Tm_app
                                                        uu____1764
                                                       in
                                                    mk1 uu____1763  in
                                                  FStar_Syntax_Subst.close
                                                    effect_binders1
                                                    uu____1762)
                                                in
                                             let register name item =
                                               let uu____1826 =
                                                 let uu____1831 = mk_lid name
                                                    in
                                                 let uu____1832 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____1831 uu____1832
                                                  in
                                               match uu____1826 with
                                               | (sigelt,fv) ->
                                                   ((let uu____1836 =
                                                       let uu____1839 =
                                                         FStar_ST.op_Bang
                                                           sigelts
                                                          in
                                                       sigelt :: uu____1839
                                                        in
                                                     FStar_ST.op_Colon_Equals
                                                       sigelts uu____1836);
                                                    fv)
                                                in
                                             let lift_from_pure_wp1 =
                                               register "lift_from_pure"
                                                 lift_from_pure_wp
                                                in
                                             let return_wp2 =
                                               register "return_wp"
                                                 return_wp1
                                                in
                                             ((let uu____1937 =
                                                 let uu____1940 =
                                                   FStar_Syntax_Syntax.mk_sigelt
                                                     (FStar_Syntax_Syntax.Sig_pragma
                                                        (FStar_Syntax_Syntax.PushOptions
                                                           (FStar_Pervasives_Native.Some
                                                              "--admit_smt_queries true")))
                                                    in
                                                 let uu____1943 =
                                                   FStar_ST.op_Bang sigelts
                                                    in
                                                 uu____1940 :: uu____1943  in
                                               FStar_ST.op_Colon_Equals
                                                 sigelts uu____1937);
                                              (let return_elab1 =
                                                 register "return_elab"
                                                   return_elab
                                                  in
                                               (let uu____2039 =
                                                  let uu____2042 =
                                                    FStar_Syntax_Syntax.mk_sigelt
                                                      (FStar_Syntax_Syntax.Sig_pragma
                                                         FStar_Syntax_Syntax.PopOptions)
                                                     in
                                                  let uu____2043 =
                                                    FStar_ST.op_Bang sigelts
                                                     in
                                                  uu____2042 :: uu____2043
                                                   in
                                                FStar_ST.op_Colon_Equals
                                                  sigelts uu____2039);
                                               (let bind_wp2 =
                                                  register "bind_wp" bind_wp1
                                                   in
                                                (let uu____2139 =
                                                   let uu____2142 =
                                                     FStar_Syntax_Syntax.mk_sigelt
                                                       (FStar_Syntax_Syntax.Sig_pragma
                                                          (FStar_Syntax_Syntax.PushOptions
                                                             (FStar_Pervasives_Native.Some
                                                                "--admit_smt_queries true")))
                                                      in
                                                   let uu____2145 =
                                                     FStar_ST.op_Bang sigelts
                                                      in
                                                   uu____2142 :: uu____2145
                                                    in
                                                 FStar_ST.op_Colon_Equals
                                                   sigelts uu____2139);
                                                (let bind_elab1 =
                                                   register "bind_elab"
                                                     bind_elab
                                                    in
                                                 (let uu____2241 =
                                                    let uu____2244 =
                                                      FStar_Syntax_Syntax.mk_sigelt
                                                        (FStar_Syntax_Syntax.Sig_pragma
                                                           FStar_Syntax_Syntax.PopOptions)
                                                       in
                                                    let uu____2245 =
                                                      FStar_ST.op_Bang
                                                        sigelts
                                                       in
                                                    uu____2244 :: uu____2245
                                                     in
                                                  FStar_ST.op_Colon_Equals
                                                    sigelts uu____2241);
                                                 (let uu____2338 =
                                                    FStar_List.fold_left
                                                      (fun uu____2380  ->
                                                         fun action  ->
                                                           match uu____2380
                                                           with
                                                           | (dmff_env3,actions)
                                                               ->
                                                               ((let uu____2401
                                                                   =
                                                                   FStar_Ident.string_of_lid
                                                                    action.FStar_Syntax_Syntax.action_name
                                                                    in
                                                                 FStar_Util.print1
                                                                   "GG proc action %s\n"
                                                                   uu____2401);
                                                                (let params_un
                                                                   =
                                                                   FStar_Syntax_Subst.open_binders
                                                                    action.FStar_Syntax_Syntax.action_params
                                                                    in
                                                                 let uu____2405
                                                                   =
                                                                   let uu____2412
                                                                    =
                                                                    FStar_TypeChecker_DMFF.get_env
                                                                    dmff_env3
                                                                     in
                                                                   FStar_TypeChecker_TcTerm.tc_tparams
                                                                    uu____2412
                                                                    params_un
                                                                    in
                                                                 match uu____2405
                                                                 with
                                                                 | (action_params,env',uu____2421)
                                                                    ->
                                                                    let action_params1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____2447
                                                                     ->
                                                                    match uu____2447
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2466
                                                                    =
                                                                    let uu___383_2467
                                                                    = bv  in
                                                                    let uu____2468
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___383_2467.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___383_2467.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2468
                                                                    }  in
                                                                    (uu____2466,
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
                                                                    (let uu____2476
                                                                    =
                                                                    elaborate_and_star
                                                                    dmff_env'
                                                                    effect_binders1
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                     in
                                                                    match uu____2476
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
                                                                    uu____2519
                                                                    ->
                                                                    let uu____2520
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2520
                                                                     in
                                                                    ((
                                                                    let uu____2524
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____2527
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____2530
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____2532
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2524
                                                                    uu____2527
                                                                    uu____2530
                                                                    uu____2532);
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
                                                                    let uu____2539
                                                                    =
                                                                    let uu____2542
                                                                    =
                                                                    let uu___384_2543
                                                                    = action
                                                                     in
                                                                    let uu____2544
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____2545
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___384_2543.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___384_2543.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___384_2543.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2544;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2545
                                                                    }  in
                                                                    uu____2542
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____2539))))))))
                                                      (dmff_env2, [])
                                                      ed.FStar_Syntax_Syntax.actions
                                                     in
                                                  match uu____2338 with
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
                                                          let uu____2589 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a1
                                                             in
                                                          let uu____2596 =
                                                            let uu____2605 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp
                                                               in
                                                            [uu____2605]  in
                                                          uu____2589 ::
                                                            uu____2596
                                                           in
                                                        let uu____2630 =
                                                          let uu____2633 =
                                                            let uu____2634 =
                                                              let uu____2635
                                                                =
                                                                let uu____2652
                                                                  =
                                                                  let uu____2663
                                                                    =
                                                                    let uu____2672
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    a1  in
                                                                    let uu____2675
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____2672,
                                                                    uu____2675)
                                                                     in
                                                                  [uu____2663]
                                                                   in
                                                                (repr,
                                                                  uu____2652)
                                                                 in
                                                              FStar_Syntax_Syntax.Tm_app
                                                                uu____2635
                                                               in
                                                            mk1 uu____2634
                                                             in
                                                          let uu____2711 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              wp
                                                             in
                                                          FStar_TypeChecker_DMFF.trans_F
                                                            dmff_env3
                                                            uu____2633
                                                            uu____2711
                                                           in
                                                        FStar_Syntax_Util.abs
                                                          binders uu____2630
                                                          FStar_Pervasives_Native.None
                                                         in
                                                      let uu____2712 =
                                                        recheck_debug "FC"
                                                          env1 repr1
                                                         in
                                                      let repr2 =
                                                        register "repr" repr1
                                                         in
                                                      let uu____2716 =
                                                        let uu____2725 =
                                                          let uu____2726 =
                                                            let uu____2729 =
                                                              FStar_Syntax_Subst.compress
                                                                wp_type
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Util.unascribe
                                                              uu____2729
                                                             in
                                                          uu____2726.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____2725 with
                                                        | FStar_Syntax_Syntax.Tm_abs
                                                            (type_param::effect_param,arrow1,uu____2743)
                                                            ->
                                                            let uu____2780 =
                                                              let uu____2801
                                                                =
                                                                FStar_Syntax_Subst.open_term
                                                                  (type_param
                                                                  ::
                                                                  effect_param)
                                                                  arrow1
                                                                 in
                                                              match uu____2801
                                                              with
                                                              | (b::bs,body)
                                                                  ->
                                                                  (b, bs,
                                                                    body)
                                                              | uu____2869 ->
                                                                  failwith
                                                                    "Impossible : open_term nt preserving binders arity"
                                                               in
                                                            (match uu____2780
                                                             with
                                                             | (type_param1,effect_param1,arrow2)
                                                                 ->
                                                                 let uu____2934
                                                                   =
                                                                   let uu____2935
                                                                    =
                                                                    let uu____2938
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____2938
                                                                     in
                                                                   uu____2935.FStar_Syntax_Syntax.n
                                                                    in
                                                                 (match uu____2934
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    let uu____2971
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                    (match uu____2971
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2986
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____3017
                                                                     ->
                                                                    match uu____3017
                                                                    with
                                                                    | 
                                                                    (bv,uu____3026)
                                                                    ->
                                                                    let uu____3031
                                                                    =
                                                                    let uu____3033
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3033
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____3031
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____2986
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
                                                                    let uu____3125
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____3125
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____3135
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____3146
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____3146
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____3156
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____3159
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____3156,
                                                                    uu____3159)))
                                                                  | uu____3174
                                                                    ->
                                                                    let uu____3175
                                                                    =
                                                                    let uu____3181
                                                                    =
                                                                    let uu____3183
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____3183
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____3181)
                                                                     in
                                                                    raise_error1
                                                                    uu____3175))
                                                        | uu____3195 ->
                                                            let uu____3196 =
                                                              let uu____3202
                                                                =
                                                                let uu____3204
                                                                  =
                                                                  FStar_Syntax_Print.term_to_string
                                                                    wp_type
                                                                   in
                                                                FStar_Util.format1
                                                                  "Impossible: pre/post abs %s"
                                                                  uu____3204
                                                                 in
                                                              (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                uu____3202)
                                                               in
                                                            raise_error1
                                                              uu____3196
                                                         in
                                                      (match uu____2716 with
                                                       | (pre,post) ->
                                                           ((let uu____3237 =
                                                               register "pre"
                                                                 pre
                                                                in
                                                             ());
                                                            (let uu____3240 =
                                                               register
                                                                 "post" post
                                                                in
                                                             ());
                                                            (let uu____3243 =
                                                               register "wp"
                                                                 wp_type
                                                                in
                                                             ());
                                                            (let ed1 =
                                                               let uu___385_3246
                                                                 = ed  in
                                                               let uu____3247
                                                                 =
                                                                 FStar_Syntax_Subst.close_binders
                                                                   effect_binders1
                                                                  in
                                                               let uu____3248
                                                                 =
                                                                 let uu____3249
                                                                   =
                                                                   let uu____3250
                                                                    =
                                                                    apply_close
                                                                    return_wp2
                                                                     in
                                                                   ([],
                                                                    uu____3250)
                                                                    in
                                                                 let uu____3257
                                                                   =
                                                                   let uu____3258
                                                                    =
                                                                    apply_close
                                                                    bind_wp2
                                                                     in
                                                                   ([],
                                                                    uu____3258)
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.monad_m
                                                                    =
                                                                    FStar_Syntax_Syntax.tun;
                                                                   FStar_Syntax_Syntax.monad_ret
                                                                    =
                                                                    uu____3249;
                                                                   FStar_Syntax_Syntax.monad_bind
                                                                    =
                                                                    uu____3257
                                                                 }  in
                                                               let uu____3265
                                                                 =
                                                                 FStar_Syntax_Subst.close
                                                                   effect_binders1
                                                                   effect_signature
                                                                  in
                                                               let uu____3266
                                                                 =
                                                                 let uu____3267
                                                                   =
                                                                   apply_close
                                                                    repr2
                                                                    in
                                                                 let uu____3268
                                                                   =
                                                                   let uu____3269
                                                                    =
                                                                    apply_close
                                                                    return_elab1
                                                                     in
                                                                   ([],
                                                                    uu____3269)
                                                                    in
                                                                 let uu____3276
                                                                   =
                                                                   let uu____3277
                                                                    =
                                                                    apply_close
                                                                    bind_elab1
                                                                     in
                                                                   ([],
                                                                    uu____3277)
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.monad_m
                                                                    =
                                                                    uu____3267;
                                                                   FStar_Syntax_Syntax.monad_ret
                                                                    =
                                                                    uu____3268;
                                                                   FStar_Syntax_Syntax.monad_bind
                                                                    =
                                                                    uu____3276
                                                                 }  in
                                                               {
                                                                 FStar_Syntax_Syntax.cattributes
                                                                   =
                                                                   (uu___385_3246.FStar_Syntax_Syntax.cattributes);
                                                                 FStar_Syntax_Syntax.mname
                                                                   =
                                                                   (uu___385_3246.FStar_Syntax_Syntax.mname);
                                                                 FStar_Syntax_Syntax.univs
                                                                   =
                                                                   (uu___385_3246.FStar_Syntax_Syntax.univs);
                                                                 FStar_Syntax_Syntax.binders
                                                                   =
                                                                   uu____3247;
                                                                 FStar_Syntax_Syntax.spec
                                                                   =
                                                                   uu____3248;
                                                                 FStar_Syntax_Syntax.signature
                                                                   =
                                                                   uu____3265;
                                                                 FStar_Syntax_Syntax.if_then_else
                                                                   =
                                                                   (uu___385_3246.FStar_Syntax_Syntax.if_then_else);
                                                                 FStar_Syntax_Syntax.ite_wp
                                                                   =
                                                                   (uu___385_3246.FStar_Syntax_Syntax.ite_wp);
                                                                 FStar_Syntax_Syntax.stronger
                                                                   =
                                                                   (uu___385_3246.FStar_Syntax_Syntax.stronger);
                                                                 FStar_Syntax_Syntax.close_wp
                                                                   =
                                                                   (uu___385_3246.FStar_Syntax_Syntax.close_wp);
                                                                 FStar_Syntax_Syntax.assert_p
                                                                   =
                                                                   (uu___385_3246.FStar_Syntax_Syntax.assert_p);
                                                                 FStar_Syntax_Syntax.assume_p
                                                                   =
                                                                   (uu___385_3246.FStar_Syntax_Syntax.assume_p);
                                                                 FStar_Syntax_Syntax.null_wp
                                                                   =
                                                                   (uu___385_3246.FStar_Syntax_Syntax.null_wp);
                                                                 FStar_Syntax_Syntax.trivial
                                                                   =
                                                                   (uu___385_3246.FStar_Syntax_Syntax.trivial);
                                                                 FStar_Syntax_Syntax.repr
                                                                   =
                                                                   uu____3266;
                                                                 FStar_Syntax_Syntax.elaborated
                                                                   =
                                                                   (uu___385_3246.FStar_Syntax_Syntax.elaborated);
                                                                 FStar_Syntax_Syntax.actions
                                                                   = actions1;
                                                                 FStar_Syntax_Syntax.eff_attrs
                                                                   =
                                                                   (uu___385_3246.FStar_Syntax_Syntax.eff_attrs)
                                                               }  in
                                                             let uu____3284 =
                                                               FStar_TypeChecker_DMFF.gen_wps_for_free
                                                                 env1
                                                                 effect_binders1
                                                                 a1 wp_a ed1
                                                                in
                                                             match uu____3284
                                                             with
                                                             | (sigelts',ed2)
                                                                 ->
                                                                 ((let uu____3302
                                                                    =
                                                                    FStar_Syntax_Print.eff_decl_to_string
                                                                    ed2  in
                                                                   FStar_Util.print_string
                                                                    uu____3302);
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
                                                                    let uu____3319
                                                                    =
                                                                    let uu____3322
                                                                    =
                                                                    let uu____3323
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____3323)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3322
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
                                                                    uu____3319;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                    let uu____3330
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3330
                                                                    else
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                   let uu____3333
                                                                    =
                                                                    let uu____3336
                                                                    =
                                                                    let uu____3339
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                    FStar_List.rev
                                                                    uu____3339
                                                                     in
                                                                    FStar_List.append
                                                                    uu____3336
                                                                    sigelts'
                                                                     in
                                                                   (uu____3333,
                                                                    ed2,
                                                                    lift_from_pure_opt))))))))))))))))))))))
  
let tc_eff_decl :
  'Auu____3400 .
    FStar_TypeChecker_Env.env ->
      'Auu____3400 ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun se  ->
      fun ed  ->
        (let uu____3417 =
           FStar_TypeChecker_Env.debug env0 (FStar_Options.Other "ED")  in
         if uu____3417
         then
           let uu____3421 = FStar_Syntax_Print.eff_decl_to_string ed  in
           FStar_Util.print1 "initial eff_decl :\n\t%s\n" uu____3421
         else ());
        (let uu____3426 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____3426 with
         | (open_annotated_univs,annotated_univ_names) ->
             let open_univs n_binders t =
               let uu____3458 =
                 FStar_Syntax_Subst.shift_subst n_binders
                   open_annotated_univs
                  in
               FStar_Syntax_Subst.subst uu____3458 t  in
             let open_univs_binders n_binders bs =
               let uu____3474 =
                 FStar_Syntax_Subst.shift_subst n_binders
                   open_annotated_univs
                  in
               FStar_Syntax_Subst.subst_binders uu____3474 bs  in
             let n_effect_params =
               FStar_List.length ed.FStar_Syntax_Syntax.binders  in
             let signature = ed.FStar_Syntax_Syntax.signature  in
             let uu____3485 =
               let uu____3492 =
                 open_univs_binders (Prims.parse_int "0")
                   ed.FStar_Syntax_Syntax.binders
                  in
               let uu____3494 = open_univs n_effect_params signature  in
               FStar_Syntax_Subst.open_term' uu____3492 uu____3494  in
             (match uu____3485 with
              | (effect_params_un,signature_un,opening) ->
                  let env =
                    FStar_TypeChecker_Env.push_univ_vars env0
                      annotated_univ_names
                     in
                  let uu____3505 =
                    FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un
                     in
                  (match uu____3505 with
                   | (effect_params,env1,uu____3514) ->
                       let uu____3515 =
                         FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                           signature_un
                          in
                       (match uu____3515 with
                        | (signature1,uu____3521) ->
                            let ed1 =
                              let uu___386_3523 = ed  in
                              {
                                FStar_Syntax_Syntax.cattributes =
                                  (uu___386_3523.FStar_Syntax_Syntax.cattributes);
                                FStar_Syntax_Syntax.mname =
                                  (uu___386_3523.FStar_Syntax_Syntax.mname);
                                FStar_Syntax_Syntax.univs =
                                  (uu___386_3523.FStar_Syntax_Syntax.univs);
                                FStar_Syntax_Syntax.binders = effect_params;
                                FStar_Syntax_Syntax.spec =
                                  (uu___386_3523.FStar_Syntax_Syntax.spec);
                                FStar_Syntax_Syntax.signature = signature1;
                                FStar_Syntax_Syntax.if_then_else =
                                  (uu___386_3523.FStar_Syntax_Syntax.if_then_else);
                                FStar_Syntax_Syntax.ite_wp =
                                  (uu___386_3523.FStar_Syntax_Syntax.ite_wp);
                                FStar_Syntax_Syntax.stronger =
                                  (uu___386_3523.FStar_Syntax_Syntax.stronger);
                                FStar_Syntax_Syntax.close_wp =
                                  (uu___386_3523.FStar_Syntax_Syntax.close_wp);
                                FStar_Syntax_Syntax.assert_p =
                                  (uu___386_3523.FStar_Syntax_Syntax.assert_p);
                                FStar_Syntax_Syntax.assume_p =
                                  (uu___386_3523.FStar_Syntax_Syntax.assume_p);
                                FStar_Syntax_Syntax.null_wp =
                                  (uu___386_3523.FStar_Syntax_Syntax.null_wp);
                                FStar_Syntax_Syntax.trivial =
                                  (uu___386_3523.FStar_Syntax_Syntax.trivial);
                                FStar_Syntax_Syntax.repr =
                                  (uu___386_3523.FStar_Syntax_Syntax.repr);
                                FStar_Syntax_Syntax.elaborated =
                                  (uu___386_3523.FStar_Syntax_Syntax.elaborated);
                                FStar_Syntax_Syntax.actions =
                                  (uu___386_3523.FStar_Syntax_Syntax.actions);
                                FStar_Syntax_Syntax.eff_attrs =
                                  (uu___386_3523.FStar_Syntax_Syntax.eff_attrs)
                              }  in
                            let ed2 =
                              match (effect_params, annotated_univ_names)
                              with
                              | ([],[]) -> ed1
                              | uu____3551 ->
                                  let op uu____3583 =
                                    match uu____3583 with
                                    | (us,t) ->
                                        let n_us = FStar_List.length us  in
                                        let uu____3603 =
                                          let uu____3604 =
                                            FStar_Syntax_Subst.shift_subst
                                              n_us opening
                                             in
                                          let uu____3613 = open_univs n_us t
                                             in
                                          FStar_Syntax_Subst.subst uu____3604
                                            uu____3613
                                           in
                                        (us, uu____3603)
                                     in
                                  let uu___387_3622 = ed1  in
                                  let uu____3623 =
                                    let uu____3624 =
                                      let uu____3625 =
                                        op
                                          ([],
                                            ((ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m))
                                         in
                                      FStar_Pervasives_Native.snd uu____3625
                                       in
                                    let uu____3636 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                       in
                                    let uu____3637 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                       in
                                    {
                                      FStar_Syntax_Syntax.monad_m =
                                        uu____3624;
                                      FStar_Syntax_Syntax.monad_ret =
                                        uu____3636;
                                      FStar_Syntax_Syntax.monad_bind =
                                        uu____3637
                                    }  in
                                  let uu____3638 =
                                    op ed1.FStar_Syntax_Syntax.if_then_else
                                     in
                                  let uu____3639 =
                                    op ed1.FStar_Syntax_Syntax.ite_wp  in
                                  let uu____3640 =
                                    op ed1.FStar_Syntax_Syntax.stronger  in
                                  let uu____3641 =
                                    op ed1.FStar_Syntax_Syntax.close_wp  in
                                  let uu____3642 =
                                    op ed1.FStar_Syntax_Syntax.assert_p  in
                                  let uu____3643 =
                                    op ed1.FStar_Syntax_Syntax.assume_p  in
                                  let uu____3644 =
                                    op ed1.FStar_Syntax_Syntax.null_wp  in
                                  let uu____3645 =
                                    op ed1.FStar_Syntax_Syntax.trivial  in
                                  let uu____3646 =
                                    let uu____3647 =
                                      let uu____3648 =
                                        op
                                          ([],
                                            ((ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m))
                                         in
                                      FStar_Pervasives_Native.snd uu____3648
                                       in
                                    let uu____3659 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                       in
                                    let uu____3660 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                       in
                                    {
                                      FStar_Syntax_Syntax.monad_m =
                                        uu____3647;
                                      FStar_Syntax_Syntax.monad_ret =
                                        uu____3659;
                                      FStar_Syntax_Syntax.monad_bind =
                                        uu____3660
                                    }  in
                                  let uu____3661 =
                                    FStar_List.map
                                      (fun a  ->
                                         let uu___388_3669 = a  in
                                         let uu____3670 =
                                           let uu____3671 =
                                             op
                                               ((a.FStar_Syntax_Syntax.action_univs),
                                                 (a.FStar_Syntax_Syntax.action_defn))
                                              in
                                           FStar_Pervasives_Native.snd
                                             uu____3671
                                            in
                                         let uu____3682 =
                                           let uu____3683 =
                                             op
                                               ((a.FStar_Syntax_Syntax.action_univs),
                                                 (a.FStar_Syntax_Syntax.action_typ))
                                              in
                                           FStar_Pervasives_Native.snd
                                             uu____3683
                                            in
                                         {
                                           FStar_Syntax_Syntax.action_name =
                                             (uu___388_3669.FStar_Syntax_Syntax.action_name);
                                           FStar_Syntax_Syntax.action_unqualified_name
                                             =
                                             (uu___388_3669.FStar_Syntax_Syntax.action_unqualified_name);
                                           FStar_Syntax_Syntax.action_univs =
                                             (uu___388_3669.FStar_Syntax_Syntax.action_univs);
                                           FStar_Syntax_Syntax.action_params
                                             =
                                             (uu___388_3669.FStar_Syntax_Syntax.action_params);
                                           FStar_Syntax_Syntax.action_defn =
                                             uu____3670;
                                           FStar_Syntax_Syntax.action_typ =
                                             uu____3682
                                         }) ed1.FStar_Syntax_Syntax.actions
                                     in
                                  {
                                    FStar_Syntax_Syntax.cattributes =
                                      (uu___387_3622.FStar_Syntax_Syntax.cattributes);
                                    FStar_Syntax_Syntax.mname =
                                      (uu___387_3622.FStar_Syntax_Syntax.mname);
                                    FStar_Syntax_Syntax.univs =
                                      annotated_univ_names;
                                    FStar_Syntax_Syntax.binders =
                                      (uu___387_3622.FStar_Syntax_Syntax.binders);
                                    FStar_Syntax_Syntax.spec = uu____3623;
                                    FStar_Syntax_Syntax.signature =
                                      (uu___387_3622.FStar_Syntax_Syntax.signature);
                                    FStar_Syntax_Syntax.if_then_else =
                                      uu____3638;
                                    FStar_Syntax_Syntax.ite_wp = uu____3639;
                                    FStar_Syntax_Syntax.stronger = uu____3640;
                                    FStar_Syntax_Syntax.close_wp = uu____3641;
                                    FStar_Syntax_Syntax.assert_p = uu____3642;
                                    FStar_Syntax_Syntax.assume_p = uu____3643;
                                    FStar_Syntax_Syntax.null_wp = uu____3644;
                                    FStar_Syntax_Syntax.trivial = uu____3645;
                                    FStar_Syntax_Syntax.repr = uu____3646;
                                    FStar_Syntax_Syntax.elaborated =
                                      (uu___387_3622.FStar_Syntax_Syntax.elaborated);
                                    FStar_Syntax_Syntax.actions = uu____3661;
                                    FStar_Syntax_Syntax.eff_attrs =
                                      (uu___387_3622.FStar_Syntax_Syntax.eff_attrs)
                                  }
                               in
                            ((let uu____3695 =
                                FStar_TypeChecker_Env.debug env0
                                  (FStar_Options.Other "ED")
                                 in
                              if uu____3695
                              then
                                let uu____3699 =
                                  FStar_Syntax_Print.eff_decl_to_string ed2
                                   in
                                FStar_Util.print1
                                  "eff_decl after opening:\n\t%s\n"
                                  uu____3699
                              else ());
                             (let wp_with_fresh_result_type env2 mname
                                signature2 =
                                let fail1 t =
                                  let uu____3738 =
                                    FStar_TypeChecker_Err.unexpected_signature_for_monad
                                      env2 mname t
                                     in
                                  let uu____3744 =
                                    FStar_Ident.range_of_lid mname  in
                                  FStar_Errors.raise_error uu____3738
                                    uu____3744
                                   in
                                let uu____3751 =
                                  let uu____3752 =
                                    FStar_Syntax_Subst.compress signature2
                                     in
                                  uu____3752.FStar_Syntax_Syntax.n  in
                                match uu____3751 with
                                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                    let bs1 =
                                      FStar_Syntax_Subst.open_binders bs  in
                                    (match bs1 with
                                     | (a,uu____3791)::(wp,uu____3793)::[] ->
                                         (a, (wp.FStar_Syntax_Syntax.sort))
                                     | uu____3822 -> fail1 signature2)
                                | uu____3823 -> fail1 signature2  in
                              let uu____3824 =
                                wp_with_fresh_result_type env1
                                  ed2.FStar_Syntax_Syntax.mname signature1
                                 in
                              match uu____3824 with
                              | (a,wp_a) ->
                                  let fresh_effect_signature uu____3848 =
                                    match annotated_univ_names with
                                    | [] ->
                                        let uu____3855 =
                                          FStar_TypeChecker_TcTerm.tc_trivial_guard
                                            env1 signature_un
                                           in
                                        (match uu____3855 with
                                         | (signature2,uu____3867) ->
                                             wp_with_fresh_result_type env1
                                               ed2.FStar_Syntax_Syntax.mname
                                               signature2)
                                    | uu____3868 ->
                                        let uu____3871 =
                                          let uu____3876 =
                                            let uu____3877 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                annotated_univ_names
                                                signature1
                                               in
                                            (annotated_univ_names,
                                              uu____3877)
                                             in
                                          FStar_TypeChecker_Env.inst_tscheme
                                            uu____3876
                                           in
                                        (match uu____3871 with
                                         | (uu____3890,signature2) ->
                                             wp_with_fresh_result_type env1
                                               ed2.FStar_Syntax_Syntax.mname
                                               signature2)
                                     in
                                  let env2 =
                                    let uu____3893 =
                                      FStar_Syntax_Syntax.new_bv
                                        FStar_Pervasives_Native.None
                                        signature1
                                       in
                                    FStar_TypeChecker_Env.push_bv env1
                                      uu____3893
                                     in
                                  ((let uu____3895 =
                                      FStar_Syntax_Print.lid_to_string
                                        ed2.FStar_Syntax_Syntax.mname
                                       in
                                    let uu____3897 =
                                      FStar_Syntax_Print.binders_to_string
                                        " " ed2.FStar_Syntax_Syntax.binders
                                       in
                                    let uu____3900 =
                                      FStar_Syntax_Print.term_to_string
                                        signature1
                                       in
                                    let uu____3902 =
                                      let uu____3904 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      FStar_Syntax_Print.term_to_string
                                        uu____3904
                                       in
                                    let uu____3905 =
                                      FStar_Syntax_Print.term_to_string
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    FStar_Util.print5
                                      "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                      uu____3895 uu____3897 uu____3900
                                      uu____3902 uu____3905);
                                   (let check_and_gen' env3 uu____3938 k =
                                      match uu____3938 with
                                      | (us,t) ->
                                          (match annotated_univ_names with
                                           | [] -> check_and_gen env3 t k
                                           | uu____3974::uu____3975 ->
                                               let uu____3978 =
                                                 FStar_Syntax_Subst.subst_tscheme
                                                   open_annotated_univs
                                                   (us, t)
                                                  in
                                               (match uu____3978 with
                                                | (us1,t1) ->
                                                    let uu____4001 =
                                                      FStar_Syntax_Subst.open_univ_vars
                                                        us1 t1
                                                       in
                                                    (match uu____4001 with
                                                     | (us2,t2) ->
                                                         let uu____4016 =
                                                           let uu____4017 =
                                                             FStar_TypeChecker_Env.push_univ_vars
                                                               env3 us2
                                                              in
                                                           tc_check_trivial_guard
                                                             uu____4017 t2 k
                                                            in
                                                         let uu____4018 =
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             us2 t2
                                                            in
                                                         (us2, uu____4018))))
                                       in
                                    let return_wp =
                                      let expected_k =
                                        let uu____4037 =
                                          let uu____4046 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4053 =
                                            let uu____4062 =
                                              let uu____4069 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4069
                                               in
                                            [uu____4062]  in
                                          uu____4046 :: uu____4053  in
                                        let uu____4088 =
                                          FStar_Syntax_Syntax.mk_GTotal wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4037
                                          uu____4088
                                         in
                                      check_and_gen' env2
                                        (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                        expected_k
                                       in
                                    let bind_wp =
                                      let uu____4092 =
                                        fresh_effect_signature ()  in
                                      match uu____4092 with
                                      | (b,wp_b) ->
                                          let a_wp_b =
                                            let uu____4108 =
                                              let uu____4117 =
                                                let uu____4124 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____4124
                                                 in
                                              [uu____4117]  in
                                            let uu____4137 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_b
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4108 uu____4137
                                             in
                                          let expected_k =
                                            let uu____4143 =
                                              let uu____4152 =
                                                FStar_Syntax_Syntax.null_binder
                                                  FStar_Syntax_Syntax.t_range
                                                 in
                                              let uu____4159 =
                                                let uu____4168 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____4175 =
                                                  let uu____4184 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____4191 =
                                                    let uu____4200 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_a
                                                       in
                                                    let uu____4207 =
                                                      let uu____4216 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          a_wp_b
                                                         in
                                                      [uu____4216]  in
                                                    uu____4200 :: uu____4207
                                                     in
                                                  uu____4184 :: uu____4191
                                                   in
                                                uu____4168 :: uu____4175  in
                                              uu____4152 :: uu____4159  in
                                            let uu____4259 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_b
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4143 uu____4259
                                             in
                                          check_and_gen' env2
                                            (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                            expected_k
                                       in
                                    let if_then_else1 =
                                      let p =
                                        let uu____4272 =
                                          let uu____4275 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4275
                                           in
                                        let uu____4276 =
                                          let uu____4277 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4277
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4272
                                          uu____4276
                                         in
                                      let expected_k =
                                        let uu____4289 =
                                          let uu____4298 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4305 =
                                            let uu____4314 =
                                              FStar_Syntax_Syntax.mk_binder p
                                               in
                                            let uu____4321 =
                                              let uu____4330 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              let uu____4337 =
                                                let uu____4346 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____4346]  in
                                              uu____4330 :: uu____4337  in
                                            uu____4314 :: uu____4321  in
                                          uu____4298 :: uu____4305  in
                                        let uu____4383 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4289
                                          uu____4383
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.if_then_else
                                        expected_k
                                       in
                                    let ite_wp =
                                      let expected_k =
                                        let uu____4398 =
                                          let uu____4407 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4414 =
                                            let uu____4423 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____4423]  in
                                          uu____4407 :: uu____4414  in
                                        let uu____4448 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4398
                                          uu____4448
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.ite_wp
                                        expected_k
                                       in
                                    let stronger =
                                      let uu____4452 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____4452 with
                                      | (t,uu____4458) ->
                                          let expected_k =
                                            let uu____4462 =
                                              let uu____4471 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4478 =
                                                let uu____4487 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____4494 =
                                                  let uu____4503 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____4503]  in
                                                uu____4487 :: uu____4494  in
                                              uu____4471 :: uu____4478  in
                                            let uu____4534 =
                                              FStar_Syntax_Syntax.mk_Total t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4462 uu____4534
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.stronger
                                            expected_k
                                       in
                                    let close_wp =
                                      let b =
                                        let uu____4547 =
                                          let uu____4550 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4550
                                           in
                                        let uu____4551 =
                                          let uu____4552 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4552
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4547
                                          uu____4551
                                         in
                                      let b_wp_a =
                                        let uu____4564 =
                                          let uu____4573 =
                                            let uu____4580 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                b
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____4580
                                             in
                                          [uu____4573]  in
                                        let uu____4593 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4564
                                          uu____4593
                                         in
                                      let expected_k =
                                        let uu____4599 =
                                          let uu____4608 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4615 =
                                            let uu____4624 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4631 =
                                              let uu____4640 =
                                                FStar_Syntax_Syntax.null_binder
                                                  b_wp_a
                                                 in
                                              [uu____4640]  in
                                            uu____4624 :: uu____4631  in
                                          uu____4608 :: uu____4615  in
                                        let uu____4671 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4599
                                          uu____4671
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.close_wp
                                        expected_k
                                       in
                                    let assert_p =
                                      let expected_k =
                                        let uu____4686 =
                                          let uu____4695 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4702 =
                                            let uu____4711 =
                                              let uu____4718 =
                                                let uu____4719 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____4719
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4718
                                               in
                                            let uu____4728 =
                                              let uu____4737 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____4737]  in
                                            uu____4711 :: uu____4728  in
                                          uu____4695 :: uu____4702  in
                                        let uu____4768 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4686
                                          uu____4768
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.assert_p
                                        expected_k
                                       in
                                    let assume_p =
                                      let expected_k =
                                        let uu____4783 =
                                          let uu____4792 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4799 =
                                            let uu____4808 =
                                              let uu____4815 =
                                                let uu____4816 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____4816
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4815
                                               in
                                            let uu____4825 =
                                              let uu____4834 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____4834]  in
                                            uu____4808 :: uu____4825  in
                                          uu____4792 :: uu____4799  in
                                        let uu____4865 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4783
                                          uu____4865
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.assume_p
                                        expected_k
                                       in
                                    let null_wp =
                                      let expected_k =
                                        let uu____4880 =
                                          let uu____4889 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          [uu____4889]  in
                                        let uu____4908 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4880
                                          uu____4908
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.null_wp
                                        expected_k
                                       in
                                    let trivial_wp =
                                      let uu____4912 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____4912 with
                                      | (t,uu____4918) ->
                                          let expected_k =
                                            let uu____4922 =
                                              let uu____4931 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4938 =
                                                let uu____4947 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____4947]  in
                                              uu____4931 :: uu____4938  in
                                            let uu____4972 =
                                              FStar_Syntax_Syntax.mk_GTotal t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4922 uu____4972
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.trivial
                                            expected_k
                                       in
                                    let uu____4975 =
                                      let uu____4988 =
                                        let uu____4989 =
                                          FStar_Syntax_Subst.compress
                                            (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                           in
                                        uu____4989.FStar_Syntax_Syntax.n  in
                                      match uu____4988 with
                                      | FStar_Syntax_Syntax.Tm_unknown  ->
                                          (((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m),
                                            ((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind),
                                            ((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret),
                                            (ed2.FStar_Syntax_Syntax.actions))
                                      | uu____5008 ->
                                          let repr =
                                            let uu____5010 =
                                              FStar_Syntax_Util.type_u ()  in
                                            match uu____5010 with
                                            | (t,uu____5016) ->
                                                let expected_k =
                                                  let uu____5020 =
                                                    let uu____5029 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a
                                                       in
                                                    let uu____5036 =
                                                      let uu____5045 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          wp_a
                                                         in
                                                      [uu____5045]  in
                                                    uu____5029 :: uu____5036
                                                     in
                                                  let uu____5070 =
                                                    FStar_Syntax_Syntax.mk_GTotal
                                                      t
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____5020 uu____5070
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
                                            let uu____5087 =
                                              let uu____5094 =
                                                let uu____5095 =
                                                  let uu____5112 =
                                                    let uu____5123 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        t
                                                       in
                                                    let uu____5132 =
                                                      let uu____5143 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          wp
                                                         in
                                                      [uu____5143]  in
                                                    uu____5123 :: uu____5132
                                                     in
                                                  (repr1, uu____5112)  in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____5095
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____5094
                                               in
                                            uu____5087
                                              FStar_Pervasives_Native.None
                                              FStar_Range.dummyRange
                                             in
                                          let mk_repr a1 wp =
                                            let uu____5204 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            mk_repr' uu____5204 wp  in
                                          let destruct_repr t =
                                            let uu____5219 =
                                              let uu____5220 =
                                                FStar_Syntax_Subst.compress t
                                                 in
                                              uu____5220.FStar_Syntax_Syntax.n
                                               in
                                            match uu____5219 with
                                            | FStar_Syntax_Syntax.Tm_app
                                                (uu____5231,(t1,uu____5233)::
                                                 (wp,uu____5235)::[])
                                                -> (t1, wp)
                                            | uu____5294 ->
                                                failwith
                                                  "Unexpected repr type"
                                             in
                                          let bind_repr =
                                            let r =
                                              let uu____5306 =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  FStar_Parser_Const.range_0
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              FStar_All.pipe_right uu____5306
                                                FStar_Syntax_Syntax.fv_to_tm
                                               in
                                            let uu____5307 =
                                              fresh_effect_signature ()  in
                                            match uu____5307 with
                                            | (b,wp_b) ->
                                                let a_wp_b =
                                                  let uu____5323 =
                                                    let uu____5332 =
                                                      let uu____5339 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.null_binder
                                                        uu____5339
                                                       in
                                                    [uu____5332]  in
                                                  let uu____5352 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      wp_b
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____5323 uu____5352
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
                                                  let uu____5360 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a
                                                     in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "x_a"
                                                    FStar_Pervasives_Native.None
                                                    uu____5360
                                                   in
                                                let wp_g_x =
                                                  let uu____5365 =
                                                    let uu____5370 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        wp_g
                                                       in
                                                    let uu____5371 =
                                                      let uu____5372 =
                                                        let uu____5381 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Syntax.as_arg
                                                          uu____5381
                                                         in
                                                      [uu____5372]  in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____5370 uu____5371
                                                     in
                                                  uu____5365
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                let res =
                                                  let wp =
                                                    let uu____5414 =
                                                      let uu____5419 =
                                                        let uu____5420 =
                                                          FStar_TypeChecker_Env.inst_tscheme
                                                            bind_wp
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____5420
                                                          FStar_Pervasives_Native.snd
                                                         in
                                                      let uu____5429 =
                                                        let uu____5430 =
                                                          let uu____5433 =
                                                            let uu____5436 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                a
                                                               in
                                                            let uu____5437 =
                                                              let uu____5440
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  b
                                                                 in
                                                              let uu____5441
                                                                =
                                                                let uu____5444
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f
                                                                   in
                                                                let uu____5445
                                                                  =
                                                                  let uu____5448
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                  [uu____5448]
                                                                   in
                                                                uu____5444 ::
                                                                  uu____5445
                                                                 in
                                                              uu____5440 ::
                                                                uu____5441
                                                               in
                                                            uu____5436 ::
                                                              uu____5437
                                                             in
                                                          r :: uu____5433  in
                                                        FStar_List.map
                                                          FStar_Syntax_Syntax.as_arg
                                                          uu____5430
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____5419 uu____5429
                                                       in
                                                    uu____5414
                                                      FStar_Pervasives_Native.None
                                                      FStar_Range.dummyRange
                                                     in
                                                  mk_repr b wp  in
                                                let maybe_range_arg =
                                                  let uu____5468 =
                                                    FStar_Util.for_some
                                                      (FStar_Syntax_Util.attr_eq
                                                         FStar_Syntax_Util.dm4f_bind_range_attr)
                                                      ed2.FStar_Syntax_Syntax.eff_attrs
                                                     in
                                                  if uu____5468
                                                  then
                                                    let uu____5479 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        FStar_Syntax_Syntax.t_range
                                                       in
                                                    let uu____5486 =
                                                      let uu____5495 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          FStar_Syntax_Syntax.t_range
                                                         in
                                                      [uu____5495]  in
                                                    uu____5479 :: uu____5486
                                                  else []  in
                                                let expected_k =
                                                  let uu____5531 =
                                                    let uu____5540 =
                                                      let uu____5549 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a
                                                         in
                                                      let uu____5556 =
                                                        let uu____5565 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            b
                                                           in
                                                        [uu____5565]  in
                                                      uu____5549 ::
                                                        uu____5556
                                                       in
                                                    let uu____5590 =
                                                      let uu____5599 =
                                                        let uu____5608 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp_f
                                                           in
                                                        let uu____5615 =
                                                          let uu____5624 =
                                                            let uu____5631 =
                                                              let uu____5632
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_f
                                                                 in
                                                              mk_repr a
                                                                uu____5632
                                                               in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____5631
                                                             in
                                                          let uu____5633 =
                                                            let uu____5642 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_g
                                                               in
                                                            let uu____5649 =
                                                              let uu____5658
                                                                =
                                                                let uu____5665
                                                                  =
                                                                  let uu____5666
                                                                    =
                                                                    let uu____5675
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____5675]
                                                                     in
                                                                  let uu____5694
                                                                    =
                                                                    let uu____5697
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____5697
                                                                     in
                                                                  FStar_Syntax_Util.arrow
                                                                    uu____5666
                                                                    uu____5694
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____5665
                                                                 in
                                                              [uu____5658]
                                                               in
                                                            uu____5642 ::
                                                              uu____5649
                                                             in
                                                          uu____5624 ::
                                                            uu____5633
                                                           in
                                                        uu____5608 ::
                                                          uu____5615
                                                         in
                                                      FStar_List.append
                                                        maybe_range_arg
                                                        uu____5599
                                                       in
                                                    FStar_List.append
                                                      uu____5540 uu____5590
                                                     in
                                                  let uu____5742 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      res
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    uu____5531 uu____5742
                                                   in
                                                let uu____5745 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env2 expected_k
                                                   in
                                                (match uu____5745 with
                                                 | (expected_k1,uu____5753,uu____5754)
                                                     ->
                                                     let env3 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env2
                                                         (FStar_Pervasives_Native.snd
                                                            (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind).FStar_Syntax_Syntax.pos
                                                        in
                                                     let env4 =
                                                       let uu___389_5761 =
                                                         env3  in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.is_pattern
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.is_pattern);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.instantiate_imp);
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           = true;
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___389_5761.FStar_TypeChecker_Env.nbe)
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
                                              let uu____5774 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.gen_bv
                                                "x_a"
                                                FStar_Pervasives_Native.None
                                                uu____5774
                                               in
                                            let res =
                                              let wp =
                                                let uu____5782 =
                                                  let uu____5787 =
                                                    let uu____5788 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        return_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____5788
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____5797 =
                                                    let uu____5798 =
                                                      let uu____5801 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      let uu____5802 =
                                                        let uu____5805 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        [uu____5805]  in
                                                      uu____5801 ::
                                                        uu____5802
                                                       in
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.as_arg
                                                      uu____5798
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____5787 uu____5797
                                                   in
                                                uu____5782
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              mk_repr a wp  in
                                            let expected_k =
                                              let uu____5819 =
                                                let uu____5828 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____5835 =
                                                  let uu____5844 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x_a
                                                     in
                                                  [uu____5844]  in
                                                uu____5828 :: uu____5835  in
                                              let uu____5869 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  res
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____5819 uu____5869
                                               in
                                            let uu____5872 =
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                env2 expected_k
                                               in
                                            match uu____5872 with
                                            | (expected_k1,uu____5880,uu____5881)
                                                ->
                                                let env3 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env2
                                                    (FStar_Pervasives_Native.snd
                                                       (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret).FStar_Syntax_Syntax.pos
                                                   in
                                                let uu____5887 =
                                                  check_and_gen' env3
                                                    (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                                    expected_k1
                                                   in
                                                (match uu____5887 with
                                                 | (univs1,repr1) ->
                                                     (match univs1 with
                                                      | [] -> ([], repr1)
                                                      | uu____5910 ->
                                                          FStar_Errors.raise_error
                                                            (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                              "Unexpected universe-polymorphic return for effect")
                                                            repr1.FStar_Syntax_Syntax.pos))
                                             in
                                          let actions =
                                            let check_action act =
                                              let uu____5925 =
                                                if
                                                  act.FStar_Syntax_Syntax.action_univs
                                                    = []
                                                then (env2, act)
                                                else
                                                  (let uu____5939 =
                                                     FStar_Syntax_Subst.univ_var_opening
                                                       act.FStar_Syntax_Syntax.action_univs
                                                      in
                                                   match uu____5939 with
                                                   | (usubst,uvs) ->
                                                       let uu____5962 =
                                                         FStar_TypeChecker_Env.push_univ_vars
                                                           env2 uvs
                                                          in
                                                       let uu____5963 =
                                                         let uu___390_5964 =
                                                           act  in
                                                         let uu____5965 =
                                                           FStar_Syntax_Subst.subst_binders
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_params
                                                            in
                                                         let uu____5966 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____5967 =
                                                           FStar_Syntax_Subst.subst
                                                             usubst
                                                             act.FStar_Syntax_Syntax.action_typ
                                                            in
                                                         {
                                                           FStar_Syntax_Syntax.action_name
                                                             =
                                                             (uu___390_5964.FStar_Syntax_Syntax.action_name);
                                                           FStar_Syntax_Syntax.action_unqualified_name
                                                             =
                                                             (uu___390_5964.FStar_Syntax_Syntax.action_unqualified_name);
                                                           FStar_Syntax_Syntax.action_univs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.action_params
                                                             = uu____5965;
                                                           FStar_Syntax_Syntax.action_defn
                                                             = uu____5966;
                                                           FStar_Syntax_Syntax.action_typ
                                                             = uu____5967
                                                         }  in
                                                       (uu____5962,
                                                         uu____5963))
                                                 in
                                              match uu____5925 with
                                              | (env3,act1) ->
                                                  let act_typ =
                                                    let uu____5971 =
                                                      let uu____5972 =
                                                        FStar_Syntax_Subst.compress
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                         in
                                                      uu____5972.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____5971 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,c) ->
                                                        let c1 =
                                                          FStar_Syntax_Util.comp_to_comp_typ
                                                            c
                                                           in
                                                        let uu____5998 =
                                                          FStar_Ident.lid_equals
                                                            c1.FStar_Syntax_Syntax.effect_name
                                                            ed2.FStar_Syntax_Syntax.mname
                                                           in
                                                        if uu____5998
                                                        then
                                                          let uu____6001 =
                                                            let uu____6004 =
                                                              let uu____6005
                                                                =
                                                                let uu____6006
                                                                  =
                                                                  FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____6006
                                                                 in
                                                              mk_repr'
                                                                c1.FStar_Syntax_Syntax.result_typ
                                                                uu____6005
                                                               in
                                                            FStar_Syntax_Syntax.mk_Total
                                                              uu____6004
                                                             in
                                                          FStar_Syntax_Util.arrow
                                                            bs uu____6001
                                                        else
                                                          act1.FStar_Syntax_Syntax.action_typ
                                                    | uu____6029 ->
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  let uu____6030 =
                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                      env3 act_typ
                                                     in
                                                  (match uu____6030 with
                                                   | (act_typ1,uu____6038,g_t)
                                                       ->
                                                       let env' =
                                                         let uu___391_6041 =
                                                           FStar_TypeChecker_Env.set_expected_typ
                                                             env3 act_typ1
                                                            in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             = false;
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.lax);
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___391_6041.FStar_TypeChecker_Env.nbe)
                                                         }  in
                                                       ((let uu____6044 =
                                                           FStar_Ident.text_of_lid
                                                             act1.FStar_Syntax_Syntax.action_name
                                                            in
                                                         let uu____6046 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____6048 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act_typ1
                                                            in
                                                         FStar_Util.print3
                                                           "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                           uu____6044
                                                           uu____6046
                                                           uu____6048);
                                                        (let uu____6051 =
                                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                             env'
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         match uu____6051
                                                         with
                                                         | (act_defn,uu____6059,g_a)
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
                                                             let uu____6063 =
                                                               let act_typ3 =
                                                                 FStar_Syntax_Subst.compress
                                                                   act_typ2
                                                                  in
                                                               match 
                                                                 act_typ3.FStar_Syntax_Syntax.n
                                                               with
                                                               | FStar_Syntax_Syntax.Tm_arrow
                                                                   (bs,c) ->
                                                                   let uu____6099
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                   (match uu____6099
                                                                    with
                                                                    | 
                                                                    (bs1,uu____6111)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6118
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____6118
                                                                     in
                                                                    let uu____6121
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____6121
                                                                    with
                                                                    | 
                                                                    (k1,uu____6135,g)
                                                                    ->
                                                                    (k1, g)))
                                                               | uu____6139
                                                                   ->
                                                                   let uu____6140
                                                                    =
                                                                    let uu____6146
                                                                    =
                                                                    let uu____6148
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____6150
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____6148
                                                                    uu____6150
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____6146)
                                                                     in
                                                                   FStar_Errors.raise_error
                                                                    uu____6140
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                in
                                                             (match uu____6063
                                                              with
                                                              | (expected_k,g_k)
                                                                  ->
                                                                  let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env3
                                                                    act_typ2
                                                                    expected_k
                                                                     in
                                                                  ((let uu____6168
                                                                    =
                                                                    let uu____6169
                                                                    =
                                                                    let uu____6170
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____6170
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____6169
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env3
                                                                    uu____6168);
                                                                   (let act_typ3
                                                                    =
                                                                    let uu____6172
                                                                    =
                                                                    let uu____6173
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____6173.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____6172
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____6198
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____6198
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____6205
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____6205
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____6225
                                                                    =
                                                                    let uu____6226
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____6226]
                                                                     in
                                                                    let uu____6227
                                                                    =
                                                                    let uu____6238
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____6238]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6225;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6227;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____6263
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____6263))
                                                                    | 
                                                                    uu____6266
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____6268
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                    else
                                                                    (let uu____6290
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____6290))
                                                                     in
                                                                    match uu____6268
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
                                                                    let uu___392_6309
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___392_6309.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___392_6309.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___392_6309.FStar_Syntax_Syntax.action_params);
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
                                    match uu____4975 with
                                    | (repr,bind_repr,return_repr,actions) ->
                                        let t0 =
                                          let uu____6333 =
                                            FStar_Syntax_Syntax.mk_Total
                                              signature1
                                             in
                                          FStar_Syntax_Util.arrow
                                            ed2.FStar_Syntax_Syntax.binders
                                            uu____6333
                                           in
                                        let uu____6336 =
                                          let uu____6341 =
                                            FStar_TypeChecker_Util.generalize_universes
                                              env0 t0
                                             in
                                          match uu____6341 with
                                          | (gen_univs,t) ->
                                              (match annotated_univ_names
                                               with
                                               | [] -> (gen_univs, t)
                                               | uu____6360 ->
                                                   let uu____6363 =
                                                     ((FStar_List.length
                                                         gen_univs)
                                                        =
                                                        (FStar_List.length
                                                           annotated_univ_names))
                                                       &&
                                                       (FStar_List.forall2
                                                          (fun u1  ->
                                                             fun u2  ->
                                                               let uu____6370
                                                                 =
                                                                 FStar_Syntax_Syntax.order_univ_name
                                                                   u1 u2
                                                                  in
                                                               uu____6370 =
                                                                 (Prims.parse_int "0"))
                                                          gen_univs
                                                          annotated_univ_names)
                                                      in
                                                   if uu____6363
                                                   then (gen_univs, t)
                                                   else
                                                     (let uu____6381 =
                                                        let uu____6387 =
                                                          let uu____6389 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 annotated_univ_names)
                                                             in
                                                          let uu____6391 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 gen_univs)
                                                             in
                                                          FStar_Util.format2
                                                            "Expected an effect definition with %s universes; but found %s"
                                                            uu____6389
                                                            uu____6391
                                                           in
                                                        (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                          uu____6387)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____6381
                                                        signature1.FStar_Syntax_Syntax.pos))
                                           in
                                        (match uu____6336 with
                                         | (univs1,t) ->
                                             let signature2 =
                                               let uu____6402 =
                                                 let uu____6415 =
                                                   let uu____6416 =
                                                     FStar_Syntax_Subst.compress
                                                       t
                                                      in
                                                   uu____6416.FStar_Syntax_Syntax.n
                                                    in
                                                 (effect_params, uu____6415)
                                                  in
                                               match uu____6402 with
                                               | ([],uu____6427) -> t
                                               | (uu____6442,FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____6443,c)) ->
                                                   FStar_Syntax_Util.comp_result
                                                     c
                                               | uu____6481 ->
                                                   failwith
                                                     "Impossible : t is an arrow"
                                                in
                                             let close1 n1 ts =
                                               let ts1 =
                                                 let uu____6509 =
                                                   FStar_Syntax_Subst.close_tscheme
                                                     effect_params ts
                                                    in
                                                 FStar_Syntax_Subst.close_univ_vars_tscheme
                                                   univs1 uu____6509
                                                  in
                                               let m =
                                                 FStar_List.length
                                                   (FStar_Pervasives_Native.fst
                                                      ts1)
                                                  in
                                               (let uu____6516 =
                                                  ((n1 >=
                                                      (Prims.parse_int "0"))
                                                     &&
                                                     (let uu____6520 =
                                                        FStar_Syntax_Util.is_unknown
                                                          (FStar_Pervasives_Native.snd
                                                             ts1)
                                                         in
                                                      Prims.op_Negation
                                                        uu____6520))
                                                    && (m <> n1)
                                                   in
                                                if uu____6516
                                                then
                                                  let error =
                                                    if m < n1
                                                    then
                                                      "not universe-polymorphic enough"
                                                    else
                                                      "too universe-polymorphic"
                                                     in
                                                  let err_msg =
                                                    let uu____6548 =
                                                      FStar_Util.string_of_int
                                                        m
                                                       in
                                                    let uu____6556 =
                                                      FStar_Util.string_of_int
                                                        n1
                                                       in
                                                    let uu____6558 =
                                                      FStar_Syntax_Print.tscheme_to_string
                                                        ts1
                                                       in
                                                    FStar_Util.format4
                                                      "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                      error uu____6548
                                                      uu____6556 uu____6558
                                                     in
                                                  FStar_Errors.raise_error
                                                    (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                      err_msg)
                                                    (FStar_Pervasives_Native.snd
                                                       ts1).FStar_Syntax_Syntax.pos
                                                else ());
                                               ts1  in
                                             let close_action act =
                                               let uu____6574 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               match uu____6574 with
                                               | (univs2,defn) ->
                                                   let uu____6590 =
                                                     close1
                                                       (~-
                                                          (Prims.parse_int "1"))
                                                       ((act.FStar_Syntax_Syntax.action_univs),
                                                         (act.FStar_Syntax_Syntax.action_typ))
                                                      in
                                                   (match uu____6590 with
                                                    | (univs',typ) ->
                                                        let uu___393_6607 =
                                                          act  in
                                                        {
                                                          FStar_Syntax_Syntax.action_name
                                                            =
                                                            (uu___393_6607.FStar_Syntax_Syntax.action_name);
                                                          FStar_Syntax_Syntax.action_unqualified_name
                                                            =
                                                            (uu___393_6607.FStar_Syntax_Syntax.action_unqualified_name);
                                                          FStar_Syntax_Syntax.action_univs
                                                            = univs2;
                                                          FStar_Syntax_Syntax.action_params
                                                            =
                                                            (uu___393_6607.FStar_Syntax_Syntax.action_params);
                                                          FStar_Syntax_Syntax.action_defn
                                                            = defn;
                                                          FStar_Syntax_Syntax.action_typ
                                                            = typ
                                                        })
                                                in
                                             let ed3 =
                                               let uu___394_6610 = ed2  in
                                               let uu____6611 =
                                                 let uu____6612 =
                                                   close1
                                                     (Prims.parse_int "0")
                                                     return_wp
                                                    in
                                                 let uu____6614 =
                                                   close1
                                                     (Prims.parse_int "1")
                                                     bind_wp
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     =
                                                     FStar_Syntax_Syntax.tun;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____6612;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____6614
                                                 }  in
                                               let uu____6616 =
                                                 close1 (Prims.parse_int "0")
                                                   if_then_else1
                                                  in
                                               let uu____6618 =
                                                 close1 (Prims.parse_int "0")
                                                   ite_wp
                                                  in
                                               let uu____6620 =
                                                 close1 (Prims.parse_int "0")
                                                   stronger
                                                  in
                                               let uu____6622 =
                                                 close1 (Prims.parse_int "1")
                                                   close_wp
                                                  in
                                               let uu____6624 =
                                                 close1 (Prims.parse_int "0")
                                                   assert_p
                                                  in
                                               let uu____6626 =
                                                 close1 (Prims.parse_int "0")
                                                   assume_p
                                                  in
                                               let uu____6628 =
                                                 close1 (Prims.parse_int "0")
                                                   null_wp
                                                  in
                                               let uu____6630 =
                                                 close1 (Prims.parse_int "0")
                                                   trivial_wp
                                                  in
                                               let uu____6632 =
                                                 let uu____6633 =
                                                   let uu____6634 =
                                                     close1
                                                       (Prims.parse_int "0")
                                                       ([], repr)
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____6634
                                                    in
                                                 let uu____6652 =
                                                   close1
                                                     (Prims.parse_int "0")
                                                     return_repr
                                                    in
                                                 let uu____6654 =
                                                   close1
                                                     (Prims.parse_int "1")
                                                     bind_repr
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     = uu____6633;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____6652;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____6654
                                                 }  in
                                               let uu____6656 =
                                                 FStar_List.map close_action
                                                   actions
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.cattributes
                                                   =
                                                   (uu___394_6610.FStar_Syntax_Syntax.cattributes);
                                                 FStar_Syntax_Syntax.mname =
                                                   (uu___394_6610.FStar_Syntax_Syntax.mname);
                                                 FStar_Syntax_Syntax.univs =
                                                   univs1;
                                                 FStar_Syntax_Syntax.binders
                                                   = effect_params;
                                                 FStar_Syntax_Syntax.spec =
                                                   uu____6611;
                                                 FStar_Syntax_Syntax.signature
                                                   = signature2;
                                                 FStar_Syntax_Syntax.if_then_else
                                                   = uu____6616;
                                                 FStar_Syntax_Syntax.ite_wp =
                                                   uu____6618;
                                                 FStar_Syntax_Syntax.stronger
                                                   = uu____6620;
                                                 FStar_Syntax_Syntax.close_wp
                                                   = uu____6622;
                                                 FStar_Syntax_Syntax.assert_p
                                                   = uu____6624;
                                                 FStar_Syntax_Syntax.assume_p
                                                   = uu____6626;
                                                 FStar_Syntax_Syntax.null_wp
                                                   = uu____6628;
                                                 FStar_Syntax_Syntax.trivial
                                                   = uu____6630;
                                                 FStar_Syntax_Syntax.repr =
                                                   uu____6632;
                                                 FStar_Syntax_Syntax.elaborated
                                                   =
                                                   (uu___394_6610.FStar_Syntax_Syntax.elaborated);
                                                 FStar_Syntax_Syntax.actions
                                                   = uu____6656;
                                                 FStar_Syntax_Syntax.eff_attrs
                                                   =
                                                   (uu___394_6610.FStar_Syntax_Syntax.eff_attrs)
                                               }  in
                                             ((let uu____6660 =
                                                 FStar_Syntax_Print.eff_decl_to_string
                                                   ed3
                                                  in
                                               FStar_Util.print_string
                                                 uu____6660);
                                              ed3))))))))))
  
let tc_lex_t :
  'Auu____6673 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____6673 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____6708 = FStar_List.hd ses  in
            uu____6708.FStar_Syntax_Syntax.sigrng  in
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
           | uu____6713 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____6719,[],t,uu____6721,uu____6722);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____6724;
               FStar_Syntax_Syntax.sigattrs = uu____6725;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____6727,_t_top,_lex_t_top,_0_1,uu____6730);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____6732;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____6733;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____6735,_t_cons,_lex_t_cons,_0_2,uu____6738);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____6740;
                 FStar_Syntax_Syntax.sigattrs = uu____6741;_}::[]
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
                 let uu____6792 =
                   let uu____6799 =
                     let uu____6800 =
                       let uu____6807 =
                         let uu____6810 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____6810
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____6807, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____6800  in
                   FStar_Syntax_Syntax.mk uu____6799  in
                 uu____6792 FStar_Pervasives_Native.None r1  in
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
                   let uu____6828 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6828
                    in
                 let hd1 =
                   let uu____6830 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6830
                    in
                 let tl1 =
                   let uu____6832 =
                     let uu____6833 =
                       let uu____6840 =
                         let uu____6841 =
                           let uu____6848 =
                             let uu____6851 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____6851
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____6848, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____6841  in
                       FStar_Syntax_Syntax.mk uu____6840  in
                     uu____6833 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6832
                    in
                 let res =
                   let uu____6860 =
                     let uu____6867 =
                       let uu____6868 =
                         let uu____6875 =
                           let uu____6878 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____6878
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____6875,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____6868  in
                     FStar_Syntax_Syntax.mk uu____6867  in
                   uu____6860 FStar_Pervasives_Native.None r2  in
                 let uu____6884 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____6884
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
               let uu____6923 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____6923;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____6928 ->
               let err_msg =
                 let uu____6933 =
                   let uu____6935 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____6935  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____6933
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
    fun uu____6960  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____6960 with
          | (uvs,t) ->
              let uu____6973 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____6973 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____6985 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____6985 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____7003 =
                        let uu____7006 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____7006
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____7003)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7029 =
          let uu____7030 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7030 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7029 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7055 =
          let uu____7056 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7056 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7055 r
  
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
          (let uu____7105 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____7105
           then
             let uu____7108 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____7108
           else ());
          (let uu____7113 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____7113 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____7144 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____7144 FStar_List.flatten  in
               ((let uu____7158 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____7161 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____7161)
                    in
                 if uu____7158
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
                           let uu____7177 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____7187,uu____7188,uu____7189,uu____7190,uu____7191)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____7200 -> failwith "Impossible!"  in
                           match uu____7177 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.strcat "Inductive type "
                                      (Prims.strcat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____7219 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____7229,uu____7230,ty_lid,uu____7232,uu____7233)
                               -> (data_lid, ty_lid)
                           | uu____7240 -> failwith "Impossible"  in
                         match uu____7219 with
                         | (data_lid,ty_lid) ->
                             let uu____7248 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____7251 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____7251)
                                in
                             if uu____7248
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.strcat "Exception "
                                      (Prims.strcat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____7265 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____7270,uu____7271,uu____7272,uu____7273,uu____7274)
                         -> lid
                     | uu____7283 -> failwith "Impossible"  in
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
                   let uu____7301 =
                     (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____7301
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
          let pop1 uu____7376 =
            let uu____7377 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___396_7387  ->
               match () with
               | () ->
                   let uu____7394 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____7394 (fun r  -> pop1 (); r)) ()
          with | uu___395_7425 -> (pop1 (); FStar_Exn.raise uu___395_7425)
  
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en  ->
    let env =
      let uu____7446 = FStar_Options.using_facts_from ()  in
      FStar_TypeChecker_Env.set_proof_ns uu____7446 en  in
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
      | uu____7750 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____7808 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____7808 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____7833 .
    'Auu____7833 FStar_Pervasives_Native.option -> 'Auu____7833 Prims.list
  =
  fun uu___374_7842  ->
    match uu___374_7842 with
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
            let uu____7922 = collect1 tl1  in
            (match uu____7922 with
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
        | ((e,n1)::uu____8160,[]) ->
            FStar_Pervasives_Native.Some (e, n1, (Prims.parse_int "0"))
        | ([],(e,n1)::uu____8216) ->
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
          let uu____8444 =
            let uu____8446 = FStar_Options.ide ()  in
            Prims.op_Negation uu____8446  in
          if uu____8444
          then
            let uu____8449 =
              let uu____8454 = FStar_TypeChecker_Env.dsenv env  in
              let uu____8455 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____8454 uu____8455  in
            (match uu____8449 with
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
                              let uu____8488 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____8489 =
                                let uu____8495 =
                                  let uu____8497 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____8499 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____8497 uu____8499
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____8495)
                                 in
                              FStar_Errors.log_issue uu____8488 uu____8489
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____8506 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____8507 =
                                   let uu____8513 =
                                     let uu____8515 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____8515
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____8513)
                                    in
                                 FStar_Errors.log_issue uu____8506 uu____8507)
                              else ())
                         else ())))
          else ()
      | uu____8525 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____8570 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____8598 ->
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
             let uu____8658 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____8658
             then
               let ses1 =
                 let uu____8666 =
                   let uu____8667 =
                     let uu____8668 =
                       tc_inductive
                         (let uu___397_8677 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___397_8677.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___397_8677.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___397_8677.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___397_8677.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___397_8677.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___397_8677.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___397_8677.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___397_8677.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___397_8677.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___397_8677.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___397_8677.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___397_8677.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___397_8677.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___397_8677.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___397_8677.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___397_8677.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___397_8677.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___397_8677.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___397_8677.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___397_8677.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___397_8677.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___397_8677.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___397_8677.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___397_8677.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___397_8677.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___397_8677.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___397_8677.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___397_8677.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___397_8677.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___397_8677.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___397_8677.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___397_8677.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___397_8677.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___397_8677.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___397_8677.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___397_8677.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___397_8677.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___397_8677.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___397_8677.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___397_8677.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___397_8677.FStar_TypeChecker_Env.nbe)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____8668
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____8667
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____8666
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____8691 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____8691
                 then
                   let uu____8696 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___398_8700 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___398_8700.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___398_8700.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___398_8700.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___398_8700.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____8696
                 else ());
                ses1)
             else ses  in
           let uu____8710 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____8710 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___399_8734 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___399_8734.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___399_8734.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___399_8734.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___399_8734.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           ((let uu____8747 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____8747
             then
               let uu____8751 =
                 FStar_Syntax_Print.term_to_string
                   (ne.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                  in
               let uu____8753 =
                 FStar_Syntax_Print.tag_of_term
                   (ne.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                  in
               FStar_Util.print2 "GG repr = %s (%s)\n" uu____8751 uu____8753
             else ());
            (let forfree =
               let uu____8760 =
                 let uu____8761 =
                   FStar_Syntax_Subst.compress
                     (ne.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                    in
                 uu____8761.FStar_Syntax_Syntax.n  in
               match uu____8760 with
               | FStar_Syntax_Syntax.Tm_unknown  -> false
               | uu____8766 ->
                   Prims.op_Negation ne.FStar_Syntax_Syntax.elaborated
                in
             if forfree
             then
               ((let uu____8779 =
                   FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                    in
                 if uu____8779
                 then FStar_Util.print_string "Beginning DM4F run\n"
                 else ());
                (let uu____8786 = cps_and_elaborate_ed env0 ne  in
                 match uu____8786 with
                 | (ses,ne1,lift_from_pure_opt) ->
                     let ne2 =
                       let uu___400_8819 = ne1  in
                       {
                         FStar_Syntax_Syntax.cattributes =
                           (uu___400_8819.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.mname =
                           (uu___400_8819.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.univs =
                           (uu___400_8819.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___400_8819.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.spec =
                           (uu___400_8819.FStar_Syntax_Syntax.spec);
                         FStar_Syntax_Syntax.signature =
                           (uu___400_8819.FStar_Syntax_Syntax.signature);
                         FStar_Syntax_Syntax.if_then_else =
                           (uu___400_8819.FStar_Syntax_Syntax.if_then_else);
                         FStar_Syntax_Syntax.ite_wp =
                           (uu___400_8819.FStar_Syntax_Syntax.ite_wp);
                         FStar_Syntax_Syntax.stronger =
                           (uu___400_8819.FStar_Syntax_Syntax.stronger);
                         FStar_Syntax_Syntax.close_wp =
                           (uu___400_8819.FStar_Syntax_Syntax.close_wp);
                         FStar_Syntax_Syntax.assert_p =
                           (uu___400_8819.FStar_Syntax_Syntax.assert_p);
                         FStar_Syntax_Syntax.assume_p =
                           (uu___400_8819.FStar_Syntax_Syntax.assume_p);
                         FStar_Syntax_Syntax.null_wp =
                           (uu___400_8819.FStar_Syntax_Syntax.null_wp);
                         FStar_Syntax_Syntax.trivial =
                           (uu___400_8819.FStar_Syntax_Syntax.trivial);
                         FStar_Syntax_Syntax.repr =
                           (uu___400_8819.FStar_Syntax_Syntax.repr);
                         FStar_Syntax_Syntax.elaborated = true;
                         FStar_Syntax_Syntax.actions =
                           (uu___400_8819.FStar_Syntax_Syntax.actions);
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___400_8819.FStar_Syntax_Syntax.eff_attrs)
                       }  in
                     let effect_and_lift_ses =
                       match lift_from_pure_opt with
                       | FStar_Pervasives_Native.Some lift ->
                           [(let uu___401_8828 = se  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_new_effect ne2);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___401_8828.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___401_8828.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___401_8828.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___401_8828.FStar_Syntax_Syntax.sigattrs)
                             });
                           lift]
                       | FStar_Pervasives_Native.None  ->
                           [(let uu___402_8830 = se  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_new_effect ne2);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___402_8830.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___402_8830.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___402_8830.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___402_8830.FStar_Syntax_Syntax.sigattrs)
                             })]
                        in
                     ([], (FStar_List.append ses effect_and_lift_ses), env0)))
             else
               (let ne1 =
                  let uu____8838 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env)
                     in
                  if uu____8838
                  then
                    let ne1 =
                      let uu____8842 =
                        let uu____8843 =
                          let uu____8844 =
                            tc_eff_decl
                              (let uu___403_8846 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___403_8846.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___403_8846.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___403_8846.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___403_8846.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___403_8846.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___403_8846.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___403_8846.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___403_8846.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___403_8846.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___403_8846.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___403_8846.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___403_8846.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___403_8846.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___403_8846.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___403_8846.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___403_8846.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___403_8846.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___403_8846.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___403_8846.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___403_8846.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___403_8846.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 = true;
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___403_8846.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___403_8846.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___403_8846.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___403_8846.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___403_8846.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___403_8846.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___403_8846.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___403_8846.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___403_8846.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___403_8846.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___403_8846.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___403_8846.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___403_8846.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___403_8846.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___403_8846.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___403_8846.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___403_8846.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___403_8846.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___403_8846.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___403_8846.FStar_TypeChecker_Env.nbe)
                               }) se ne
                             in
                          FStar_All.pipe_right uu____8844
                            (fun ne1  ->
                               let uu___404_8852 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___404_8852.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals =
                                   (uu___404_8852.FStar_Syntax_Syntax.sigquals);
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___404_8852.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___404_8852.FStar_Syntax_Syntax.sigattrs)
                               })
                           in
                        FStar_All.pipe_right uu____8843
                          (FStar_TypeChecker_Normalize.elim_uvars env)
                         in
                      FStar_All.pipe_right uu____8842
                        FStar_Syntax_Util.eff_decl_of_new_effect
                       in
                    ((let uu____8854 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "TwoPhases")
                         in
                      if uu____8854
                      then
                        let uu____8859 =
                          FStar_Syntax_Print.sigelt_to_string
                            (let uu___405_8863 = se  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___405_8863.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___405_8863.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___405_8863.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___405_8863.FStar_Syntax_Syntax.sigattrs)
                             })
                           in
                        FStar_Util.print1 "Effect decl after phase 1: %s\n"
                          uu____8859
                      else ());
                     ne1)
                  else ne  in
                let ne2 = tc_eff_decl env se ne1  in
                let se1 =
                  let uu___406_8871 = se  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_new_effect ne2);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___406_8871.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___406_8871.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___406_8871.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___406_8871.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([se1], [], env0))))
       | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
           let ed_src =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.source
              in
           let ed_tgt =
             FStar_TypeChecker_Env.get_effect_decl env
               sub1.FStar_Syntax_Syntax.target
              in
           let uu____8879 =
             let uu____8886 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____8886
              in
           (match uu____8879 with
            | (a,wp_a_src) ->
                let uu____8903 =
                  let uu____8910 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____8910
                   in
                (match uu____8903 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____8928 =
                         let uu____8931 =
                           let uu____8932 =
                             let uu____8939 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____8939)  in
                           FStar_Syntax_Syntax.NT uu____8932  in
                         [uu____8931]  in
                       FStar_Syntax_Subst.subst uu____8928 wp_b_tgt  in
                     let expected_k =
                       let uu____8947 =
                         let uu____8956 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____8963 =
                           let uu____8972 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____8972]  in
                         uu____8956 :: uu____8963  in
                       let uu____8997 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____8947 uu____8997  in
                     let repr_type eff_name a1 wp =
                       (let uu____9019 =
                          let uu____9021 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____9021  in
                        if uu____9019
                        then
                          let uu____9024 =
                            let uu____9030 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____9030)
                             in
                          let uu____9034 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____9024 uu____9034
                        else ());
                       (let uu____9037 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____9037 with
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
                            let uu____9074 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____9075 =
                              let uu____9082 =
                                let uu____9083 =
                                  let uu____9100 =
                                    let uu____9111 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____9120 =
                                      let uu____9131 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____9131]  in
                                    uu____9111 :: uu____9120  in
                                  (repr, uu____9100)  in
                                FStar_Syntax_Syntax.Tm_app uu____9083  in
                              FStar_Syntax_Syntax.mk uu____9082  in
                            uu____9075 FStar_Pervasives_Native.None
                              uu____9074)
                        in
                     let uu____9179 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____9352 =
                             if
                               (FStar_List.length uvs) >
                                 (Prims.parse_int "0")
                             then
                               let uu____9363 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____9363 with
                               | (usubst,uvs1) ->
                                   let uu____9386 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____9387 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____9386, uu____9387)
                             else (env, lift_wp)  in
                           (match uu____9352 with
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
                                     let uu____9437 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____9437))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____9508 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____9523 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____9523 with
                               | (usubst,uvs) ->
                                   let uu____9548 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____9548)
                             else ([], lift)  in
                           (match uu____9508 with
                            | (uvs,lift1) ->
                                ((let uu____9584 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____9584
                                  then
                                    let uu____9588 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____9588
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____9594 =
                                    let uu____9601 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____9601 lift1
                                     in
                                  match uu____9594 with
                                  | (lift2,comp,uu____9626) ->
                                      let uu____9627 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____9627 with
                                       | (uu____9656,lift_wp,lift_elab) ->
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
                                             let uu____9688 =
                                               let uu____9699 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____9699
                                                in
                                             let uu____9716 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____9688, uu____9716)
                                           else
                                             (let uu____9745 =
                                                let uu____9756 =
                                                  let uu____9765 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____9765)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____9756
                                                 in
                                              let uu____9780 =
                                                let uu____9789 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____9789)  in
                                              (uu____9745, uu____9780))))))
                        in
                     (match uu____9179 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___407_9863 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___407_9863.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___407_9863.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___407_9863.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___407_9863.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___407_9863.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___407_9863.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___407_9863.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___407_9863.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___407_9863.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___407_9863.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___407_9863.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___407_9863.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___407_9863.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___407_9863.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___407_9863.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___407_9863.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___407_9863.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___407_9863.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___407_9863.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___407_9863.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___407_9863.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___407_9863.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___407_9863.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___407_9863.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___407_9863.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___407_9863.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___407_9863.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___407_9863.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___407_9863.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___407_9863.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___407_9863.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___407_9863.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___407_9863.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___407_9863.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___407_9863.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___407_9863.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___407_9863.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___407_9863.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___407_9863.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___407_9863.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___407_9863.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___407_9863.FStar_TypeChecker_Env.nbe)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____9896 =
                                  let uu____9901 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____9901 with
                                  | (usubst,uvs1) ->
                                      let uu____9924 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____9925 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____9924, uu____9925)
                                   in
                                (match uu____9896 with
                                 | (env2,lift2) ->
                                     let uu____9930 =
                                       let uu____9937 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____9937
                                        in
                                     (match uu____9930 with
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
                                              let uu____9963 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____9964 =
                                                let uu____9971 =
                                                  let uu____9972 =
                                                    let uu____9989 =
                                                      let uu____10000 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____10009 =
                                                        let uu____10020 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____10020]  in
                                                      uu____10000 ::
                                                        uu____10009
                                                       in
                                                    (lift_wp1, uu____9989)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____9972
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____9971
                                                 in
                                              uu____9964
                                                FStar_Pervasives_Native.None
                                                uu____9963
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____10071 =
                                              let uu____10080 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____10087 =
                                                let uu____10096 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____10103 =
                                                  let uu____10112 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____10112]  in
                                                uu____10096 :: uu____10103
                                                 in
                                              uu____10080 :: uu____10087  in
                                            let uu____10143 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____10071 uu____10143
                                             in
                                          let uu____10146 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____10146 with
                                           | (expected_k2,uu____10156,uu____10157)
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
                                                    let uu____10165 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____10165))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____10173 =
                              let uu____10175 =
                                let uu____10177 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____10177
                                  FStar_List.length
                                 in
                              uu____10175 <> (Prims.parse_int "1")  in
                            if uu____10173
                            then
                              let uu____10199 =
                                let uu____10205 =
                                  let uu____10207 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10209 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10211 =
                                    let uu____10213 =
                                      let uu____10215 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10215
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10213
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10207 uu____10209 uu____10211
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10205)
                                 in
                              FStar_Errors.raise_error uu____10199 r
                            else ());
                           (let uu____10242 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____10245 =
                                   let uu____10247 =
                                     let uu____10250 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____10250
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____10247
                                     FStar_List.length
                                    in
                                 uu____10245 <> (Prims.parse_int "1"))
                               in
                            if uu____10242
                            then
                              let uu____10288 =
                                let uu____10294 =
                                  let uu____10296 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10298 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10300 =
                                    let uu____10302 =
                                      let uu____10304 =
                                        let uu____10307 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____10307
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10304
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10302
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10296 uu____10298 uu____10300
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10294)
                                 in
                              FStar_Errors.raise_error uu____10288 r
                            else ());
                           (let sub2 =
                              let uu___408_10350 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___408_10350.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___408_10350.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___409_10352 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___409_10352.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___409_10352.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___409_10352.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___409_10352.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let uu____10366 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (env, uvs, tps, c)
             else
               (let uu____10394 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____10394 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____10425 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____10425 c  in
                    let uu____10434 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____10434, uvs1, tps1, c1))
              in
           (match uu____10366 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____10456 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____10456 with
                 | (tps2,c2) ->
                     let uu____10473 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____10473 with
                      | (tps3,env3,us) ->
                          let uu____10493 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____10493 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____10521)::uu____10522 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____10541 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____10549 =
                                   let uu____10551 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____10551  in
                                 if uu____10549
                                 then
                                   let uu____10554 =
                                     let uu____10560 =
                                       let uu____10562 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____10564 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____10562 uu____10564
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____10560)
                                      in
                                   FStar_Errors.raise_error uu____10554 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____10572 =
                                   let uu____10573 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____10573
                                    in
                                 match uu____10572 with
                                 | (uvs2,t) ->
                                     let uu____10604 =
                                       let uu____10609 =
                                         let uu____10622 =
                                           let uu____10623 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10623.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____10622)  in
                                       match uu____10609 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____10638,c5)) -> ([], c5)
                                       | (uu____10680,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____10719 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____10604 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____10753 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____10753 with
                                              | (uu____10758,t1) ->
                                                  let uu____10760 =
                                                    let uu____10766 =
                                                      let uu____10768 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____10770 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____10774 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____10768
                                                        uu____10770
                                                        uu____10774
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____10766)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____10760 r)
                                           else ();
                                           (let se1 =
                                              let uu___410_10781 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags1));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___410_10781.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___410_10781.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___410_10781.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___410_10781.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____10788,uu____10789,uu____10790) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___375_10795  ->
                   match uu___375_10795 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____10798 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____10804,uu____10805) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___375_10814  ->
                   match uu___375_10814 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____10817 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____10828 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____10828
             then
               let uu____10831 =
                 let uu____10837 =
                   let uu____10839 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____10839
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____10837)
                  in
               FStar_Errors.raise_error uu____10831 r
             else ());
            (let uu____10845 =
               let uu____10854 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____10854
               then
                 let uu____10865 =
                   tc_declare_typ
                     (let uu___411_10868 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___411_10868.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___411_10868.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___411_10868.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___411_10868.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___411_10868.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___411_10868.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___411_10868.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___411_10868.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___411_10868.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___411_10868.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___411_10868.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___411_10868.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___411_10868.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___411_10868.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___411_10868.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___411_10868.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___411_10868.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___411_10868.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___411_10868.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___411_10868.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___411_10868.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___411_10868.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___411_10868.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___411_10868.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___411_10868.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___411_10868.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___411_10868.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___411_10868.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___411_10868.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___411_10868.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___411_10868.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___411_10868.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___411_10868.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___411_10868.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___411_10868.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___411_10868.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___411_10868.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___411_10868.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___411_10868.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___411_10868.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___411_10868.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___411_10868.FStar_TypeChecker_Env.nbe)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____10865 with
                 | (uvs1,t1) ->
                     ((let uu____10893 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____10893
                       then
                         let uu____10898 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____10900 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____10898 uu____10900
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____10845 with
             | (uvs1,t1) ->
                 let uu____10935 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____10935 with
                  | (uvs2,t2) ->
                      ([(let uu___412_10965 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___412_10965.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___412_10965.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___412_10965.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___412_10965.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____10970 =
             let uu____10979 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____10979
             then
               let uu____10990 =
                 tc_assume
                   (let uu___413_10993 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___413_10993.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___413_10993.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___413_10993.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___413_10993.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___413_10993.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___413_10993.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___413_10993.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___413_10993.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___413_10993.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___413_10993.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___413_10993.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___413_10993.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___413_10993.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___413_10993.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___413_10993.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___413_10993.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___413_10993.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___413_10993.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___413_10993.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___413_10993.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___413_10993.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___413_10993.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___413_10993.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___413_10993.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___413_10993.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___413_10993.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___413_10993.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___413_10993.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___413_10993.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___413_10993.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___413_10993.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___413_10993.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___413_10993.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___413_10993.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___413_10993.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___413_10993.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___413_10993.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___413_10993.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___413_10993.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___413_10993.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___413_10993.FStar_TypeChecker_Env.nbe)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____10990 with
               | (uvs1,t1) ->
                   ((let uu____11019 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____11019
                     then
                       let uu____11024 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____11026 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____11024
                         uu____11026
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____10970 with
            | (uvs1,t1) ->
                let uu____11061 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____11061 with
                 | (uvs2,t2) ->
                     ([(let uu___414_11091 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___414_11091.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___414_11091.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___414_11091.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___414_11091.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____11095 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____11095 with
            | (e1,c,g1) ->
                let uu____11115 =
                  let uu____11122 =
                    let uu____11125 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____11125  in
                  let uu____11126 =
                    let uu____11131 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____11131)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____11122 uu____11126
                   in
                (match uu____11115 with
                 | (e2,uu____11143,g) ->
                     ((let uu____11146 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____11146);
                      (let se1 =
                         let uu___415_11148 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___415_11148.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___415_11148.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___415_11148.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___415_11148.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____11160 = FStar_Options.debug_any ()  in
             if uu____11160
             then
               let uu____11163 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____11165 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____11163
                 uu____11165
             else ());
            (let uu____11170 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____11170 with
             | (t1,uu____11188,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____11202 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____11202 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____11205 =
                              let uu____11211 =
                                let uu____11213 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____11215 =
                                  let uu____11217 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____11217
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____11213 uu____11215
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____11211)
                               in
                            FStar_Errors.raise_error uu____11205 r
                        | uu____11229 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___416_11234 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___416_11234.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___416_11234.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___416_11234.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___416_11234.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___416_11234.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___416_11234.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___416_11234.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___416_11234.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___416_11234.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___416_11234.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___416_11234.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___416_11234.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___416_11234.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___416_11234.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___416_11234.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___416_11234.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___416_11234.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___416_11234.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___416_11234.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___416_11234.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___416_11234.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___416_11234.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___416_11234.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___416_11234.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___416_11234.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___416_11234.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___416_11234.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___416_11234.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___416_11234.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___416_11234.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___416_11234.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___416_11234.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___416_11234.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___416_11234.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___416_11234.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___416_11234.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___416_11234.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___416_11234.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___416_11234.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___416_11234.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___416_11234.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___416_11234.FStar_TypeChecker_Env.nbe)
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
                 let uu____11302 =
                   let uu____11304 =
                     let uu____11313 = drop_logic val_q  in
                     let uu____11316 = drop_logic q'  in
                     (uu____11313, uu____11316)  in
                   match uu____11304 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____11302
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____11343 =
                      let uu____11349 =
                        let uu____11351 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____11353 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____11355 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____11351 uu____11353 uu____11355
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____11349)
                       in
                    FStar_Errors.raise_error uu____11343 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____11392 =
                   let uu____11393 = FStar_Syntax_Subst.compress def  in
                   uu____11393.FStar_Syntax_Syntax.n  in
                 match uu____11392 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____11405,uu____11406) -> binders
                 | uu____11431 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____11443;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____11548) -> val_bs1
                     | (uu____11579,[]) -> val_bs1
                     | ((body_bv,uu____11611)::bt,(val_bv,aqual)::vt) ->
                         let uu____11668 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____11692) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___417_11706 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___418_11709 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___418_11709.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___417_11706.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___417_11706.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____11668
                      in
                   let uu____11716 =
                     let uu____11723 =
                       let uu____11724 =
                         let uu____11739 = rename_binders1 def_bs val_bs  in
                         (uu____11739, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____11724  in
                     FStar_Syntax_Syntax.mk uu____11723  in
                   uu____11716 FStar_Pervasives_Native.None r1
               | uu____11761 -> typ1  in
             let uu___419_11762 = lb  in
             let uu____11763 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___419_11762.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___419_11762.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____11763;
               FStar_Syntax_Syntax.lbeff =
                 (uu___419_11762.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___419_11762.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___419_11762.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___419_11762.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____11766 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____11821  ->
                     fun lb  ->
                       match uu____11821 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____11867 =
                             let uu____11879 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____11879 with
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
                                   | uu____11959 ->
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
                                  (let uu____12006 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____12006, quals_opt1)))
                              in
                           (match uu____11867 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____11766 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____12110 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___376_12116  ->
                                match uu___376_12116 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____12121 -> false))
                         in
                      if uu____12110
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____12134 =
                    let uu____12141 =
                      let uu____12142 =
                        let uu____12156 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____12156)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____12142  in
                    FStar_Syntax_Syntax.mk uu____12141  in
                  uu____12134 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___420_12178 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___420_12178.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___420_12178.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___420_12178.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___420_12178.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___420_12178.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___420_12178.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___420_12178.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___420_12178.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___420_12178.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___420_12178.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___420_12178.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___420_12178.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___420_12178.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___420_12178.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___420_12178.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___420_12178.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___420_12178.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___420_12178.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___420_12178.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___420_12178.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___420_12178.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___420_12178.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___420_12178.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___420_12178.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___420_12178.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___420_12178.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___420_12178.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___420_12178.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___420_12178.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___420_12178.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___420_12178.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___420_12178.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___420_12178.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___420_12178.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___420_12178.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___420_12178.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___420_12178.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___420_12178.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___420_12178.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___420_12178.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___420_12178.FStar_TypeChecker_Env.nbe)
                  }  in
                let e1 =
                  let uu____12181 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____12181
                  then
                    let drop_lbtyp e_lax =
                      let uu____12190 =
                        let uu____12191 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____12191.FStar_Syntax_Syntax.n  in
                      match uu____12190 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____12213 =
                              let uu____12214 = FStar_Syntax_Subst.compress e
                                 in
                              uu____12214.FStar_Syntax_Syntax.n  in
                            match uu____12213 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____12218,lb1::[]),uu____12220) ->
                                let uu____12236 =
                                  let uu____12237 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____12237.FStar_Syntax_Syntax.n  in
                                (match uu____12236 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____12242 -> false)
                            | uu____12244 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___421_12248 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___422_12263 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___422_12263.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___422_12263.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___422_12263.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___422_12263.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___422_12263.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___422_12263.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___421_12248.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___421_12248.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____12266 -> e_lax  in
                    let e1 =
                      let uu____12268 =
                        let uu____12269 =
                          let uu____12270 =
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              (let uu___423_12279 = env'  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___423_12279.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___423_12279.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___423_12279.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___423_12279.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___423_12279.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___423_12279.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___423_12279.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___423_12279.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___423_12279.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___423_12279.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___423_12279.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___423_12279.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___423_12279.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___423_12279.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___423_12279.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___423_12279.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___423_12279.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___423_12279.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___423_12279.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___423_12279.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___423_12279.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 = true;
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___423_12279.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___423_12279.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___423_12279.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___423_12279.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___423_12279.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___423_12279.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___423_12279.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___423_12279.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___423_12279.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___423_12279.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___423_12279.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___423_12279.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___423_12279.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___423_12279.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___423_12279.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___423_12279.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___423_12279.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___423_12279.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___423_12279.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___423_12279.FStar_TypeChecker_Env.nbe)
                               }) e
                             in
                          FStar_All.pipe_right uu____12270
                            (fun uu____12292  ->
                               match uu____12292 with
                               | (e1,uu____12300,uu____12301) -> e1)
                           in
                        FStar_All.pipe_right uu____12269
                          (FStar_TypeChecker_Normalize.remove_uvar_solutions
                             env')
                         in
                      FStar_All.pipe_right uu____12268 drop_lbtyp  in
                    ((let uu____12303 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "TwoPhases")
                         in
                      if uu____12303
                      then
                        let uu____12308 =
                          FStar_Syntax_Print.term_to_string e1  in
                        FStar_Util.print1 "Let binding after phase 1: %s\n"
                          uu____12308
                      else ());
                     e1)
                  else e  in
                let uu____12315 =
                  let uu____12324 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____12324 with
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
                (match uu____12315 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___424_12429 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___424_12429.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___424_12429.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___424_12429.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___424_12429.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___425_12442 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___425_12442.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___425_12442.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___425_12442.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___425_12442.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___425_12442.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___425_12442.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____12443 =
                       let uu____12455 =
                         FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env'
                           e1
                          in
                       match uu____12455 with
                       | ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                            FStar_Syntax_Syntax.pos = uu____12475;
                            FStar_Syntax_Syntax.vars = uu____12476;_},uu____12477,g)
                           when FStar_TypeChecker_Env.is_trivial g ->
                           let lbs2 =
                             let uu____12507 =
                               FStar_All.pipe_right
                                 (FStar_Pervasives_Native.snd lbs1)
                                 (FStar_List.map rename_parameters)
                                in
                             ((FStar_Pervasives_Native.fst lbs1),
                               uu____12507)
                              in
                           let lbs3 =
                             let uu____12531 =
                               match post_tau with
                               | FStar_Pervasives_Native.Some tau ->
                                   FStar_List.map (postprocess_lb tau)
                                     (FStar_Pervasives_Native.snd lbs2)
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.snd lbs2
                                in
                             ((FStar_Pervasives_Native.fst lbs2),
                               uu____12531)
                              in
                           let quals1 =
                             match e2.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_meta
                                 (uu____12554,FStar_Syntax_Syntax.Meta_desugared
                                  (FStar_Syntax_Syntax.Masked_effect ))
                                 -> FStar_Syntax_Syntax.HasMaskedEffect ::
                                 quals
                             | uu____12559 -> quals  in
                           ((let uu___426_12568 = se1  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_let (lbs3, lids));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___426_12568.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals = quals1;
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___426_12568.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___426_12568.FStar_Syntax_Syntax.sigattrs)
                             }), lbs3)
                       | uu____12571 ->
                           failwith
                             "impossible (typechecking should preserve Tm_let)"
                        in
                     (match uu____12443 with
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
                           (let uu____12627 = log env1  in
                            if uu____12627
                            then
                              let uu____12630 =
                                let uu____12632 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs1)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let should_log =
                                            let uu____12652 =
                                              let uu____12661 =
                                                let uu____12662 =
                                                  let uu____12665 =
                                                    FStar_Util.right
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  uu____12665.FStar_Syntax_Syntax.fv_name
                                                   in
                                                uu____12662.FStar_Syntax_Syntax.v
                                                 in
                                              FStar_TypeChecker_Env.try_lookup_val_decl
                                                env1 uu____12661
                                               in
                                            match uu____12652 with
                                            | FStar_Pervasives_Native.None 
                                                -> true
                                            | uu____12674 -> false  in
                                          if should_log
                                          then
                                            let uu____12686 =
                                              FStar_Syntax_Print.lbname_to_string
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            let uu____12688 =
                                              FStar_Syntax_Print.term_to_string
                                                lb.FStar_Syntax_Syntax.lbtyp
                                               in
                                            FStar_Util.format2 "let %s : %s"
                                              uu____12686 uu____12688
                                          else ""))
                                   in
                                FStar_All.pipe_right uu____12632
                                  (FStar_String.concat "\n")
                                 in
                              FStar_Util.print1 "%s\n" uu____12630
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
      (let uu____12740 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____12740
       then
         let uu____12743 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____12743
       else ());
      (let uu____12748 = get_fail_se se  in
       match uu____12748 with
       | FStar_Pervasives_Native.Some (uu____12769,false ) when
           let uu____12786 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____12786 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___427_12812 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___427_12812.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___427_12812.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___427_12812.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___427_12812.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___427_12812.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___427_12812.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___427_12812.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___427_12812.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___427_12812.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___427_12812.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___427_12812.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___427_12812.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___427_12812.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___427_12812.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___427_12812.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___427_12812.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___427_12812.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___427_12812.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___427_12812.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___427_12812.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___427_12812.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___427_12812.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___427_12812.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___427_12812.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___427_12812.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___427_12812.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___427_12812.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___427_12812.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___427_12812.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___427_12812.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___427_12812.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___427_12812.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___427_12812.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___427_12812.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___427_12812.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___427_12812.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___427_12812.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___427_12812.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___427_12812.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___427_12812.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___427_12812.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___427_12812.FStar_TypeChecker_Env.nbe)
               }
             else env1  in
           ((let uu____12817 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____12817
             then
               let uu____12820 =
                 let uu____12822 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____12822
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____12820
             else ());
            (let uu____12836 =
               FStar_Errors.catch_errors
                 (fun uu____12866  ->
                    FStar_Options.with_saved_options
                      (fun uu____12878  -> tc_decl' env' se))
                in
             match uu____12836 with
             | (errs,uu____12890) ->
                 ((let uu____12920 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____12920
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____12955 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____12955  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____12967 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____12978 =
                            let uu____12988 =
                              check_multi_contained errnos1 actual  in
                            match uu____12988 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")))
                             in
                          (match uu____12978 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____13053 =
                                   let uu____13059 =
                                     let uu____13061 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____13064 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____13067 =
                                       FStar_Util.string_of_int e  in
                                     let uu____13069 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____13071 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____13061 uu____13064 uu____13067
                                       uu____13069 uu____13071
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____13059)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____13053)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____13098 .
    'Auu____13098 ->
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
               (fun uu___377_13141  ->
                  match uu___377_13141 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____13144 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____13155) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____13163 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____13173 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____13178 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____13194 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____13220 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13246) ->
            let uu____13255 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13255
            then
              let for_export_bundle se1 uu____13292 =
                match uu____13292 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____13331,uu____13332) ->
                         let dec =
                           let uu___428_13342 = se1  in
                           let uu____13343 =
                             let uu____13344 =
                               let uu____13351 =
                                 let uu____13352 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____13352  in
                               (l, us, uu____13351)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____13344
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____13343;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___428_13342.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___428_13342.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___428_13342.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____13362,uu____13363,uu____13364) ->
                         let dec =
                           let uu___429_13372 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___429_13372.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___429_13372.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___429_13372.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____13377 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____13400,uu____13401,uu____13402) ->
            let uu____13403 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13403 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____13427 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____13427
            then
              ([(let uu___430_13446 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___430_13446.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___430_13446.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___430_13446.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____13449 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___378_13455  ->
                         match uu___378_13455 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____13458 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____13464 ->
                             true
                         | uu____13466 -> false))
                  in
               if uu____13449 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____13487 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____13492 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____13497 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13502 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13520) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____13534 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____13534
            then ([], hidden)
            else
              (let dec =
                 let uu____13555 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____13555;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____13566 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13566
            then
              let uu____13577 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___431_13591 = se  in
                        let uu____13592 =
                          let uu____13593 =
                            let uu____13600 =
                              let uu____13601 =
                                let uu____13604 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____13604.FStar_Syntax_Syntax.fv_name  in
                              uu____13601.FStar_Syntax_Syntax.v  in
                            (uu____13600, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____13593  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____13592;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___431_13591.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___431_13591.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___431_13591.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____13577, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____13627 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____13627
       then
         let uu____13630 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____13630
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____13635 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____13653 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____13670) -> z3_reset_options env
       | FStar_Syntax_Syntax.Sig_pragma uu____13674 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____13684 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____13684) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____13685,uu____13686,uu____13687) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_13692  ->
                   match uu___379_13692 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13695 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____13697,uu____13698) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_13707  ->
                   match uu___379_13707 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13710 -> false))
           -> env
       | uu____13712 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____13781 se =
        match uu____13781 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____13834 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____13834
              then
                let uu____13837 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____13837
              else ());
             (let uu____13842 = tc_decl env1 se  in
              match uu____13842 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____13895 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____13895
                             then
                               let uu____13899 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____13899
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____13915 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____13915
                             then
                               let uu____13919 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____13919
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
                    (let uu____13936 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____13936
                     then
                       let uu____13941 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____13950 =
                                  let uu____13952 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____13952 "\n"  in
                                Prims.strcat s uu____13950) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____13941
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____13962 =
                       let uu____13971 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____13971
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____14013 se1 =
                            match uu____14013 with
                            | (exports1,hidden1) ->
                                let uu____14041 = for_export env3 hidden1 se1
                                   in
                                (match uu____14041 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____13962 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____14195 = acc  in
        match uu____14195 with
        | (uu____14230,uu____14231,env1,uu____14233) ->
            let uu____14246 =
              FStar_Util.record_time
                (fun uu____14293  -> process_one_decl acc se)
               in
            (match uu____14246 with
             | (r,ms_elapsed) ->
                 ((let uu____14359 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____14359
                   then
                     let uu____14363 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____14365 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____14363 uu____14365
                   else ());
                  r))
         in
      let uu____14370 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____14370 with
      | (ses1,exports,env1,uu____14418) ->
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
          let uu___432_14456 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___432_14456.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___432_14456.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___432_14456.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___432_14456.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___432_14456.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___432_14456.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___432_14456.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___432_14456.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___432_14456.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___432_14456.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___432_14456.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___432_14456.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___432_14456.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___432_14456.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___432_14456.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___432_14456.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___432_14456.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___432_14456.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___432_14456.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___432_14456.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___432_14456.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___432_14456.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___432_14456.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___432_14456.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___432_14456.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___432_14456.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___432_14456.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___432_14456.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___432_14456.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___432_14456.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___432_14456.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___432_14456.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___432_14456.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___432_14456.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___432_14456.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___432_14456.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___432_14456.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___432_14456.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___432_14456.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___432_14456.FStar_TypeChecker_Env.nbe)
          }  in
        let check_term lid univs1 t =
          let uu____14476 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____14476 with
          | (univs2,t1) ->
              ((let uu____14484 =
                  let uu____14486 =
                    let uu____14492 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____14492  in
                  FStar_All.pipe_left uu____14486
                    (FStar_Options.Other "Exports")
                   in
                if uu____14484
                then
                  let uu____14496 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____14498 =
                    let uu____14500 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____14500
                      (FStar_String.concat ", ")
                     in
                  let uu____14517 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____14496 uu____14498 uu____14517
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____14523 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____14523 (fun a2  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____14549 =
             let uu____14551 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____14553 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____14551 uu____14553
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____14549);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14564) ->
              let uu____14573 =
                let uu____14575 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14575  in
              if uu____14573
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____14589,uu____14590) ->
              let t =
                let uu____14602 =
                  let uu____14609 =
                    let uu____14610 =
                      let uu____14625 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____14625)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____14610  in
                  FStar_Syntax_Syntax.mk uu____14609  in
                uu____14602 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____14644,uu____14645,uu____14646) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____14656 =
                let uu____14658 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14658  in
              if uu____14656 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____14666,lbs),uu____14668) ->
              let uu____14679 =
                let uu____14681 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14681  in
              if uu____14679
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
              let uu____14704 =
                let uu____14706 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14706  in
              if uu____14704
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____14727 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____14728 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14735 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____14736 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____14737 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____14744 -> ()  in
        let uu____14745 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____14745 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____14851) -> true
             | uu____14853 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____14883 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____14922 ->
                   let uu____14923 =
                     let uu____14930 =
                       let uu____14931 =
                         let uu____14946 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____14946)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____14931  in
                     FStar_Syntax_Syntax.mk uu____14930  in
                   uu____14923 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____14966,uu____14967) ->
            let s1 =
              let uu___433_14977 = s  in
              let uu____14978 =
                let uu____14979 =
                  let uu____14986 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____14986)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____14979  in
              let uu____14987 =
                let uu____14990 =
                  let uu____14993 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____14993  in
                FStar_Syntax_Syntax.Assumption :: uu____14990  in
              {
                FStar_Syntax_Syntax.sigel = uu____14978;
                FStar_Syntax_Syntax.sigrng =
                  (uu___433_14977.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____14987;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___433_14977.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___433_14977.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____14996 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____15021 lbdef =
        match uu____15021 with
        | (uvs,t) ->
            let attrs =
              let uu____15032 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____15032
              then
                let uu____15037 =
                  let uu____15038 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____15038
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____15037 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___434_15041 = s  in
            let uu____15042 =
              let uu____15045 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____15045  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___434_15041.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____15042;
              FStar_Syntax_Syntax.sigmeta =
                (uu___434_15041.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____15063 -> failwith "Impossible!"  in
        let c_opt =
          let uu____15070 = FStar_Syntax_Util.is_unit t  in
          if uu____15070
          then
            let uu____15077 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____15077
          else
            (let uu____15084 =
               let uu____15085 = FStar_Syntax_Subst.compress t  in
               uu____15085.FStar_Syntax_Syntax.n  in
             match uu____15084 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____15092,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____15116 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____15128 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____15128
            then false
            else
              (let uu____15135 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____15135
               then true
               else
                 (let uu____15142 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____15142))
         in
      let extract_sigelt s =
        (let uu____15154 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____15154
         then
           let uu____15157 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____15157
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____15164 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____15184 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____15203 ->
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
                             (lid,uu____15249,uu____15250,uu____15251,uu____15252,uu____15253)
                             ->
                             ((let uu____15263 =
                                 let uu____15266 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____15266  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____15263);
                              (let uu____15359 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____15359 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____15363,uu____15364,uu____15365,uu____15366,uu____15367)
                             ->
                             ((let uu____15375 =
                                 let uu____15378 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____15378  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____15375);
                              sigelts1)
                         | uu____15471 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____15480 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15480
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____15490 =
                    let uu___435_15491 = s  in
                    let uu____15492 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___435_15491.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___435_15491.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15492;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___435_15491.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___435_15491.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15490])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____15503 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15503
             then []
             else
               (let uu____15510 = lbs  in
                match uu____15510 with
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
                        (fun uu____15572  ->
                           match uu____15572 with
                           | (uu____15580,t,uu____15582) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____15599  ->
                             match uu____15599 with
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
                           (fun uu____15626  ->
                              match uu____15626 with
                              | (uu____15634,t,uu____15636) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____15648,uu____15649) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____15657 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____15708 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____15708) uu____15657
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____15712 =
                    let uu___436_15713 = s  in
                    let uu____15714 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___436_15713.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___436_15713.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15714;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___436_15713.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___436_15713.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15712]
                else [])
             else
               (let uu____15721 =
                  let uu___437_15722 = s  in
                  let uu____15723 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___437_15722.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___437_15722.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____15723;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___437_15722.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___437_15722.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____15721])
         | FStar_Syntax_Syntax.Sig_new_effect uu____15726 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____15727 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15728 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____15741 -> [s])
         in
      let uu___438_15742 = m  in
      let uu____15743 =
        let uu____15744 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____15744 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___438_15742.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____15743;
        FStar_Syntax_Syntax.exports =
          (uu___438_15742.FStar_Syntax_Syntax.exports);
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
        (fun uu____15795  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____15843  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             solver.FStar_TypeChecker_Env.refresh (); env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____15859 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____15859
  
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
      (let uu____15948 = FStar_Options.debug_any ()  in
       if uu____15948
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
         let uu___439_15964 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___439_15964.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___439_15964.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___439_15964.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___439_15964.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___439_15964.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___439_15964.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___439_15964.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___439_15964.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___439_15964.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___439_15964.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___439_15964.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___439_15964.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___439_15964.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___439_15964.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___439_15964.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___439_15964.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___439_15964.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___439_15964.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___439_15964.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___439_15964.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___439_15964.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___439_15964.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___439_15964.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___439_15964.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___439_15964.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___439_15964.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___439_15964.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___439_15964.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___439_15964.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___439_15964.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___439_15964.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___439_15964.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___439_15964.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___439_15964.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___439_15964.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___439_15964.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___439_15964.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___439_15964.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___439_15964.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___439_15964.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___439_15964.FStar_TypeChecker_Env.nbe)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____15966 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____15966 with
       | (ses,exports,env3) ->
           ((let uu___440_15999 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___440_15999.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___440_15999.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___440_15999.FStar_Syntax_Syntax.is_interface)
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
        let uu____16028 = tc_decls env decls  in
        match uu____16028 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___441_16059 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___441_16059.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___441_16059.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___441_16059.FStar_Syntax_Syntax.is_interface)
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
        let uu____16120 = tc_partial_modul env01 m  in
        match uu____16120 with
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
                (let uu____16157 = FStar_Errors.get_err_count ()  in
                 uu____16157 = (Prims.parse_int "0"))
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____16168 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____16168
                then
                  let uu____16172 =
                    let uu____16174 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16174 then "" else " (in lax mode) "  in
                  let uu____16182 =
                    let uu____16184 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16184
                    then
                      let uu____16188 =
                        let uu____16190 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.strcat uu____16190 "\n"  in
                      Prims.strcat "\nfrom: " uu____16188
                    else ""  in
                  let uu____16197 =
                    let uu____16199 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16199
                    then
                      let uu____16203 =
                        let uu____16205 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.strcat uu____16205 "\n"  in
                      Prims.strcat "\nto: " uu____16203
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____16172
                    uu____16182 uu____16197
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.strcat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___442_16219 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___442_16219.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___442_16219.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___442_16219.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___442_16219.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___442_16219.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___442_16219.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___442_16219.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___442_16219.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___442_16219.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___442_16219.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___442_16219.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___442_16219.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___442_16219.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___442_16219.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___442_16219.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___442_16219.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___442_16219.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___442_16219.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___442_16219.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___442_16219.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___442_16219.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___442_16219.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___442_16219.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___442_16219.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___442_16219.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___442_16219.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___442_16219.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___442_16219.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___442_16219.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___442_16219.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___442_16219.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___442_16219.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___442_16219.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___442_16219.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___442_16219.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___442_16219.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___442_16219.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___442_16219.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___442_16219.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___442_16219.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___442_16219.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___442_16219.FStar_TypeChecker_Env.nbe)
                    }  in
                  let en02 =
                    let uu___443_16221 = en01  in
                    let uu____16222 =
                      let uu____16237 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____16237, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___443_16221.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___443_16221.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___443_16221.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___443_16221.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___443_16221.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___443_16221.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___443_16221.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___443_16221.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___443_16221.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___443_16221.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___443_16221.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___443_16221.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___443_16221.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___443_16221.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___443_16221.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___443_16221.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___443_16221.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___443_16221.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___443_16221.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___443_16221.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___443_16221.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___443_16221.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___443_16221.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___443_16221.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___443_16221.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___443_16221.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___443_16221.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___443_16221.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___443_16221.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___443_16221.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___443_16221.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____16222;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___443_16221.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___443_16221.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___443_16221.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___443_16221.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___443_16221.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___443_16221.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___443_16221.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___443_16221.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___443_16221.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___443_16221.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___443_16221.FStar_TypeChecker_Env.nbe)
                    }  in
                  let uu____16283 =
                    let uu____16285 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____16285  in
                  if uu____16283
                  then
                    ((let uu____16289 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____16289 (fun a3  -> ()));
                     z3_reset_options en02)
                  else en02  in
                let uu____16293 = tc_modul en0 modul_iface true  in
                match uu____16293 with
                | (modul_iface1,env) ->
                    ((let uu___444_16306 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___444_16306.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___444_16306.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___444_16306.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___445_16310 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___445_16310.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___445_16310.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___445_16310.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____16313 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____16313 FStar_Util.smap_clear);
               (let uu____16349 =
                  ((let uu____16353 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____16353) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____16356 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____16356)
                   in
                if uu____16349 then check_exports env modul exports else ());
               (let uu____16362 =
                  pop_context env
                    (Prims.strcat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____16362 (fun a4  -> ()));
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
                 env modul;
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ();
               (let uu____16367 =
                  let uu____16369 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____16369  in
                if uu____16367
                then
                  let uu____16372 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____16372 (fun a5  -> ())
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
        let uu____16389 =
          let uu____16391 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____16391  in
        push_context env uu____16389  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____16412 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____16423 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____16423 with | (uu____16430,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____16455 = FStar_Options.debug_any ()  in
         if uu____16455
         then
           let uu____16458 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____16458
         else ());
        (let uu____16470 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____16470
         then
           let uu____16473 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____16473
         else ());
        (let env1 =
           let uu___446_16479 = env  in
           let uu____16480 =
             let uu____16482 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____16482  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___446_16479.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___446_16479.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___446_16479.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___446_16479.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___446_16479.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___446_16479.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___446_16479.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___446_16479.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___446_16479.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___446_16479.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___446_16479.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___446_16479.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___446_16479.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___446_16479.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___446_16479.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___446_16479.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___446_16479.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___446_16479.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___446_16479.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___446_16479.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____16480;
             FStar_TypeChecker_Env.lax_universes =
               (uu___446_16479.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___446_16479.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___446_16479.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___446_16479.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___446_16479.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___446_16479.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___446_16479.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___446_16479.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___446_16479.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___446_16479.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___446_16479.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___446_16479.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___446_16479.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___446_16479.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___446_16479.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___446_16479.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___446_16479.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___446_16479.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___446_16479.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___446_16479.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___446_16479.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___446_16479.FStar_TypeChecker_Env.nbe)
           }  in
         let uu____16484 = tc_modul env1 m b  in
         match uu____16484 with
         | (m1,env2) ->
             ((let uu____16496 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____16496
               then
                 let uu____16499 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____16499
               else ());
              (let uu____16505 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____16505
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
                         let uu____16543 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____16543 with
                         | (univnames1,e) ->
                             let uu___447_16550 = lb  in
                             let uu____16551 =
                               let uu____16554 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____16554 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___447_16550.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___447_16550.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___447_16550.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___447_16550.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16551;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___447_16550.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___447_16550.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___448_16555 = se  in
                       let uu____16556 =
                         let uu____16557 =
                           let uu____16564 =
                             let uu____16565 = FStar_List.map update lbs  in
                             (b1, uu____16565)  in
                           (uu____16564, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____16557  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____16556;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___448_16555.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___448_16555.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___448_16555.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___448_16555.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____16573 -> se  in
                 let normalized_module =
                   let uu___449_16575 = m1  in
                   let uu____16576 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___449_16575.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____16576;
                     FStar_Syntax_Syntax.exports =
                       (uu___449_16575.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___449_16575.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____16577 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____16577
               else ());
              (m1, env2)))
  
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
                                let is_unk t =
                                  let uu____924 =
                                    let uu____925 =
                                      FStar_Syntax_Subst.compress t  in
                                    uu____925.FStar_Syntax_Syntax.n  in
                                  match uu____924 with
                                  | FStar_Syntax_Syntax.Tm_unknown  -> true
                                  | uu____930 -> false  in
                                let uu____932 =
                                  let uu____937 =
                                    is_unk
                                      (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m
                                     in
                                  if uu____937
                                  then
                                    let uu____944 =
                                      FStar_TypeChecker_DMFF.star_type
                                        dmff_env repr
                                       in
                                    ((let uu___383_946 = ed  in
                                      {
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___383_946.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___383_946.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___383_946.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___383_946.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.spec =
                                          (uu___383_946.FStar_Syntax_Syntax.spec);
                                        FStar_Syntax_Syntax.signature =
                                          (uu___383_946.FStar_Syntax_Syntax.signature);
                                        FStar_Syntax_Syntax.if_then_else =
                                          (uu___383_946.FStar_Syntax_Syntax.if_then_else);
                                        FStar_Syntax_Syntax.ite_wp =
                                          (uu___383_946.FStar_Syntax_Syntax.ite_wp);
                                        FStar_Syntax_Syntax.stronger =
                                          (uu___383_946.FStar_Syntax_Syntax.stronger);
                                        FStar_Syntax_Syntax.close_wp =
                                          (uu___383_946.FStar_Syntax_Syntax.close_wp);
                                        FStar_Syntax_Syntax.assert_p =
                                          (uu___383_946.FStar_Syntax_Syntax.assert_p);
                                        FStar_Syntax_Syntax.assume_p =
                                          (uu___383_946.FStar_Syntax_Syntax.assume_p);
                                        FStar_Syntax_Syntax.null_wp =
                                          (uu___383_946.FStar_Syntax_Syntax.null_wp);
                                        FStar_Syntax_Syntax.trivial =
                                          (uu___383_946.FStar_Syntax_Syntax.trivial);
                                        FStar_Syntax_Syntax.repr =
                                          (uu___383_946.FStar_Syntax_Syntax.repr);
                                        FStar_Syntax_Syntax.elaborated =
                                          (uu___383_946.FStar_Syntax_Syntax.elaborated);
                                        FStar_Syntax_Syntax.spec_dm4f = true;
                                        FStar_Syntax_Syntax.interp =
                                          (uu___383_946.FStar_Syntax_Syntax.interp);
                                        FStar_Syntax_Syntax.actions =
                                          (uu___383_946.FStar_Syntax_Syntax.actions);
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___383_946.FStar_Syntax_Syntax.eff_attrs)
                                      }), uu____944)
                                  else
                                    (ed,
                                      ((ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m))
                                   in
                                match uu____932 with
                                | (ed1,wp_type) ->
                                    let wp_type1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.UnfoldUntil
                                           FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.AllowUnboundUniverses]
                                        env1 wp_type
                                       in
                                    let uu____963 =
                                      recheck_debug "*" env1 wp_type1  in
                                    let wp_a =
                                      let uu____966 =
                                        let uu____967 =
                                          let uu____968 =
                                            let uu____985 =
                                              let uu____996 =
                                                let uu____1005 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a1
                                                   in
                                                let uu____1008 =
                                                  FStar_Syntax_Syntax.as_implicit
                                                    false
                                                   in
                                                (uu____1005, uu____1008)  in
                                              [uu____996]  in
                                            (wp_type1, uu____985)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____968
                                           in
                                        mk1 uu____967  in
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Beta] env1
                                        uu____966
                                       in
                                    let effect_signature =
                                      let binders =
                                        let uu____1056 =
                                          let uu____1063 =
                                            FStar_Syntax_Syntax.as_implicit
                                              false
                                             in
                                          (a1, uu____1063)  in
                                        let uu____1069 =
                                          let uu____1078 =
                                            let uu____1085 =
                                              FStar_Syntax_Syntax.gen_bv
                                                "dijkstra_wp"
                                                FStar_Pervasives_Native.None
                                                wp_a
                                               in
                                            FStar_All.pipe_right uu____1085
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          [uu____1078]  in
                                        uu____1056 :: uu____1069  in
                                      let binders1 =
                                        FStar_Syntax_Subst.close_binders
                                          binders
                                         in
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (binders1, effect_marker))
                                       in
                                    let uu____1122 =
                                      recheck_debug
                                        "turned into the effect signature"
                                        env1 effect_signature
                                       in
                                    let sigelts = FStar_Util.mk_ref []  in
                                    let mk_lid name =
                                      FStar_Syntax_Util.dm4f_lid ed1 name  in
                                    let uu____1139 =
                                      if ed1.FStar_Syntax_Syntax.spec_dm4f
                                      then
                                        let uu____1161 =
                                          elaborate_and_star dmff_env
                                            effect_binders1 []
                                            (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                           in
                                        match uu____1161 with
                                        | (dmff_env1,uu____1187,bind_wp,bind_elab)
                                            ->
                                            let bind_wp1 =
                                              let uu____1193 =
                                                is_unk
                                                  (FStar_Pervasives_Native.snd
                                                     (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind)
                                                 in
                                              if uu____1193
                                              then
                                                let uu____1202 =
                                                  let uu____1203 =
                                                    let uu____1210 =
                                                      FStar_Syntax_Syntax.tabbrev
                                                        FStar_Parser_Const.range_lid
                                                       in
                                                    FStar_Syntax_Syntax.null_binder
                                                      uu____1210
                                                     in
                                                  [uu____1203]  in
                                                FStar_Syntax_Util.abs
                                                  uu____1202 bind_wp
                                                  FStar_Pervasives_Native.None
                                              else
                                                FStar_Pervasives_Native.snd
                                                  (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                               in
                                            (dmff_env1, bind_wp1, bind_elab)
                                      else
                                        (dmff_env,
                                          (FStar_Pervasives_Native.snd
                                             (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind),
                                          (FStar_Pervasives_Native.snd
                                             (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind))
                                       in
                                    (match uu____1139 with
                                     | (dmff_env1,bind_wp,bind_elab) ->
                                         let uu____1268 =
                                           let uu____1279 =
                                             ed1.FStar_Syntax_Syntax.spec_dm4f
                                               &&
                                               (is_unk
                                                  (FStar_Pervasives_Native.snd
                                                     (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret))
                                              in
                                           if uu____1279
                                           then
                                             let uu____1296 =
                                               elaborate_and_star dmff_env1
                                                 effect_binders1 []
                                                 (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                                in
                                             match uu____1296 with
                                             | (dmff_env2,uu____1322,return_wp,return_elab)
                                                 ->
                                                 let return_wp1 =
                                                   let uu____1328 =
                                                     is_unk
                                                       (FStar_Pervasives_Native.snd
                                                          (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret)
                                                      in
                                                   if uu____1328
                                                   then return_wp
                                                   else
                                                     FStar_Pervasives_Native.snd
                                                       (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                                    in
                                                 (dmff_env2, return_wp1,
                                                   return_elab)
                                           else
                                             (dmff_env1,
                                               (FStar_Pervasives_Native.snd
                                                  (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret),
                                               (FStar_Pervasives_Native.snd
                                                  (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret))
                                            in
                                         (match uu____1268 with
                                          | (dmff_env2,return_wp,return_elab)
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
                                                let pure_wp_type t =
                                                  FStar_TypeChecker_DMFF.double_star
                                                    t
                                                   in
                                                let b1 =
                                                  let uu____1395 =
                                                    FStar_Syntax_Syntax.new_bv
                                                      FStar_Pervasives_Native.None
                                                      FStar_Syntax_Util.ktype
                                                     in
                                                  FStar_Syntax_Syntax.mk_binder
                                                    uu____1395
                                                   in
                                                let t_b1 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    (FStar_Pervasives_Native.fst
                                                       b1)
                                                   in
                                                let bwp =
                                                  let uu____1400 =
                                                    let uu____1401 =
                                                      pure_wp_type t_b1  in
                                                    FStar_Syntax_Syntax.new_bv
                                                      FStar_Pervasives_Native.None
                                                      uu____1401
                                                     in
                                                  FStar_Syntax_Syntax.mk_binder
                                                    uu____1400
                                                   in
                                                let t_wp =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    (FStar_Pervasives_Native.fst
                                                       bwp)
                                                   in
                                                let b2 =
                                                  let uu____1406 =
                                                    FStar_Syntax_Syntax.new_bv
                                                      FStar_Pervasives_Native.None
                                                      t_b1
                                                     in
                                                  FStar_Syntax_Syntax.mk_binder
                                                    uu____1406
                                                   in
                                                let t_b2 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    (FStar_Pervasives_Native.fst
                                                       b2)
                                                   in
                                                let t =
                                                  let uu____1411 =
                                                    let uu____1412 =
                                                      let uu____1423 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t_b1
                                                         in
                                                      [uu____1423]  in
                                                    FStar_Syntax_Util.mk_app
                                                      wp_type1 uu____1412
                                                     in
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 uu____1411
                                                   in
                                                let uu____1448 =
                                                  FStar_Syntax_Util.arrow_formals_comp
                                                    t
                                                   in
                                                match uu____1448 with
                                                | (bs,r) ->
                                                    let t00 =
                                                      let uu____1484 =
                                                        let uu____1495 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            t_b1
                                                           in
                                                        let uu____1502 =
                                                          let uu____1511 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              t_b2
                                                             in
                                                          let uu____1518 =
                                                            FStar_List.map
                                                              (fun uu____1543
                                                                  ->
                                                                 match uu____1543
                                                                 with
                                                                 | (bv,q) ->
                                                                    let uu____1562
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv  in
                                                                    (uu____1562,
                                                                    q)) bs
                                                             in
                                                          uu____1511 ::
                                                            uu____1518
                                                           in
                                                        uu____1495 ::
                                                          uu____1502
                                                         in
                                                      FStar_Syntax_Util.mk_app
                                                        return_wp uu____1484
                                                       in
                                                    let t0 =
                                                      FStar_Syntax_Util.abs
                                                        [b2] t00
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    let t1 =
                                                      let uu____1595 =
                                                        let uu____1598 =
                                                          let uu____1609 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              t0
                                                             in
                                                          [uu____1609]  in
                                                        FStar_Syntax_Util.mk_app
                                                          t_wp uu____1598
                                                         in
                                                      FStar_Syntax_Util.abs
                                                        bs uu____1595
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
                                                    ((let uu____1657 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          (FStar_Options.Other
                                                             "ED")
                                                         in
                                                      if uu____1657
                                                      then
                                                        let uu____1662 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t21
                                                           in
                                                        FStar_Util.print1
                                                          "elaborated lift from PURE = %s\n"
                                                          uu____1662
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
                                                  (let uu____1692 =
                                                     let uu____1693 =
                                                       let uu____1694 =
                                                         let uu____1711 =
                                                           let uu____1722 =
                                                             FStar_Syntax_Util.args_of_binders
                                                               effect_binders1
                                                              in
                                                           FStar_Pervasives_Native.snd
                                                             uu____1722
                                                            in
                                                         (t, uu____1711)  in
                                                       FStar_Syntax_Syntax.Tm_app
                                                         uu____1694
                                                        in
                                                     mk1 uu____1693  in
                                                   FStar_Syntax_Subst.close
                                                     effect_binders1
                                                     uu____1692)
                                                 in
                                              let register name item =
                                                let uu____1756 =
                                                  let uu____1761 =
                                                    mk_lid name  in
                                                  let uu____1762 =
                                                    FStar_Syntax_Util.abs
                                                      effect_binders1 item
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  FStar_TypeChecker_Util.mk_toplevel_definition
                                                    env1 uu____1761
                                                    uu____1762
                                                   in
                                                match uu____1756 with
                                                | (sigelt,fv) ->
                                                    ((let uu____1766 =
                                                        let uu____1769 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____1769
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____1766);
                                                     fv)
                                                 in
                                              let lift_from_pure_wp1 =
                                                register "lift_from_pure"
                                                  lift_from_pure_wp
                                                 in
                                              let return_wp1 =
                                                register "return_wp"
                                                  return_wp
                                                 in
                                              ((let uu____1867 =
                                                  let uu____1870 =
                                                    FStar_Syntax_Syntax.mk_sigelt
                                                      (FStar_Syntax_Syntax.Sig_pragma
                                                         (FStar_Syntax_Syntax.PushOptions
                                                            (FStar_Pervasives_Native.Some
                                                               "--admit_smt_queries true")))
                                                     in
                                                  let uu____1873 =
                                                    FStar_ST.op_Bang sigelts
                                                     in
                                                  uu____1870 :: uu____1873
                                                   in
                                                FStar_ST.op_Colon_Equals
                                                  sigelts uu____1867);
                                               (let return_elab1 =
                                                  register "return_elab"
                                                    return_elab
                                                   in
                                                (let uu____1969 =
                                                   let uu____1972 =
                                                     FStar_Syntax_Syntax.mk_sigelt
                                                       (FStar_Syntax_Syntax.Sig_pragma
                                                          FStar_Syntax_Syntax.PopOptions)
                                                      in
                                                   let uu____1973 =
                                                     FStar_ST.op_Bang sigelts
                                                      in
                                                   uu____1972 :: uu____1973
                                                    in
                                                 FStar_ST.op_Colon_Equals
                                                   sigelts uu____1969);
                                                (let bind_wp1 =
                                                   register "bind_wp" bind_wp
                                                    in
                                                 (let uu____2069 =
                                                    let uu____2072 =
                                                      FStar_Syntax_Syntax.mk_sigelt
                                                        (FStar_Syntax_Syntax.Sig_pragma
                                                           (FStar_Syntax_Syntax.PushOptions
                                                              (FStar_Pervasives_Native.Some
                                                                 "--admit_smt_queries true")))
                                                       in
                                                    let uu____2075 =
                                                      FStar_ST.op_Bang
                                                        sigelts
                                                       in
                                                    uu____2072 :: uu____2075
                                                     in
                                                  FStar_ST.op_Colon_Equals
                                                    sigelts uu____2069);
                                                 (let bind_elab1 =
                                                    register "bind_elab"
                                                      bind_elab
                                                     in
                                                  (let uu____2171 =
                                                     let uu____2174 =
                                                       FStar_Syntax_Syntax.mk_sigelt
                                                         (FStar_Syntax_Syntax.Sig_pragma
                                                            FStar_Syntax_Syntax.PopOptions)
                                                        in
                                                     let uu____2175 =
                                                       FStar_ST.op_Bang
                                                         sigelts
                                                        in
                                                     uu____2174 :: uu____2175
                                                      in
                                                   FStar_ST.op_Colon_Equals
                                                     sigelts uu____2171);
                                                  (let uu____2268 =
                                                     FStar_List.fold_left
                                                       (fun uu____2308  ->
                                                          fun action  ->
                                                            match uu____2308
                                                            with
                                                            | (dmff_env3,actions)
                                                                ->
                                                                let params_un
                                                                  =
                                                                  FStar_Syntax_Subst.open_binders
                                                                    action.FStar_Syntax_Syntax.action_params
                                                                   in
                                                                let uu____2329
                                                                  =
                                                                  let uu____2336
                                                                    =
                                                                    FStar_TypeChecker_DMFF.get_env
                                                                    dmff_env3
                                                                     in
                                                                  FStar_TypeChecker_TcTerm.tc_tparams
                                                                    uu____2336
                                                                    params_un
                                                                   in
                                                                (match uu____2329
                                                                 with
                                                                 | (action_params,env',uu____2345)
                                                                    ->
                                                                    let action_params1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____2371
                                                                     ->
                                                                    match uu____2371
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2390
                                                                    =
                                                                    let uu___384_2391
                                                                    = bv  in
                                                                    let uu____2392
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___384_2391.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___384_2391.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2392
                                                                    }  in
                                                                    (uu____2390,
                                                                    qual))
                                                                    action_params
                                                                     in
                                                                    let dmff_env'
                                                                    =
                                                                    FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'  in
                                                                    let uu____2398
                                                                    =
                                                                    elaborate_and_star
                                                                    dmff_env'
                                                                    effect_binders1
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                     in
                                                                    (match uu____2398
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
                                                                    uu____2441
                                                                    ->
                                                                    let uu____2442
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2442
                                                                     in
                                                                    ((
                                                                    let uu____2446
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____2446
                                                                    then
                                                                    let uu____2451
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____2454
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____2457
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____2459
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2451
                                                                    uu____2454
                                                                    uu____2457
                                                                    uu____2459
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
                                                                    let uu____2468
                                                                    =
                                                                    let uu____2471
                                                                    =
                                                                    let uu___385_2472
                                                                    = action
                                                                     in
                                                                    let uu____2473
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____2474
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___385_2472.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___385_2472.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___385_2472.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2473;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2474
                                                                    }  in
                                                                    uu____2471
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____2468))))))
                                                       (dmff_env2, [])
                                                       ed1.FStar_Syntax_Syntax.actions
                                                      in
                                                   match uu____2268 with
                                                   | (dmff_env3,actions) ->
                                                       let actions1 =
                                                         FStar_List.rev
                                                           actions
                                                          in
                                                       let repr1 =
                                                         if
                                                           Prims.op_Negation
                                                             ed1.FStar_Syntax_Syntax.spec_dm4f
                                                         then repr
                                                         else
                                                           (let wp =
                                                              FStar_Syntax_Syntax.gen_bv
                                                                "wp_a"
                                                                FStar_Pervasives_Native.None
                                                                wp_a
                                                               in
                                                            let binders =
                                                              let uu____2523
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  a1
                                                                 in
                                                              let uu____2530
                                                                =
                                                                let uu____2539
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp
                                                                   in
                                                                [uu____2539]
                                                                 in
                                                              uu____2523 ::
                                                                uu____2530
                                                               in
                                                            let r =
                                                              let uu____2567
                                                                =
                                                                let uu____2570
                                                                  =
                                                                  let uu____2571
                                                                    =
                                                                    let uu____2572
                                                                    =
                                                                    let uu____2589
                                                                    =
                                                                    let uu____2600
                                                                    =
                                                                    let uu____2609
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    a1  in
                                                                    let uu____2612
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____2609,
                                                                    uu____2612)
                                                                     in
                                                                    [uu____2600]
                                                                     in
                                                                    (repr,
                                                                    uu____2589)
                                                                     in
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    uu____2572
                                                                     in
                                                                  mk1
                                                                    uu____2571
                                                                   in
                                                                let uu____2648
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    wp
                                                                   in
                                                                FStar_TypeChecker_DMFF.trans_F
                                                                  dmff_env3
                                                                  uu____2570
                                                                  uu____2648
                                                                 in
                                                              FStar_Syntax_Util.abs
                                                                binders
                                                                uu____2567
                                                                FStar_Pervasives_Native.None
                                                               in
                                                            r)
                                                          in
                                                       let uu____2649 =
                                                         recheck_debug "FC"
                                                           env1 repr1
                                                          in
                                                       let repr2 =
                                                         register "repr"
                                                           repr1
                                                          in
                                                       let uu____2653 =
                                                         let uu____2662 =
                                                           let uu____2663 =
                                                             let uu____2666 =
                                                               FStar_Syntax_Subst.compress
                                                                 wp_type1
                                                                in
                                                             FStar_All.pipe_left
                                                               FStar_Syntax_Util.unascribe
                                                               uu____2666
                                                              in
                                                           uu____2663.FStar_Syntax_Syntax.n
                                                            in
                                                         match uu____2662
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_abs
                                                             (type_param::effect_param,arrow1,uu____2680)
                                                             ->
                                                             let uu____2717 =
                                                               let uu____2738
                                                                 =
                                                                 FStar_Syntax_Subst.open_term
                                                                   (type_param
                                                                   ::
                                                                   effect_param)
                                                                   arrow1
                                                                  in
                                                               match uu____2738
                                                               with
                                                               | (b::bs,body)
                                                                   ->
                                                                   (b, bs,
                                                                    body)
                                                               | uu____2806
                                                                   ->
                                                                   failwith
                                                                    "Impossible : open_term nt preserving binders arity"
                                                                in
                                                             (match uu____2717
                                                              with
                                                              | (type_param1,effect_param1,arrow2)
                                                                  ->
                                                                  let uu____2871
                                                                    =
                                                                    let uu____2872
                                                                    =
                                                                    let uu____2875
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____2875
                                                                     in
                                                                    uu____2872.FStar_Syntax_Syntax.n
                                                                     in
                                                                  (match uu____2871
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    let uu____2908
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                    (match uu____2908
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2923
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2954
                                                                     ->
                                                                    match uu____2954
                                                                    with
                                                                    | 
                                                                    (bv,uu____2963)
                                                                    ->
                                                                    let uu____2968
                                                                    =
                                                                    let uu____2970
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2970
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2968
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____2923
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
                                                                    let uu____3062
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____3062
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____3072
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____3083
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____3083
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____3093
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____3096
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____3093,
                                                                    uu____3096)))
                                                                   | 
                                                                   uu____3111
                                                                    ->
                                                                    let uu____3112
                                                                    =
                                                                    let uu____3118
                                                                    =
                                                                    let uu____3120
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____3120
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____3118)
                                                                     in
                                                                    raise_error1
                                                                    uu____3112))
                                                         | uu____3132 ->
                                                             let uu____3133 =
                                                               let uu____3139
                                                                 =
                                                                 let uu____3141
                                                                   =
                                                                   FStar_Syntax_Print.term_to_string
                                                                    wp_type1
                                                                    in
                                                                 FStar_Util.format1
                                                                   "Impossible: pre/post abs %s"
                                                                   uu____3141
                                                                  in
                                                               (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                 uu____3139)
                                                                in
                                                             raise_error1
                                                               uu____3133
                                                          in
                                                       (match uu____2653 with
                                                        | (pre,post) ->
                                                            ((let uu____3174
                                                                =
                                                                register
                                                                  "pre" pre
                                                                 in
                                                              ());
                                                             (let uu____3177
                                                                =
                                                                register
                                                                  "post" post
                                                                 in
                                                              ());
                                                             (let uu____3180
                                                                =
                                                                register "wp"
                                                                  wp_type1
                                                                 in
                                                              ());
                                                             (let ed2 =
                                                                let uu___386_3183
                                                                  = ed1  in
                                                                let uu____3184
                                                                  =
                                                                  FStar_Syntax_Subst.close_binders
                                                                    effect_binders1
                                                                   in
                                                                let uu____3185
                                                                  =
                                                                  let uu____3186
                                                                    =
                                                                    let uu____3187
                                                                    =
                                                                    apply_close
                                                                    return_wp1
                                                                     in
                                                                    ([],
                                                                    uu____3187)
                                                                     in
                                                                  let uu____3194
                                                                    =
                                                                    let uu____3195
                                                                    =
                                                                    apply_close
                                                                    bind_wp1
                                                                     in
                                                                    ([],
                                                                    uu____3195)
                                                                     in
                                                                  {
                                                                    FStar_Syntax_Syntax.monad_m
                                                                    =
                                                                    FStar_Syntax_Syntax.tun;
                                                                    FStar_Syntax_Syntax.monad_ret
                                                                    =
                                                                    uu____3186;
                                                                    FStar_Syntax_Syntax.monad_bind
                                                                    =
                                                                    uu____3194
                                                                  }  in
                                                                let uu____3202
                                                                  =
                                                                  FStar_Syntax_Subst.close
                                                                    effect_binders1
                                                                    effect_signature
                                                                   in
                                                                let uu____3203
                                                                  =
                                                                  let uu____3204
                                                                    =
                                                                    apply_close
                                                                    repr2  in
                                                                  let uu____3205
                                                                    =
                                                                    let uu____3206
                                                                    =
                                                                    apply_close
                                                                    return_elab1
                                                                     in
                                                                    ([],
                                                                    uu____3206)
                                                                     in
                                                                  let uu____3213
                                                                    =
                                                                    if
                                                                    ed1.FStar_Syntax_Syntax.spec_dm4f
                                                                    then
                                                                    let uu____3215
                                                                    =
                                                                    apply_close
                                                                    bind_elab1
                                                                     in
                                                                    ([],
                                                                    uu____3215)
                                                                    else
                                                                    (let uu____3224
                                                                    =
                                                                    let uu____3227
                                                                    =
                                                                    FStar_Ident.gen
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    [uu____3227]
                                                                     in
                                                                    let uu____3228
                                                                    =
                                                                    apply_close
                                                                    bind_elab1
                                                                     in
                                                                    (uu____3224,
                                                                    uu____3228))
                                                                     in
                                                                  {
                                                                    FStar_Syntax_Syntax.monad_m
                                                                    =
                                                                    uu____3204;
                                                                    FStar_Syntax_Syntax.monad_ret
                                                                    =
                                                                    uu____3205;
                                                                    FStar_Syntax_Syntax.monad_bind
                                                                    =
                                                                    uu____3213
                                                                  }  in
                                                                {
                                                                  FStar_Syntax_Syntax.cattributes
                                                                    =
                                                                    (
                                                                    uu___386_3183.FStar_Syntax_Syntax.cattributes);
                                                                  FStar_Syntax_Syntax.mname
                                                                    =
                                                                    (
                                                                    uu___386_3183.FStar_Syntax_Syntax.mname);
                                                                  FStar_Syntax_Syntax.univs
                                                                    =
                                                                    (
                                                                    uu___386_3183.FStar_Syntax_Syntax.univs);
                                                                  FStar_Syntax_Syntax.binders
                                                                    =
                                                                    uu____3184;
                                                                  FStar_Syntax_Syntax.spec
                                                                    =
                                                                    uu____3185;
                                                                  FStar_Syntax_Syntax.signature
                                                                    =
                                                                    uu____3202;
                                                                  FStar_Syntax_Syntax.if_then_else
                                                                    =
                                                                    (
                                                                    uu___386_3183.FStar_Syntax_Syntax.if_then_else);
                                                                  FStar_Syntax_Syntax.ite_wp
                                                                    =
                                                                    (
                                                                    uu___386_3183.FStar_Syntax_Syntax.ite_wp);
                                                                  FStar_Syntax_Syntax.stronger
                                                                    =
                                                                    (
                                                                    uu___386_3183.FStar_Syntax_Syntax.stronger);
                                                                  FStar_Syntax_Syntax.close_wp
                                                                    =
                                                                    (
                                                                    uu___386_3183.FStar_Syntax_Syntax.close_wp);
                                                                  FStar_Syntax_Syntax.assert_p
                                                                    =
                                                                    (
                                                                    uu___386_3183.FStar_Syntax_Syntax.assert_p);
                                                                  FStar_Syntax_Syntax.assume_p
                                                                    =
                                                                    (
                                                                    uu___386_3183.FStar_Syntax_Syntax.assume_p);
                                                                  FStar_Syntax_Syntax.null_wp
                                                                    =
                                                                    (
                                                                    uu___386_3183.FStar_Syntax_Syntax.null_wp);
                                                                  FStar_Syntax_Syntax.trivial
                                                                    =
                                                                    (
                                                                    uu___386_3183.FStar_Syntax_Syntax.trivial);
                                                                  FStar_Syntax_Syntax.repr
                                                                    =
                                                                    uu____3203;
                                                                  FStar_Syntax_Syntax.elaborated
                                                                    =
                                                                    (
                                                                    uu___386_3183.FStar_Syntax_Syntax.elaborated);
                                                                  FStar_Syntax_Syntax.spec_dm4f
                                                                    =
                                                                    (
                                                                    uu___386_3183.FStar_Syntax_Syntax.spec_dm4f);
                                                                  FStar_Syntax_Syntax.interp
                                                                    =
                                                                    (
                                                                    uu___386_3183.FStar_Syntax_Syntax.interp);
                                                                  FStar_Syntax_Syntax.actions
                                                                    =
                                                                    actions1;
                                                                  FStar_Syntax_Syntax.eff_attrs
                                                                    =
                                                                    (
                                                                    uu___386_3183.FStar_Syntax_Syntax.eff_attrs)
                                                                }  in
                                                              let uu____3235
                                                                =
                                                                FStar_TypeChecker_DMFF.gen_wps_for_free
                                                                  env1
                                                                  effect_binders1
                                                                  a1 wp_a ed2
                                                                 in
                                                              match uu____3235
                                                              with
                                                              | (sigelts',ed3)
                                                                  ->
                                                                  ((let uu____3253
                                                                    =
                                                                    FStar_TypeChecker_Env.debug
                                                                    env1
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____3253
                                                                    then
                                                                    let uu____3257
                                                                    =
                                                                    FStar_Syntax_Print.eff_decl_to_string
                                                                    ed3  in
                                                                    FStar_Util.print_string
                                                                    uu____3257
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
                                                                    let uu____3276
                                                                    =
                                                                    let uu____3279
                                                                    =
                                                                    let uu____3280
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____3280)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3279
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed3.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____3276;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                    let uu____3287
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3287
                                                                    else
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____3290
                                                                    =
                                                                    let uu____3293
                                                                    =
                                                                    let uu____3296
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                    FStar_List.rev
                                                                    uu____3296
                                                                     in
                                                                    FStar_List.append
                                                                    uu____3293
                                                                    sigelts'
                                                                     in
                                                                    (uu____3290,
                                                                    ed3,
                                                                    lift_from_pure_opt)))))))))))))))))))
  
let tc_eff_decl :
  'Auu____3357 .
    FStar_TypeChecker_Env.env ->
      'Auu____3357 ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun se  ->
      fun ed  ->
        (let uu____3374 =
           FStar_TypeChecker_Env.debug env0 (FStar_Options.Other "ED")  in
         if uu____3374
         then
           let uu____3378 = FStar_Syntax_Print.eff_decl_to_string ed  in
           FStar_Util.print1 "initial eff_decl :\n\t%s\n" uu____3378
         else ());
        (let uu____3383 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____3383 with
         | (open_annotated_univs,annotated_univ_names) ->
             let open_univs n_binders t =
               let uu____3415 =
                 FStar_Syntax_Subst.shift_subst n_binders
                   open_annotated_univs
                  in
               FStar_Syntax_Subst.subst uu____3415 t  in
             let open_univs_binders n_binders bs =
               let uu____3431 =
                 FStar_Syntax_Subst.shift_subst n_binders
                   open_annotated_univs
                  in
               FStar_Syntax_Subst.subst_binders uu____3431 bs  in
             let n_effect_params =
               FStar_List.length ed.FStar_Syntax_Syntax.binders  in
             let signature = ed.FStar_Syntax_Syntax.signature  in
             let uu____3442 =
               let uu____3449 =
                 open_univs_binders (Prims.parse_int "0")
                   ed.FStar_Syntax_Syntax.binders
                  in
               let uu____3451 = open_univs n_effect_params signature  in
               FStar_Syntax_Subst.open_term' uu____3449 uu____3451  in
             (match uu____3442 with
              | (effect_params_un,signature_un,opening) ->
                  let env =
                    FStar_TypeChecker_Env.push_univ_vars env0
                      annotated_univ_names
                     in
                  let uu____3462 =
                    FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un
                     in
                  (match uu____3462 with
                   | (effect_params,env1,uu____3471) ->
                       let uu____3472 =
                         FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                           signature_un
                          in
                       (match uu____3472 with
                        | (signature1,uu____3478) ->
                            let ed1 =
                              let uu___387_3480 = ed  in
                              {
                                FStar_Syntax_Syntax.cattributes =
                                  (uu___387_3480.FStar_Syntax_Syntax.cattributes);
                                FStar_Syntax_Syntax.mname =
                                  (uu___387_3480.FStar_Syntax_Syntax.mname);
                                FStar_Syntax_Syntax.univs =
                                  (uu___387_3480.FStar_Syntax_Syntax.univs);
                                FStar_Syntax_Syntax.binders = effect_params;
                                FStar_Syntax_Syntax.spec =
                                  (uu___387_3480.FStar_Syntax_Syntax.spec);
                                FStar_Syntax_Syntax.signature = signature1;
                                FStar_Syntax_Syntax.if_then_else =
                                  (uu___387_3480.FStar_Syntax_Syntax.if_then_else);
                                FStar_Syntax_Syntax.ite_wp =
                                  (uu___387_3480.FStar_Syntax_Syntax.ite_wp);
                                FStar_Syntax_Syntax.stronger =
                                  (uu___387_3480.FStar_Syntax_Syntax.stronger);
                                FStar_Syntax_Syntax.close_wp =
                                  (uu___387_3480.FStar_Syntax_Syntax.close_wp);
                                FStar_Syntax_Syntax.assert_p =
                                  (uu___387_3480.FStar_Syntax_Syntax.assert_p);
                                FStar_Syntax_Syntax.assume_p =
                                  (uu___387_3480.FStar_Syntax_Syntax.assume_p);
                                FStar_Syntax_Syntax.null_wp =
                                  (uu___387_3480.FStar_Syntax_Syntax.null_wp);
                                FStar_Syntax_Syntax.trivial =
                                  (uu___387_3480.FStar_Syntax_Syntax.trivial);
                                FStar_Syntax_Syntax.repr =
                                  (uu___387_3480.FStar_Syntax_Syntax.repr);
                                FStar_Syntax_Syntax.elaborated =
                                  (uu___387_3480.FStar_Syntax_Syntax.elaborated);
                                FStar_Syntax_Syntax.spec_dm4f =
                                  (uu___387_3480.FStar_Syntax_Syntax.spec_dm4f);
                                FStar_Syntax_Syntax.interp =
                                  (uu___387_3480.FStar_Syntax_Syntax.interp);
                                FStar_Syntax_Syntax.actions =
                                  (uu___387_3480.FStar_Syntax_Syntax.actions);
                                FStar_Syntax_Syntax.eff_attrs =
                                  (uu___387_3480.FStar_Syntax_Syntax.eff_attrs)
                              }  in
                            let ed2 =
                              match (effect_params, annotated_univ_names)
                              with
                              | ([],[]) -> ed1
                              | uu____3508 ->
                                  let op uu____3540 =
                                    match uu____3540 with
                                    | (us,t) ->
                                        let n_us = FStar_List.length us  in
                                        let uu____3560 =
                                          let uu____3561 =
                                            FStar_Syntax_Subst.shift_subst
                                              n_us opening
                                             in
                                          let uu____3570 = open_univs n_us t
                                             in
                                          FStar_Syntax_Subst.subst uu____3561
                                            uu____3570
                                           in
                                        (us, uu____3560)
                                     in
                                  let uu___388_3579 = ed1  in
                                  let uu____3580 =
                                    let uu____3581 =
                                      let uu____3582 =
                                        op
                                          ([],
                                            ((ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m))
                                         in
                                      FStar_Pervasives_Native.snd uu____3582
                                       in
                                    let uu____3593 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                       in
                                    let uu____3594 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                       in
                                    {
                                      FStar_Syntax_Syntax.monad_m =
                                        uu____3581;
                                      FStar_Syntax_Syntax.monad_ret =
                                        uu____3593;
                                      FStar_Syntax_Syntax.monad_bind =
                                        uu____3594
                                    }  in
                                  let uu____3595 =
                                    op ed1.FStar_Syntax_Syntax.if_then_else
                                     in
                                  let uu____3596 =
                                    op ed1.FStar_Syntax_Syntax.ite_wp  in
                                  let uu____3597 =
                                    op ed1.FStar_Syntax_Syntax.stronger  in
                                  let uu____3598 =
                                    op ed1.FStar_Syntax_Syntax.close_wp  in
                                  let uu____3599 =
                                    op ed1.FStar_Syntax_Syntax.assert_p  in
                                  let uu____3600 =
                                    op ed1.FStar_Syntax_Syntax.assume_p  in
                                  let uu____3601 =
                                    op ed1.FStar_Syntax_Syntax.null_wp  in
                                  let uu____3602 =
                                    op ed1.FStar_Syntax_Syntax.trivial  in
                                  let uu____3603 =
                                    let uu____3604 =
                                      let uu____3605 =
                                        op
                                          ([],
                                            ((ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m))
                                         in
                                      FStar_Pervasives_Native.snd uu____3605
                                       in
                                    let uu____3616 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                       in
                                    let uu____3617 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                       in
                                    {
                                      FStar_Syntax_Syntax.monad_m =
                                        uu____3604;
                                      FStar_Syntax_Syntax.monad_ret =
                                        uu____3616;
                                      FStar_Syntax_Syntax.monad_bind =
                                        uu____3617
                                    }  in
                                  let uu____3618 =
                                    FStar_List.map
                                      (fun a  ->
                                         let uu___389_3626 = a  in
                                         let uu____3627 =
                                           let uu____3628 =
                                             op
                                               ((a.FStar_Syntax_Syntax.action_univs),
                                                 (a.FStar_Syntax_Syntax.action_defn))
                                              in
                                           FStar_Pervasives_Native.snd
                                             uu____3628
                                            in
                                         let uu____3639 =
                                           let uu____3640 =
                                             op
                                               ((a.FStar_Syntax_Syntax.action_univs),
                                                 (a.FStar_Syntax_Syntax.action_typ))
                                              in
                                           FStar_Pervasives_Native.snd
                                             uu____3640
                                            in
                                         {
                                           FStar_Syntax_Syntax.action_name =
                                             (uu___389_3626.FStar_Syntax_Syntax.action_name);
                                           FStar_Syntax_Syntax.action_unqualified_name
                                             =
                                             (uu___389_3626.FStar_Syntax_Syntax.action_unqualified_name);
                                           FStar_Syntax_Syntax.action_univs =
                                             (uu___389_3626.FStar_Syntax_Syntax.action_univs);
                                           FStar_Syntax_Syntax.action_params
                                             =
                                             (uu___389_3626.FStar_Syntax_Syntax.action_params);
                                           FStar_Syntax_Syntax.action_defn =
                                             uu____3627;
                                           FStar_Syntax_Syntax.action_typ =
                                             uu____3639
                                         }) ed1.FStar_Syntax_Syntax.actions
                                     in
                                  {
                                    FStar_Syntax_Syntax.cattributes =
                                      (uu___388_3579.FStar_Syntax_Syntax.cattributes);
                                    FStar_Syntax_Syntax.mname =
                                      (uu___388_3579.FStar_Syntax_Syntax.mname);
                                    FStar_Syntax_Syntax.univs =
                                      annotated_univ_names;
                                    FStar_Syntax_Syntax.binders =
                                      (uu___388_3579.FStar_Syntax_Syntax.binders);
                                    FStar_Syntax_Syntax.spec = uu____3580;
                                    FStar_Syntax_Syntax.signature =
                                      (uu___388_3579.FStar_Syntax_Syntax.signature);
                                    FStar_Syntax_Syntax.if_then_else =
                                      uu____3595;
                                    FStar_Syntax_Syntax.ite_wp = uu____3596;
                                    FStar_Syntax_Syntax.stronger = uu____3597;
                                    FStar_Syntax_Syntax.close_wp = uu____3598;
                                    FStar_Syntax_Syntax.assert_p = uu____3599;
                                    FStar_Syntax_Syntax.assume_p = uu____3600;
                                    FStar_Syntax_Syntax.null_wp = uu____3601;
                                    FStar_Syntax_Syntax.trivial = uu____3602;
                                    FStar_Syntax_Syntax.repr = uu____3603;
                                    FStar_Syntax_Syntax.elaborated =
                                      (uu___388_3579.FStar_Syntax_Syntax.elaborated);
                                    FStar_Syntax_Syntax.spec_dm4f =
                                      (uu___388_3579.FStar_Syntax_Syntax.spec_dm4f);
                                    FStar_Syntax_Syntax.interp =
                                      (uu___388_3579.FStar_Syntax_Syntax.interp);
                                    FStar_Syntax_Syntax.actions = uu____3618;
                                    FStar_Syntax_Syntax.eff_attrs =
                                      (uu___388_3579.FStar_Syntax_Syntax.eff_attrs)
                                  }
                               in
                            ((let uu____3652 =
                                FStar_TypeChecker_Env.debug env0
                                  (FStar_Options.Other "ED")
                                 in
                              if uu____3652
                              then
                                let uu____3656 =
                                  FStar_Syntax_Print.eff_decl_to_string ed2
                                   in
                                FStar_Util.print1
                                  "eff_decl after opening:\n\t%s\n"
                                  uu____3656
                              else ());
                             (let wp_with_fresh_result_type env2 mname
                                signature2 =
                                let fail1 t =
                                  let uu____3695 =
                                    FStar_TypeChecker_Err.unexpected_signature_for_monad
                                      env2 mname t
                                     in
                                  let uu____3701 =
                                    FStar_Ident.range_of_lid mname  in
                                  FStar_Errors.raise_error uu____3695
                                    uu____3701
                                   in
                                let uu____3708 =
                                  let uu____3709 =
                                    FStar_Syntax_Subst.compress signature2
                                     in
                                  uu____3709.FStar_Syntax_Syntax.n  in
                                match uu____3708 with
                                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                    let bs1 =
                                      FStar_Syntax_Subst.open_binders bs  in
                                    (match bs1 with
                                     | (a,uu____3748)::(wp,uu____3750)::[] ->
                                         (a, (wp.FStar_Syntax_Syntax.sort))
                                     | uu____3779 -> fail1 signature2)
                                | uu____3780 -> fail1 signature2  in
                              let uu____3781 =
                                wp_with_fresh_result_type env1
                                  ed2.FStar_Syntax_Syntax.mname signature1
                                 in
                              match uu____3781 with
                              | (a,wp_a) ->
                                  let fresh_effect_signature uu____3805 =
                                    match annotated_univ_names with
                                    | [] ->
                                        let uu____3812 =
                                          FStar_TypeChecker_TcTerm.tc_trivial_guard
                                            env1 signature_un
                                           in
                                        (match uu____3812 with
                                         | (signature2,uu____3824) ->
                                             wp_with_fresh_result_type env1
                                               ed2.FStar_Syntax_Syntax.mname
                                               signature2)
                                    | uu____3825 ->
                                        let uu____3828 =
                                          let uu____3833 =
                                            let uu____3834 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                annotated_univ_names
                                                signature1
                                               in
                                            (annotated_univ_names,
                                              uu____3834)
                                             in
                                          FStar_TypeChecker_Env.inst_tscheme
                                            uu____3833
                                           in
                                        (match uu____3828 with
                                         | (uu____3847,signature2) ->
                                             wp_with_fresh_result_type env1
                                               ed2.FStar_Syntax_Syntax.mname
                                               signature2)
                                     in
                                  let env2 =
                                    let uu____3850 =
                                      FStar_Syntax_Syntax.new_bv
                                        FStar_Pervasives_Native.None
                                        signature1
                                       in
                                    FStar_TypeChecker_Env.push_bv env1
                                      uu____3850
                                     in
                                  ((let uu____3852 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env0)
                                        (FStar_Options.Other "ED")
                                       in
                                    if uu____3852
                                    then
                                      let uu____3857 =
                                        FStar_Syntax_Print.lid_to_string
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      let uu____3859 =
                                        FStar_Syntax_Print.binders_to_string
                                          " " ed2.FStar_Syntax_Syntax.binders
                                         in
                                      let uu____3862 =
                                        FStar_Syntax_Print.term_to_string
                                          signature1
                                         in
                                      let uu____3864 =
                                        let uu____3866 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Print.term_to_string
                                          uu____3866
                                         in
                                      let uu____3867 =
                                        FStar_Syntax_Print.term_to_string
                                          a.FStar_Syntax_Syntax.sort
                                         in
                                      FStar_Util.print5
                                        "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                        uu____3857 uu____3859 uu____3862
                                        uu____3864 uu____3867
                                    else ());
                                   (let check_and_gen' env3 uu____3902 k =
                                      match uu____3902 with
                                      | (us,t) ->
                                          (match annotated_univ_names with
                                           | [] -> check_and_gen env3 t k
                                           | uu____3938::uu____3939 ->
                                               let uu____3942 =
                                                 FStar_Syntax_Subst.subst_tscheme
                                                   open_annotated_univs
                                                   (us, t)
                                                  in
                                               (match uu____3942 with
                                                | (us1,t1) ->
                                                    let uu____3965 =
                                                      FStar_Syntax_Subst.open_univ_vars
                                                        us1 t1
                                                       in
                                                    (match uu____3965 with
                                                     | (us2,t2) ->
                                                         let uu____3980 =
                                                           let uu____3981 =
                                                             FStar_TypeChecker_Env.push_univ_vars
                                                               env3 us2
                                                              in
                                                           tc_check_trivial_guard
                                                             uu____3981 t2 k
                                                            in
                                                         let uu____3982 =
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             us2 t2
                                                            in
                                                         (us2, uu____3982))))
                                       in
                                    let return_wp =
                                      let expected_k =
                                        let uu____4001 =
                                          let uu____4010 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4017 =
                                            let uu____4026 =
                                              let uu____4033 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4033
                                               in
                                            [uu____4026]  in
                                          uu____4010 :: uu____4017  in
                                        let uu____4052 =
                                          FStar_Syntax_Syntax.mk_GTotal wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4001
                                          uu____4052
                                         in
                                      check_and_gen' env2
                                        (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                        expected_k
                                       in
                                    let bind_wp =
                                      let uu____4056 =
                                        fresh_effect_signature ()  in
                                      match uu____4056 with
                                      | (b,wp_b) ->
                                          let a_wp_b =
                                            let uu____4072 =
                                              let uu____4081 =
                                                let uu____4088 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____4088
                                                 in
                                              [uu____4081]  in
                                            let uu____4101 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_b
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4072 uu____4101
                                             in
                                          let expected_k =
                                            let uu____4107 =
                                              let uu____4116 =
                                                FStar_Syntax_Syntax.null_binder
                                                  FStar_Syntax_Syntax.t_range
                                                 in
                                              let uu____4123 =
                                                let uu____4132 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____4139 =
                                                  let uu____4148 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____4155 =
                                                    let uu____4164 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_a
                                                       in
                                                    let uu____4171 =
                                                      let uu____4180 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          a_wp_b
                                                         in
                                                      [uu____4180]  in
                                                    uu____4164 :: uu____4171
                                                     in
                                                  uu____4148 :: uu____4155
                                                   in
                                                uu____4132 :: uu____4139  in
                                              uu____4116 :: uu____4123  in
                                            let uu____4223 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_b
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4107 uu____4223
                                             in
                                          check_and_gen' env2
                                            (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                            expected_k
                                       in
                                    let interp =
                                      match ed2.FStar_Syntax_Syntax.interp
                                      with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some interp
                                          ->
                                          let uu____4256 =
                                            fresh_effect_signature ()  in
                                          (match uu____4256 with
                                           | (a1,wp_a1) ->
                                               let repr_a =
                                                 let uu____4282 =
                                                   let uu____4293 =
                                                     let uu____4302 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a1
                                                        in
                                                     FStar_Syntax_Syntax.as_arg
                                                       uu____4302
                                                      in
                                                   [uu____4293]  in
                                                 FStar_Syntax_Util.mk_app
                                                   (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                                   uu____4282
                                                  in
                                               let expected_k =
                                                 let uu____4322 =
                                                   let uu____4331 =
                                                     FStar_Syntax_Syntax.mk_implicit_binder
                                                       a1
                                                      in
                                                   let uu____4338 =
                                                     let uu____4347 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         repr_a
                                                        in
                                                     [uu____4347]  in
                                                   uu____4331 :: uu____4338
                                                    in
                                                 let uu____4372 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     wp_a1
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____4322 uu____4372
                                                  in
                                               let uu____4375 =
                                                 check_and_gen' env2
                                                   ([], interp) expected_k
                                                  in
                                               FStar_All.pipe_left
                                                 (fun _0_1  ->
                                                    FStar_Pervasives_Native.Some
                                                      _0_1) uu____4375)
                                       in
                                    let if_then_else1 =
                                      let p =
                                        let uu____4424 =
                                          let uu____4427 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4427
                                           in
                                        let uu____4428 =
                                          let uu____4429 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4429
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4424
                                          uu____4428
                                         in
                                      let expected_k =
                                        let uu____4441 =
                                          let uu____4450 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4457 =
                                            let uu____4466 =
                                              FStar_Syntax_Syntax.mk_binder p
                                               in
                                            let uu____4473 =
                                              let uu____4482 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              let uu____4489 =
                                                let uu____4498 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____4498]  in
                                              uu____4482 :: uu____4489  in
                                            uu____4466 :: uu____4473  in
                                          uu____4450 :: uu____4457  in
                                        let uu____4535 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4441
                                          uu____4535
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.if_then_else
                                        expected_k
                                       in
                                    let ite_wp =
                                      let expected_k =
                                        let uu____4550 =
                                          let uu____4559 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4566 =
                                            let uu____4575 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____4575]  in
                                          uu____4559 :: uu____4566  in
                                        let uu____4600 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4550
                                          uu____4600
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.ite_wp
                                        expected_k
                                       in
                                    let stronger =
                                      let uu____4604 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____4604 with
                                      | (t,uu____4610) ->
                                          let expected_k =
                                            let uu____4614 =
                                              let uu____4623 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4630 =
                                                let uu____4639 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____4646 =
                                                  let uu____4655 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____4655]  in
                                                uu____4639 :: uu____4646  in
                                              uu____4623 :: uu____4630  in
                                            let uu____4686 =
                                              FStar_Syntax_Syntax.mk_Total t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4614 uu____4686
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.stronger
                                            expected_k
                                       in
                                    let close_wp =
                                      let b =
                                        let uu____4699 =
                                          let uu____4702 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4702
                                           in
                                        let uu____4703 =
                                          let uu____4704 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4704
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4699
                                          uu____4703
                                         in
                                      let b_wp_a =
                                        let uu____4716 =
                                          let uu____4725 =
                                            let uu____4732 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                b
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____4732
                                             in
                                          [uu____4725]  in
                                        let uu____4745 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4716
                                          uu____4745
                                         in
                                      let expected_k =
                                        let uu____4751 =
                                          let uu____4760 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4767 =
                                            let uu____4776 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4783 =
                                              let uu____4792 =
                                                FStar_Syntax_Syntax.null_binder
                                                  b_wp_a
                                                 in
                                              [uu____4792]  in
                                            uu____4776 :: uu____4783  in
                                          uu____4760 :: uu____4767  in
                                        let uu____4823 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4751
                                          uu____4823
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.close_wp
                                        expected_k
                                       in
                                    let assert_p =
                                      let expected_k =
                                        let uu____4838 =
                                          let uu____4847 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4854 =
                                            let uu____4863 =
                                              let uu____4870 =
                                                let uu____4871 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____4871
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4870
                                               in
                                            let uu____4880 =
                                              let uu____4889 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____4889]  in
                                            uu____4863 :: uu____4880  in
                                          uu____4847 :: uu____4854  in
                                        let uu____4920 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4838
                                          uu____4920
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.assert_p
                                        expected_k
                                       in
                                    let assume_p =
                                      let expected_k =
                                        let uu____4935 =
                                          let uu____4944 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4951 =
                                            let uu____4960 =
                                              let uu____4967 =
                                                let uu____4968 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____4968
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4967
                                               in
                                            let uu____4977 =
                                              let uu____4986 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____4986]  in
                                            uu____4960 :: uu____4977  in
                                          uu____4944 :: uu____4951  in
                                        let uu____5017 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4935
                                          uu____5017
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.assume_p
                                        expected_k
                                       in
                                    let null_wp =
                                      let expected_k =
                                        let uu____5032 =
                                          let uu____5041 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          [uu____5041]  in
                                        let uu____5060 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____5032
                                          uu____5060
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.null_wp
                                        expected_k
                                       in
                                    let trivial_wp =
                                      let uu____5064 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____5064 with
                                      | (t,uu____5070) ->
                                          let expected_k =
                                            let uu____5074 =
                                              let uu____5083 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____5090 =
                                                let uu____5099 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____5099]  in
                                              uu____5083 :: uu____5090  in
                                            let uu____5124 =
                                              FStar_Syntax_Syntax.mk_GTotal t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5074 uu____5124
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.trivial
                                            expected_k
                                       in
                                    let uu____5127 =
                                      let uu____5140 =
                                        let uu____5145 =
                                          let uu____5146 =
                                            FStar_Syntax_Subst.compress
                                              (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                             in
                                          uu____5146.FStar_Syntax_Syntax.n
                                           in
                                        let uu____5149 =
                                          let uu____5150 =
                                            FStar_Syntax_Subst.compress
                                              (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m
                                             in
                                          uu____5150.FStar_Syntax_Syntax.n
                                           in
                                        (uu____5145, uu____5149)  in
                                      if ed2.FStar_Syntax_Syntax.spec_dm4f
                                      then
                                        let repr =
                                          let uu____5166 =
                                            FStar_Syntax_Util.type_u ()  in
                                          match uu____5166 with
                                          | (t,uu____5172) ->
                                              let expected_k =
                                                let uu____5176 =
                                                  let uu____5185 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____5192 =
                                                    let uu____5201 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_a
                                                       in
                                                    [uu____5201]  in
                                                  uu____5185 :: uu____5192
                                                   in
                                                let uu____5226 =
                                                  FStar_Syntax_Syntax.mk_GTotal
                                                    t
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____5176 uu____5226
                                                 in
                                              ((let uu____5230 =
                                                  FStar_TypeChecker_Env.debug
                                                    env2
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____5230
                                                then
                                                  let uu____5234 =
                                                    FStar_Syntax_Print.term_to_string
                                                      (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                                     in
                                                  let uu____5236 =
                                                    FStar_Syntax_Print.term_to_string
                                                      expected_k
                                                     in
                                                  FStar_Util.print2
                                                    "About to check repr=%s\nat type %s\n"
                                                    uu____5234 uu____5236
                                                else ());
                                               tc_check_trivial_guard env2
                                                 (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                                 expected_k)
                                           in
                                        let mk_repr' t wp =
                                          let repr1 =
                                            FStar_TypeChecker_Normalize.normalize
                                              [FStar_TypeChecker_Env.EraseUniverses;
                                              FStar_TypeChecker_Env.AllowUnboundUniverses]
                                              env2 repr
                                             in
                                          let uu____5255 =
                                            let uu____5262 =
                                              let uu____5263 =
                                                let uu____5280 =
                                                  let uu____5291 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      t
                                                     in
                                                  let uu____5300 =
                                                    let uu____5311 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        wp
                                                       in
                                                    [uu____5311]  in
                                                  uu____5291 :: uu____5300
                                                   in
                                                (repr1, uu____5280)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____5263
                                               in
                                            FStar_Syntax_Syntax.mk uu____5262
                                             in
                                          uu____5255
                                            FStar_Pervasives_Native.None
                                            FStar_Range.dummyRange
                                           in
                                        let mk_repr a1 wp =
                                          let uu____5372 =
                                            FStar_Syntax_Syntax.bv_to_name a1
                                             in
                                          mk_repr' uu____5372 wp  in
                                        let destruct_repr t =
                                          let uu____5387 =
                                            let uu____5388 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____5388.FStar_Syntax_Syntax.n
                                             in
                                          match uu____5387 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____5399,(t1,uu____5401)::
                                               (wp,uu____5403)::[])
                                              -> (t1, wp)
                                          | uu____5462 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let bind_repr =
                                          let r =
                                            let uu____5474 =
                                              FStar_Syntax_Syntax.lid_as_fv
                                                FStar_Parser_Const.range_0
                                                FStar_Syntax_Syntax.delta_constant
                                                FStar_Pervasives_Native.None
                                               in
                                            FStar_All.pipe_right uu____5474
                                              FStar_Syntax_Syntax.fv_to_tm
                                             in
                                          let uu____5475 =
                                            fresh_effect_signature ()  in
                                          match uu____5475 with
                                          | (b,wp_b) ->
                                              let a_wp_b =
                                                let uu____5491 =
                                                  let uu____5500 =
                                                    let uu____5507 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        a
                                                       in
                                                    FStar_Syntax_Syntax.null_binder
                                                      uu____5507
                                                     in
                                                  [uu____5500]  in
                                                let uu____5520 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    wp_b
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____5491 uu____5520
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
                                                let uu____5528 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____5528
                                                 in
                                              let wp_g_x =
                                                let uu____5533 =
                                                  let uu____5538 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      wp_g
                                                     in
                                                  let uu____5539 =
                                                    let uu____5540 =
                                                      let uu____5549 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x_a
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.as_arg
                                                        uu____5549
                                                       in
                                                    [uu____5540]  in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____5538 uu____5539
                                                   in
                                                uu____5533
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____5582 =
                                                    let uu____5587 =
                                                      let uu____5588 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          bind_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____5588
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____5597 =
                                                      let uu____5598 =
                                                        let uu____5601 =
                                                          let uu____5604 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          let uu____5605 =
                                                            let uu____5608 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                b
                                                               in
                                                            let uu____5609 =
                                                              let uu____5612
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_f
                                                                 in
                                                              let uu____5613
                                                                =
                                                                let uu____5616
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                   in
                                                                [uu____5616]
                                                                 in
                                                              uu____5612 ::
                                                                uu____5613
                                                               in
                                                            uu____5608 ::
                                                              uu____5609
                                                             in
                                                          uu____5604 ::
                                                            uu____5605
                                                           in
                                                        r :: uu____5601  in
                                                      FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg
                                                        uu____5598
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____5587 uu____5597
                                                     in
                                                  uu____5582
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr b wp  in
                                              let maybe_range_arg =
                                                let uu____5636 =
                                                  FStar_Util.for_some
                                                    (FStar_Syntax_Util.attr_eq
                                                       FStar_Syntax_Util.dm4f_bind_range_attr)
                                                    ed2.FStar_Syntax_Syntax.eff_attrs
                                                   in
                                                if uu____5636
                                                then
                                                  let uu____5647 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      FStar_Syntax_Syntax.t_range
                                                     in
                                                  let uu____5654 =
                                                    let uu____5663 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        FStar_Syntax_Syntax.t_range
                                                       in
                                                    [uu____5663]  in
                                                  uu____5647 :: uu____5654
                                                else []  in
                                              let expected_k =
                                                let uu____5699 =
                                                  let uu____5708 =
                                                    let uu____5717 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a
                                                       in
                                                    let uu____5724 =
                                                      let uu____5733 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          b
                                                         in
                                                      [uu____5733]  in
                                                    uu____5717 :: uu____5724
                                                     in
                                                  let uu____5758 =
                                                    let uu____5767 =
                                                      let uu____5776 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          wp_f
                                                         in
                                                      let uu____5783 =
                                                        let uu____5792 =
                                                          let uu____5799 =
                                                            let uu____5800 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            mk_repr a
                                                              uu____5800
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____5799
                                                           in
                                                        let uu____5801 =
                                                          let uu____5810 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              wp_g
                                                             in
                                                          let uu____5817 =
                                                            let uu____5826 =
                                                              let uu____5833
                                                                =
                                                                let uu____5834
                                                                  =
                                                                  let uu____5843
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                  [uu____5843]
                                                                   in
                                                                let uu____5862
                                                                  =
                                                                  let uu____5865
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____5865
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  uu____5834
                                                                  uu____5862
                                                                 in
                                                              FStar_Syntax_Syntax.null_binder
                                                                uu____5833
                                                               in
                                                            [uu____5826]  in
                                                          uu____5810 ::
                                                            uu____5817
                                                           in
                                                        uu____5792 ::
                                                          uu____5801
                                                         in
                                                      uu____5776 ::
                                                        uu____5783
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____5767
                                                     in
                                                  FStar_List.append
                                                    uu____5708 uu____5758
                                                   in
                                                let uu____5910 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____5699 uu____5910
                                                 in
                                              ((let uu____5914 =
                                                  FStar_TypeChecker_Env.debug
                                                    env2
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____5914
                                                then
                                                  let uu____5918 =
                                                    FStar_Syntax_Print.term_to_string
                                                      expected_k
                                                     in
                                                  FStar_Util.print1
                                                    "About to check expected_k %s\n"
                                                    uu____5918
                                                else ());
                                               (let uu____5923 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env2 expected_k
                                                   in
                                                match uu____5923 with
                                                | (expected_k1,uu____5931,uu____5932)
                                                    ->
                                                    ((let uu____5934 =
                                                        FStar_TypeChecker_Env.debug
                                                          env2
                                                          (FStar_Options.Other
                                                             "ED")
                                                         in
                                                      if uu____5934
                                                      then
                                                        let uu____5938 =
                                                          FStar_Syntax_Print.term_to_string
                                                            (FStar_Pervasives_Native.snd
                                                               (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind)
                                                           in
                                                        let uu____5944 =
                                                          FStar_Syntax_Print.term_to_string
                                                            expected_k1
                                                           in
                                                        FStar_Util.print2
                                                          "About to check bind=%s\n\n, at type %s\n"
                                                          uu____5938
                                                          uu____5944
                                                      else ());
                                                     (let env3 =
                                                        FStar_TypeChecker_Env.set_range
                                                          env2
                                                          (FStar_Pervasives_Native.snd
                                                             (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind).FStar_Syntax_Syntax.pos
                                                         in
                                                      let env4 =
                                                        let uu___390_5955 =
                                                          env3  in
                                                        {
                                                          FStar_TypeChecker_Env.solver
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.solver);
                                                          FStar_TypeChecker_Env.range
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.range);
                                                          FStar_TypeChecker_Env.curmodule
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.curmodule);
                                                          FStar_TypeChecker_Env.gamma
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.gamma);
                                                          FStar_TypeChecker_Env.gamma_sig
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.gamma_sig);
                                                          FStar_TypeChecker_Env.gamma_cache
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.gamma_cache);
                                                          FStar_TypeChecker_Env.modules
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.modules);
                                                          FStar_TypeChecker_Env.expected_typ
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.expected_typ);
                                                          FStar_TypeChecker_Env.sigtab
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.sigtab);
                                                          FStar_TypeChecker_Env.attrtab
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.attrtab);
                                                          FStar_TypeChecker_Env.is_pattern
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.is_pattern);
                                                          FStar_TypeChecker_Env.instantiate_imp
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.instantiate_imp);
                                                          FStar_TypeChecker_Env.effects
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.effects);
                                                          FStar_TypeChecker_Env.generalize
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.generalize);
                                                          FStar_TypeChecker_Env.letrecs
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.letrecs);
                                                          FStar_TypeChecker_Env.top_level
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.top_level);
                                                          FStar_TypeChecker_Env.check_uvars
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.check_uvars);
                                                          FStar_TypeChecker_Env.use_eq
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.use_eq);
                                                          FStar_TypeChecker_Env.is_iface
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.is_iface);
                                                          FStar_TypeChecker_Env.admit
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.admit);
                                                          FStar_TypeChecker_Env.lax
                                                            = true;
                                                          FStar_TypeChecker_Env.lax_universes
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.lax_universes);
                                                          FStar_TypeChecker_Env.phase1
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.phase1);
                                                          FStar_TypeChecker_Env.failhard
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.failhard);
                                                          FStar_TypeChecker_Env.nosynth
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.nosynth);
                                                          FStar_TypeChecker_Env.uvar_subtyping
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.uvar_subtyping);
                                                          FStar_TypeChecker_Env.tc_term
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.tc_term);
                                                          FStar_TypeChecker_Env.type_of
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.type_of);
                                                          FStar_TypeChecker_Env.universe_of
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.universe_of);
                                                          FStar_TypeChecker_Env.check_type_of
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.check_type_of);
                                                          FStar_TypeChecker_Env.use_bv_sorts
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.use_bv_sorts);
                                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                          FStar_TypeChecker_Env.normalized_eff_names
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.normalized_eff_names);
                                                          FStar_TypeChecker_Env.fv_delta_depths
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.fv_delta_depths);
                                                          FStar_TypeChecker_Env.proof_ns
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.proof_ns);
                                                          FStar_TypeChecker_Env.synth_hook
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.synth_hook);
                                                          FStar_TypeChecker_Env.splice
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.splice);
                                                          FStar_TypeChecker_Env.postprocess
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.postprocess);
                                                          FStar_TypeChecker_Env.is_native_tactic
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.is_native_tactic);
                                                          FStar_TypeChecker_Env.identifier_info
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.identifier_info);
                                                          FStar_TypeChecker_Env.tc_hooks
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.tc_hooks);
                                                          FStar_TypeChecker_Env.dsenv
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.dsenv);
                                                          FStar_TypeChecker_Env.nbe
                                                            =
                                                            (uu___390_5955.FStar_TypeChecker_Env.nbe)
                                                        }  in
                                                      let br =
                                                        check_and_gen' env4
                                                          (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                                          expected_k1
                                                         in
                                                      (let uu____5967 =
                                                         FStar_TypeChecker_Env.debug
                                                           env4
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____5967
                                                       then
                                                         let uu____5971 =
                                                           FStar_Syntax_Print.tscheme_to_string
                                                             br
                                                            in
                                                         let uu____5973 =
                                                           FStar_Syntax_Print.term_to_string
                                                             expected_k1
                                                            in
                                                         FStar_Util.print2
                                                           "After checking bind_repr is %s\nexpected_k is %s\n"
                                                           uu____5971
                                                           uu____5973
                                                       else ());
                                                      br))))
                                           in
                                        let return_repr =
                                          let x_a =
                                            let uu____5980 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.gen_bv "x_a"
                                              FStar_Pervasives_Native.None
                                              uu____5980
                                             in
                                          let res =
                                            let wp =
                                              let uu____5988 =
                                                let uu____5993 =
                                                  let uu____5994 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      return_wp
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____5994
                                                    FStar_Pervasives_Native.snd
                                                   in
                                                let uu____6003 =
                                                  let uu____6004 =
                                                    let uu____6007 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        a
                                                       in
                                                    let uu____6008 =
                                                      let uu____6011 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x_a
                                                         in
                                                      [uu____6011]  in
                                                    uu____6007 :: uu____6008
                                                     in
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.as_arg
                                                    uu____6004
                                                   in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____5993 uu____6003
                                                 in
                                              uu____5988
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            mk_repr a wp  in
                                          let expected_k =
                                            let uu____6025 =
                                              let uu____6034 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____6041 =
                                                let uu____6050 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    x_a
                                                   in
                                                [uu____6050]  in
                                              uu____6034 :: uu____6041  in
                                            let uu____6075 =
                                              FStar_Syntax_Syntax.mk_Total
                                                res
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____6025 uu____6075
                                             in
                                          let uu____6078 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k
                                             in
                                          match uu____6078 with
                                          | (expected_k1,uu____6086,uu____6087)
                                              ->
                                              let env3 =
                                                FStar_TypeChecker_Env.set_range
                                                  env2
                                                  (FStar_Pervasives_Native.snd
                                                     (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret).FStar_Syntax_Syntax.pos
                                                 in
                                              let uu____6093 =
                                                check_and_gen' env3
                                                  (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                                  expected_k1
                                                 in
                                              (match uu____6093 with
                                               | (univs1,repr1) ->
                                                   (match univs1 with
                                                    | [] -> ([], repr1)
                                                    | uu____6116 ->
                                                        FStar_Errors.raise_error
                                                          (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                            "Unexpected universe-polymorphic return for effect")
                                                          repr1.FStar_Syntax_Syntax.pos))
                                           in
                                        let actions =
                                          let check_action act =
                                            let uu____6131 =
                                              if
                                                act.FStar_Syntax_Syntax.action_univs
                                                  = []
                                              then (env2, act)
                                              else
                                                (let uu____6145 =
                                                   FStar_Syntax_Subst.univ_var_opening
                                                     act.FStar_Syntax_Syntax.action_univs
                                                    in
                                                 match uu____6145 with
                                                 | (usubst,uvs) ->
                                                     let uu____6168 =
                                                       FStar_TypeChecker_Env.push_univ_vars
                                                         env2 uvs
                                                        in
                                                     let uu____6169 =
                                                       let uu___391_6170 =
                                                         act  in
                                                       let uu____6171 =
                                                         FStar_Syntax_Subst.subst_binders
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_params
                                                          in
                                                       let uu____6172 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____6173 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___391_6170.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___391_6170.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = uvs;
                                                         FStar_Syntax_Syntax.action_params
                                                           = uu____6171;
                                                         FStar_Syntax_Syntax.action_defn
                                                           = uu____6172;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____6173
                                                       }  in
                                                     (uu____6168, uu____6169))
                                               in
                                            match uu____6131 with
                                            | (env3,act1) ->
                                                let act_typ =
                                                  let uu____6177 =
                                                    let uu____6178 =
                                                      FStar_Syntax_Subst.compress
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                       in
                                                    uu____6178.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____6177 with
                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                      (bs,c) ->
                                                      let c1 =
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                          c
                                                         in
                                                      let uu____6204 =
                                                        FStar_Ident.lid_equals
                                                          c1.FStar_Syntax_Syntax.effect_name
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      if uu____6204
                                                      then
                                                        let uu____6207 =
                                                          let uu____6210 =
                                                            let uu____6211 =
                                                              let uu____6212
                                                                =
                                                                FStar_List.hd
                                                                  c1.FStar_Syntax_Syntax.effect_args
                                                                 in
                                                              FStar_Pervasives_Native.fst
                                                                uu____6212
                                                               in
                                                            mk_repr'
                                                              c1.FStar_Syntax_Syntax.result_typ
                                                              uu____6211
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total
                                                            uu____6210
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          bs uu____6207
                                                      else
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                  | uu____6235 ->
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                   in
                                                let uu____6236 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env3 act_typ
                                                   in
                                                (match uu____6236 with
                                                 | (act_typ1,uu____6244,g_t)
                                                     ->
                                                     let env' =
                                                       let uu___392_6247 =
                                                         FStar_TypeChecker_Env.set_expected_typ
                                                           env3 act_typ1
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.is_pattern
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.is_pattern);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           = false;
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.lax);
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___392_6247.FStar_TypeChecker_Env.nbe)
                                                       }  in
                                                     ((let uu____6250 =
                                                         FStar_TypeChecker_Env.debug
                                                           env3
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____6250
                                                       then
                                                         let uu____6254 =
                                                           FStar_Ident.text_of_lid
                                                             act1.FStar_Syntax_Syntax.action_name
                                                            in
                                                         let uu____6256 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____6258 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act_typ1
                                                            in
                                                         FStar_Util.print3
                                                           "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                           uu____6254
                                                           uu____6256
                                                           uu____6258
                                                       else ());
                                                      (let uu____6263 =
                                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                           env'
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       match uu____6263 with
                                                       | (act_defn,uu____6271,g_a)
                                                           ->
                                                           let act_defn1 =
                                                             FStar_TypeChecker_Normalize.normalize
                                                               [FStar_TypeChecker_Env.UnfoldUntil
                                                                  FStar_Syntax_Syntax.delta_constant]
                                                               env3 act_defn
                                                              in
                                                           let act_typ2 =
                                                             FStar_TypeChecker_Normalize.normalize
                                                               [FStar_TypeChecker_Env.UnfoldUntil
                                                                  FStar_Syntax_Syntax.delta_constant;
                                                               FStar_TypeChecker_Env.Eager_unfolding;
                                                               FStar_TypeChecker_Env.Beta]
                                                               env3 act_typ1
                                                              in
                                                           let uu____6275 =
                                                             let act_typ3 =
                                                               FStar_Syntax_Subst.compress
                                                                 act_typ2
                                                                in
                                                             match act_typ3.FStar_Syntax_Syntax.n
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____6311
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                    in
                                                                 (match uu____6311
                                                                  with
                                                                  | (bs1,uu____6323)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6330
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____6330
                                                                     in
                                                                    let uu____6333
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____6333
                                                                    with
                                                                    | 
                                                                    (k1,uu____6347,g)
                                                                    ->
                                                                    (k1, g)))
                                                             | uu____6351 ->
                                                                 let uu____6352
                                                                   =
                                                                   let uu____6358
                                                                    =
                                                                    let uu____6360
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____6362
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____6360
                                                                    uu____6362
                                                                     in
                                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____6358)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____6352
                                                                   act_defn1.FStar_Syntax_Syntax.pos
                                                              in
                                                           (match uu____6275
                                                            with
                                                            | (expected_k,g_k)
                                                                ->
                                                                let g =
                                                                  FStar_TypeChecker_Rel.teq
                                                                    env3
                                                                    act_typ2
                                                                    expected_k
                                                                   in
                                                                ((let uu____6380
                                                                    =
                                                                    let uu____6381
                                                                    =
                                                                    let uu____6382
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____6382
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____6381
                                                                     in
                                                                  FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env3
                                                                    uu____6380);
                                                                 (let act_typ3
                                                                    =
                                                                    let uu____6384
                                                                    =
                                                                    let uu____6385
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____6385.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____6384
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____6410
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____6410
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____6417
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____6417
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____6437
                                                                    =
                                                                    let uu____6438
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____6438]
                                                                     in
                                                                    let uu____6439
                                                                    =
                                                                    let uu____6450
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____6450]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6437;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6439;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____6475
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____6475))
                                                                    | 
                                                                    uu____6478
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                  let uu____6480
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                    else
                                                                    (let uu____6502
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____6502))
                                                                     in
                                                                  match uu____6480
                                                                  with
                                                                  | (univs1,act_defn2)
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
                                                                    let uu___393_6521
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___393_6521.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___393_6521.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___393_6521.FStar_Syntax_Syntax.action_params);
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
                                      else
                                        (match uu____5140 with
                                         | (uu____6530,uu____6531) ->
                                             (((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m),
                                               ((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind),
                                               ((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret),
                                               (ed2.FStar_Syntax_Syntax.actions)))
                                       in
                                    match uu____5127 with
                                    | (repr,bind_repr,return_repr,actions) ->
                                        let t0 =
                                          let uu____6551 =
                                            FStar_Syntax_Syntax.mk_Total
                                              signature1
                                             in
                                          FStar_Syntax_Util.arrow
                                            ed2.FStar_Syntax_Syntax.binders
                                            uu____6551
                                           in
                                        let uu____6554 =
                                          let uu____6559 =
                                            FStar_TypeChecker_Util.generalize_universes
                                              env0 t0
                                             in
                                          match uu____6559 with
                                          | (gen_univs,t) ->
                                              (match annotated_univ_names
                                               with
                                               | [] -> (gen_univs, t)
                                               | uu____6578 ->
                                                   let uu____6581 =
                                                     ((FStar_List.length
                                                         gen_univs)
                                                        =
                                                        (FStar_List.length
                                                           annotated_univ_names))
                                                       &&
                                                       (FStar_List.forall2
                                                          (fun u1  ->
                                                             fun u2  ->
                                                               let uu____6588
                                                                 =
                                                                 FStar_Syntax_Syntax.order_univ_name
                                                                   u1 u2
                                                                  in
                                                               uu____6588 =
                                                                 (Prims.parse_int "0"))
                                                          gen_univs
                                                          annotated_univ_names)
                                                      in
                                                   if uu____6581
                                                   then (gen_univs, t)
                                                   else
                                                     (let uu____6599 =
                                                        let uu____6605 =
                                                          let uu____6607 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 annotated_univ_names)
                                                             in
                                                          let uu____6609 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 gen_univs)
                                                             in
                                                          FStar_Util.format2
                                                            "Expected an effect definition with %s universes; but found %s"
                                                            uu____6607
                                                            uu____6609
                                                           in
                                                        (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                          uu____6605)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____6599
                                                        signature1.FStar_Syntax_Syntax.pos))
                                           in
                                        (match uu____6554 with
                                         | (univs1,t) ->
                                             let signature2 =
                                               let uu____6620 =
                                                 let uu____6633 =
                                                   let uu____6634 =
                                                     FStar_Syntax_Subst.compress
                                                       t
                                                      in
                                                   uu____6634.FStar_Syntax_Syntax.n
                                                    in
                                                 (effect_params, uu____6633)
                                                  in
                                               match uu____6620 with
                                               | ([],uu____6645) -> t
                                               | (uu____6660,FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____6661,c)) ->
                                                   FStar_Syntax_Util.comp_result
                                                     c
                                               | uu____6699 ->
                                                   failwith
                                                     "Impossible : t is an arrow"
                                                in
                                             let close1 n1 ts =
                                               let ts1 =
                                                 let uu____6727 =
                                                   FStar_Syntax_Subst.close_tscheme
                                                     effect_params ts
                                                    in
                                                 FStar_Syntax_Subst.close_univ_vars_tscheme
                                                   univs1 uu____6727
                                                  in
                                               let m =
                                                 FStar_List.length
                                                   (FStar_Pervasives_Native.fst
                                                      ts1)
                                                  in
                                               (let uu____6734 =
                                                  ((n1 >=
                                                      (Prims.parse_int "0"))
                                                     &&
                                                     (let uu____6738 =
                                                        FStar_Syntax_Util.is_unknown
                                                          (FStar_Pervasives_Native.snd
                                                             ts1)
                                                         in
                                                      Prims.op_Negation
                                                        uu____6738))
                                                    && (m <> n1)
                                                   in
                                                if uu____6734
                                                then
                                                  let err_msg uu____6756 =
                                                    let error =
                                                      if m < n1
                                                      then
                                                        "not universe-polymorphic enough"
                                                      else
                                                        "too universe-polymorphic"
                                                       in
                                                    let uu____6771 =
                                                      FStar_Util.string_of_int
                                                        m
                                                       in
                                                    let uu____6779 =
                                                      FStar_Util.string_of_int
                                                        n1
                                                       in
                                                    let uu____6781 =
                                                      FStar_Syntax_Print.tscheme_to_string
                                                        ts1
                                                       in
                                                    FStar_Util.format4
                                                      "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                      error uu____6771
                                                      uu____6779 uu____6781
                                                     in
                                                  let uu____6784 =
                                                    let uu____6790 =
                                                      err_msg ()  in
                                                    (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                      uu____6790)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____6784
                                                    (FStar_Pervasives_Native.snd
                                                       ts1).FStar_Syntax_Syntax.pos
                                                else ());
                                               ts1  in
                                             let close_action act =
                                               let uu____6805 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               match uu____6805 with
                                               | (univs2,defn) ->
                                                   let uu____6821 =
                                                     close1
                                                       (~-
                                                          (Prims.parse_int "1"))
                                                       ((act.FStar_Syntax_Syntax.action_univs),
                                                         (act.FStar_Syntax_Syntax.action_typ))
                                                      in
                                                   (match uu____6821 with
                                                    | (univs',typ) ->
                                                        let uu___394_6838 =
                                                          act  in
                                                        {
                                                          FStar_Syntax_Syntax.action_name
                                                            =
                                                            (uu___394_6838.FStar_Syntax_Syntax.action_name);
                                                          FStar_Syntax_Syntax.action_unqualified_name
                                                            =
                                                            (uu___394_6838.FStar_Syntax_Syntax.action_unqualified_name);
                                                          FStar_Syntax_Syntax.action_univs
                                                            = univs2;
                                                          FStar_Syntax_Syntax.action_params
                                                            =
                                                            (uu___394_6838.FStar_Syntax_Syntax.action_params);
                                                          FStar_Syntax_Syntax.action_defn
                                                            = defn;
                                                          FStar_Syntax_Syntax.action_typ
                                                            = typ
                                                        })
                                                in
                                             let ed3 =
                                               let uu___395_6841 = ed2  in
                                               let uu____6842 =
                                                 let uu____6843 =
                                                   close1
                                                     (Prims.parse_int "0")
                                                     return_wp
                                                    in
                                                 let uu____6845 =
                                                   close1
                                                     (Prims.parse_int "1")
                                                     bind_wp
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     =
                                                     FStar_Syntax_Syntax.tun;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____6843;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____6845
                                                 }  in
                                               let uu____6847 =
                                                 close1 (Prims.parse_int "0")
                                                   if_then_else1
                                                  in
                                               let uu____6849 =
                                                 close1 (Prims.parse_int "0")
                                                   ite_wp
                                                  in
                                               let uu____6851 =
                                                 close1 (Prims.parse_int "0")
                                                   stronger
                                                  in
                                               let uu____6853 =
                                                 close1 (Prims.parse_int "1")
                                                   close_wp
                                                  in
                                               let uu____6855 =
                                                 close1 (Prims.parse_int "0")
                                                   assert_p
                                                  in
                                               let uu____6857 =
                                                 close1 (Prims.parse_int "0")
                                                   assume_p
                                                  in
                                               let uu____6859 =
                                                 close1 (Prims.parse_int "0")
                                                   null_wp
                                                  in
                                               let uu____6861 =
                                                 close1 (Prims.parse_int "0")
                                                   trivial_wp
                                                  in
                                               let uu____6863 =
                                                 let uu____6864 =
                                                   let uu____6865 =
                                                     close1
                                                       (Prims.parse_int "0")
                                                       ([], repr)
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____6865
                                                    in
                                                 let uu____6883 =
                                                   close1
                                                     (Prims.parse_int "0")
                                                     return_repr
                                                    in
                                                 let uu____6885 =
                                                   close1
                                                     (Prims.parse_int "1")
                                                     bind_repr
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     = uu____6864;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____6883;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____6885
                                                 }  in
                                               let uu____6887 =
                                                 FStar_Util.map_opt
                                                   ed2.FStar_Syntax_Syntax.interp
                                                   (fun t1  ->
                                                      let uu____6895 =
                                                        close1
                                                          (Prims.parse_int "0")
                                                          ([], t1)
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____6895)
                                                  in
                                               let uu____6913 =
                                                 FStar_List.map close_action
                                                   actions
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.cattributes
                                                   =
                                                   (uu___395_6841.FStar_Syntax_Syntax.cattributes);
                                                 FStar_Syntax_Syntax.mname =
                                                   (uu___395_6841.FStar_Syntax_Syntax.mname);
                                                 FStar_Syntax_Syntax.univs =
                                                   univs1;
                                                 FStar_Syntax_Syntax.binders
                                                   = effect_params;
                                                 FStar_Syntax_Syntax.spec =
                                                   uu____6842;
                                                 FStar_Syntax_Syntax.signature
                                                   = signature2;
                                                 FStar_Syntax_Syntax.if_then_else
                                                   = uu____6847;
                                                 FStar_Syntax_Syntax.ite_wp =
                                                   uu____6849;
                                                 FStar_Syntax_Syntax.stronger
                                                   = uu____6851;
                                                 FStar_Syntax_Syntax.close_wp
                                                   = uu____6853;
                                                 FStar_Syntax_Syntax.assert_p
                                                   = uu____6855;
                                                 FStar_Syntax_Syntax.assume_p
                                                   = uu____6857;
                                                 FStar_Syntax_Syntax.null_wp
                                                   = uu____6859;
                                                 FStar_Syntax_Syntax.trivial
                                                   = uu____6861;
                                                 FStar_Syntax_Syntax.repr =
                                                   uu____6863;
                                                 FStar_Syntax_Syntax.elaborated
                                                   =
                                                   (uu___395_6841.FStar_Syntax_Syntax.elaborated);
                                                 FStar_Syntax_Syntax.spec_dm4f
                                                   =
                                                   (uu___395_6841.FStar_Syntax_Syntax.spec_dm4f);
                                                 FStar_Syntax_Syntax.interp =
                                                   uu____6887;
                                                 FStar_Syntax_Syntax.actions
                                                   = uu____6913;
                                                 FStar_Syntax_Syntax.eff_attrs
                                                   =
                                                   (uu___395_6841.FStar_Syntax_Syntax.eff_attrs)
                                               }  in
                                             ed3)))))))))
  
let tc_lex_t :
  'Auu____6927 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____6927 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____6962 = FStar_List.hd ses  in
            uu____6962.FStar_Syntax_Syntax.sigrng  in
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
           | uu____6967 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____6973,[],t,uu____6975,uu____6976);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____6978;
               FStar_Syntax_Syntax.sigattrs = uu____6979;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____6981,_t_top,_lex_t_top,_0_2,uu____6984);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____6986;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____6987;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____6989,_t_cons,_lex_t_cons,_0_3,uu____6992);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____6994;
                 FStar_Syntax_Syntax.sigattrs = uu____6995;_}::[]
               when
               ((_0_2 = (Prims.parse_int "0")) &&
                  (_0_3 = (Prims.parse_int "0")))
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
                 let uu____7046 =
                   let uu____7053 =
                     let uu____7054 =
                       let uu____7061 =
                         let uu____7064 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____7064
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____7061, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____7054  in
                   FStar_Syntax_Syntax.mk uu____7053  in
                 uu____7046 FStar_Pervasives_Native.None r1  in
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
                   let uu____7082 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7082
                    in
                 let hd1 =
                   let uu____7084 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7084
                    in
                 let tl1 =
                   let uu____7086 =
                     let uu____7087 =
                       let uu____7094 =
                         let uu____7095 =
                           let uu____7102 =
                             let uu____7105 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____7105
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____7102, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____7095  in
                       FStar_Syntax_Syntax.mk uu____7094  in
                     uu____7087 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____7086
                    in
                 let res =
                   let uu____7114 =
                     let uu____7121 =
                       let uu____7122 =
                         let uu____7129 =
                           let uu____7132 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____7132
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____7129,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____7122  in
                     FStar_Syntax_Syntax.mk uu____7121  in
                   uu____7114 FStar_Pervasives_Native.None r2  in
                 let uu____7138 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____7138
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
               let uu____7177 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____7177;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____7182 ->
               let err_msg =
                 let uu____7187 =
                   let uu____7189 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____7189  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____7187
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
    fun uu____7214  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____7214 with
          | (uvs,t) ->
              let uu____7227 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____7227 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____7239 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____7239 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____7257 =
                        let uu____7260 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____7260
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____7257)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7283 =
          let uu____7284 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7284 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7283 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7309 =
          let uu____7310 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7310 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7309 r
  
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
          (let uu____7359 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____7359
           then
             let uu____7362 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____7362
           else ());
          (let uu____7367 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____7367 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____7398 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____7398 FStar_List.flatten  in
               ((let uu____7412 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____7415 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____7415)
                    in
                 if uu____7412
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
                           let uu____7431 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____7441,uu____7442,uu____7443,uu____7444,uu____7445)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____7454 -> failwith "Impossible!"  in
                           match uu____7431 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.strcat "Inductive type "
                                      (Prims.strcat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____7473 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____7483,uu____7484,ty_lid,uu____7486,uu____7487)
                               -> (data_lid, ty_lid)
                           | uu____7494 -> failwith "Impossible"  in
                         match uu____7473 with
                         | (data_lid,ty_lid) ->
                             let uu____7502 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____7505 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____7505)
                                in
                             if uu____7502
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.strcat "Exception "
                                      (Prims.strcat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____7519 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____7524,uu____7525,uu____7526,uu____7527,uu____7528)
                         -> lid
                     | uu____7537 -> failwith "Impossible"  in
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
                   let uu____7555 =
                     (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____7555
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
          let pop1 uu____7630 =
            let uu____7631 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___397_7641  ->
               match () with
               | () ->
                   let uu____7648 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____7648 (fun r  -> pop1 (); r)) ()
          with | uu___396_7679 -> (pop1 (); FStar_Exn.raise uu___396_7679)
  
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en  ->
    let env =
      let uu____7700 = FStar_Options.using_facts_from ()  in
      FStar_TypeChecker_Env.set_proof_ns uu____7700 en  in
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
      | uu____8004 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____8062 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____8062 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____8087 .
    'Auu____8087 FStar_Pervasives_Native.option -> 'Auu____8087 Prims.list
  =
  fun uu___374_8096  ->
    match uu___374_8096 with
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
            let uu____8176 = collect1 tl1  in
            (match uu____8176 with
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
        | ((e,n1)::uu____8414,[]) ->
            FStar_Pervasives_Native.Some (e, n1, (Prims.parse_int "0"))
        | ([],(e,n1)::uu____8470) ->
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
          let uu____8698 =
            let uu____8700 = FStar_Options.ide ()  in
            Prims.op_Negation uu____8700  in
          if uu____8698
          then
            let uu____8703 =
              let uu____8708 = FStar_TypeChecker_Env.dsenv env  in
              let uu____8709 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____8708 uu____8709  in
            (match uu____8703 with
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
                              let uu____8742 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____8743 =
                                let uu____8749 =
                                  let uu____8751 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____8753 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____8751 uu____8753
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____8749)
                                 in
                              FStar_Errors.log_issue uu____8742 uu____8743
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____8760 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____8761 =
                                   let uu____8767 =
                                     let uu____8769 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____8769
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____8767)
                                    in
                                 FStar_Errors.log_issue uu____8760 uu____8761)
                              else ())
                         else ())))
          else ()
      | uu____8779 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____8824 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____8852 ->
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
             let uu____8912 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____8912
             then
               let ses1 =
                 let uu____8920 =
                   let uu____8921 =
                     let uu____8922 =
                       tc_inductive
                         (let uu___398_8931 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___398_8931.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___398_8931.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___398_8931.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___398_8931.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___398_8931.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___398_8931.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___398_8931.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___398_8931.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___398_8931.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___398_8931.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___398_8931.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___398_8931.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___398_8931.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___398_8931.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___398_8931.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___398_8931.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___398_8931.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___398_8931.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___398_8931.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___398_8931.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___398_8931.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___398_8931.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___398_8931.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___398_8931.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___398_8931.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___398_8931.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___398_8931.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___398_8931.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___398_8931.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___398_8931.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___398_8931.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___398_8931.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___398_8931.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___398_8931.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___398_8931.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___398_8931.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___398_8931.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___398_8931.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___398_8931.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___398_8931.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___398_8931.FStar_TypeChecker_Env.nbe)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____8922
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____8921
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____8920
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____8945 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____8945
                 then
                   let uu____8950 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___399_8954 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___399_8954.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___399_8954.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___399_8954.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___399_8954.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____8950
                 else ());
                ses1)
             else ses  in
           let uu____8964 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____8964 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___400_8988 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___400_8988.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___400_8988.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___400_8988.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___400_8988.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let forfree =
             let uu____9002 =
               let uu____9003 =
                 FStar_Syntax_Subst.compress
                   (ne.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                  in
               uu____9003.FStar_Syntax_Syntax.n  in
             match uu____9002 with
             | FStar_Syntax_Syntax.Tm_unknown  -> false
             | uu____9008 ->
                 Prims.op_Negation ne.FStar_Syntax_Syntax.elaborated
              in
           if forfree
           then
             ((let uu____9021 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____9021
               then FStar_Util.print_string "Beginning DM4F run\n"
               else ());
              (let uu____9028 = cps_and_elaborate_ed env0 ne  in
               match uu____9028 with
               | (ses,ne1,lift_from_pure_opt) ->
                   let ne2 =
                     let uu___401_9061 = ne1  in
                     {
                       FStar_Syntax_Syntax.cattributes =
                         (uu___401_9061.FStar_Syntax_Syntax.cattributes);
                       FStar_Syntax_Syntax.mname =
                         (uu___401_9061.FStar_Syntax_Syntax.mname);
                       FStar_Syntax_Syntax.univs =
                         (uu___401_9061.FStar_Syntax_Syntax.univs);
                       FStar_Syntax_Syntax.binders =
                         (uu___401_9061.FStar_Syntax_Syntax.binders);
                       FStar_Syntax_Syntax.spec =
                         (uu___401_9061.FStar_Syntax_Syntax.spec);
                       FStar_Syntax_Syntax.signature =
                         (uu___401_9061.FStar_Syntax_Syntax.signature);
                       FStar_Syntax_Syntax.if_then_else =
                         (uu___401_9061.FStar_Syntax_Syntax.if_then_else);
                       FStar_Syntax_Syntax.ite_wp =
                         (uu___401_9061.FStar_Syntax_Syntax.ite_wp);
                       FStar_Syntax_Syntax.stronger =
                         (uu___401_9061.FStar_Syntax_Syntax.stronger);
                       FStar_Syntax_Syntax.close_wp =
                         (uu___401_9061.FStar_Syntax_Syntax.close_wp);
                       FStar_Syntax_Syntax.assert_p =
                         (uu___401_9061.FStar_Syntax_Syntax.assert_p);
                       FStar_Syntax_Syntax.assume_p =
                         (uu___401_9061.FStar_Syntax_Syntax.assume_p);
                       FStar_Syntax_Syntax.null_wp =
                         (uu___401_9061.FStar_Syntax_Syntax.null_wp);
                       FStar_Syntax_Syntax.trivial =
                         (uu___401_9061.FStar_Syntax_Syntax.trivial);
                       FStar_Syntax_Syntax.repr =
                         (uu___401_9061.FStar_Syntax_Syntax.repr);
                       FStar_Syntax_Syntax.elaborated = true;
                       FStar_Syntax_Syntax.spec_dm4f =
                         (uu___401_9061.FStar_Syntax_Syntax.spec_dm4f);
                       FStar_Syntax_Syntax.interp =
                         (uu___401_9061.FStar_Syntax_Syntax.interp);
                       FStar_Syntax_Syntax.actions =
                         (uu___401_9061.FStar_Syntax_Syntax.actions);
                       FStar_Syntax_Syntax.eff_attrs =
                         (uu___401_9061.FStar_Syntax_Syntax.eff_attrs)
                     }  in
                   let effect_and_lift_ses =
                     match lift_from_pure_opt with
                     | FStar_Pervasives_Native.Some lift ->
                         [(let uu___402_9070 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne2);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___402_9070.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___402_9070.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___402_9070.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___402_9070.FStar_Syntax_Syntax.sigattrs)
                           });
                         lift]
                     | FStar_Pervasives_Native.None  ->
                         [(let uu___403_9072 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne2);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___403_9072.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___403_9072.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___403_9072.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___403_9072.FStar_Syntax_Syntax.sigattrs)
                           })]
                      in
                   ([], (FStar_List.append ses effect_and_lift_ses), env0)))
           else
             (let ne1 =
                let uu____9080 =
                  (FStar_Options.use_two_phase_tc ()) &&
                    (FStar_TypeChecker_Env.should_verify env)
                   in
                if uu____9080
                then
                  let ne1 =
                    let uu____9084 =
                      let uu____9085 =
                        let uu____9086 =
                          tc_eff_decl
                            (let uu___404_9088 = env  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___404_9088.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___404_9088.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___404_9088.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___404_9088.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___404_9088.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___404_9088.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___404_9088.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___404_9088.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___404_9088.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___404_9088.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___404_9088.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___404_9088.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___404_9088.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___404_9088.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___404_9088.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___404_9088.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___404_9088.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___404_9088.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___404_9088.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___404_9088.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___404_9088.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 = true;
                               FStar_TypeChecker_Env.failhard =
                                 (uu___404_9088.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___404_9088.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___404_9088.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___404_9088.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___404_9088.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___404_9088.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___404_9088.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___404_9088.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___404_9088.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___404_9088.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___404_9088.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___404_9088.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___404_9088.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___404_9088.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___404_9088.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___404_9088.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___404_9088.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___404_9088.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___404_9088.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___404_9088.FStar_TypeChecker_Env.nbe)
                             }) se ne
                           in
                        FStar_All.pipe_right uu____9086
                          (fun ne1  ->
                             let uu___405_9094 = se  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___405_9094.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___405_9094.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___405_9094.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___405_9094.FStar_Syntax_Syntax.sigattrs)
                             })
                         in
                      FStar_All.pipe_right uu____9085
                        (FStar_TypeChecker_Normalize.elim_uvars env)
                       in
                    FStar_All.pipe_right uu____9084
                      FStar_Syntax_Util.eff_decl_of_new_effect
                     in
                  ((let uu____9096 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "TwoPhases")
                       in
                    if uu____9096
                    then
                      let uu____9101 =
                        FStar_Syntax_Print.sigelt_to_string
                          (let uu___406_9105 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne1);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___406_9105.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___406_9105.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___406_9105.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___406_9105.FStar_Syntax_Syntax.sigattrs)
                           })
                         in
                      FStar_Util.print1 "Effect decl after phase 1: %s\n"
                        uu____9101
                    else ());
                   ne1)
                else ne  in
              let ne2 = tc_eff_decl env se ne1  in
              let se1 =
                let uu___407_9113 = se  in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_new_effect ne2);
                  FStar_Syntax_Syntax.sigrng =
                    (uu___407_9113.FStar_Syntax_Syntax.sigrng);
                  FStar_Syntax_Syntax.sigquals =
                    (uu___407_9113.FStar_Syntax_Syntax.sigquals);
                  FStar_Syntax_Syntax.sigmeta =
                    (uu___407_9113.FStar_Syntax_Syntax.sigmeta);
                  FStar_Syntax_Syntax.sigattrs =
                    (uu___407_9113.FStar_Syntax_Syntax.sigattrs)
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
           let uu____9121 =
             let uu____9128 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9128
              in
           (match uu____9121 with
            | (a,wp_a_src) ->
                let uu____9145 =
                  let uu____9152 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____9152
                   in
                (match uu____9145 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____9170 =
                         let uu____9173 =
                           let uu____9174 =
                             let uu____9181 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____9181)  in
                           FStar_Syntax_Syntax.NT uu____9174  in
                         [uu____9173]  in
                       FStar_Syntax_Subst.subst uu____9170 wp_b_tgt  in
                     let expected_k =
                       let uu____9189 =
                         let uu____9198 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____9205 =
                           let uu____9214 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____9214]  in
                         uu____9198 :: uu____9205  in
                       let uu____9239 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____9189 uu____9239  in
                     let repr_type eff_name a1 wp =
                       (let uu____9261 =
                          let uu____9263 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____9263  in
                        if uu____9261
                        then
                          let uu____9266 =
                            let uu____9272 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____9272)
                             in
                          let uu____9276 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____9266 uu____9276
                        else ());
                       (let uu____9279 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____9279 with
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
                            let uu____9316 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____9317 =
                              let uu____9324 =
                                let uu____9325 =
                                  let uu____9342 =
                                    let uu____9353 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____9362 =
                                      let uu____9373 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____9373]  in
                                    uu____9353 :: uu____9362  in
                                  (repr, uu____9342)  in
                                FStar_Syntax_Syntax.Tm_app uu____9325  in
                              FStar_Syntax_Syntax.mk uu____9324  in
                            uu____9317 FStar_Pervasives_Native.None
                              uu____9316)
                        in
                     let uu____9421 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____9594 =
                             if
                               (FStar_List.length uvs) >
                                 (Prims.parse_int "0")
                             then
                               let uu____9605 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____9605 with
                               | (usubst,uvs1) ->
                                   let uu____9628 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____9629 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____9628, uu____9629)
                             else (env, lift_wp)  in
                           (match uu____9594 with
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
                                     let uu____9679 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____9679))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____9750 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____9765 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____9765 with
                               | (usubst,uvs) ->
                                   let uu____9790 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____9790)
                             else ([], lift)  in
                           (match uu____9750 with
                            | (uvs,lift1) ->
                                ((let uu____9826 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____9826
                                  then
                                    let uu____9830 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____9830
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____9836 =
                                    let uu____9843 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____9843 lift1
                                     in
                                  match uu____9836 with
                                  | (lift2,comp,uu____9868) ->
                                      let uu____9869 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____9869 with
                                       | (uu____9898,lift_wp,lift_elab) ->
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
                                             let uu____9930 =
                                               let uu____9941 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____9941
                                                in
                                             let uu____9958 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____9930, uu____9958)
                                           else
                                             (let uu____9987 =
                                                let uu____9998 =
                                                  let uu____10007 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____10007)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____9998
                                                 in
                                              let uu____10022 =
                                                let uu____10031 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____10031)  in
                                              (uu____9987, uu____10022))))))
                        in
                     (match uu____9421 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___408_10105 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___408_10105.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___408_10105.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___408_10105.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___408_10105.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___408_10105.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___408_10105.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___408_10105.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___408_10105.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___408_10105.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___408_10105.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___408_10105.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___408_10105.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___408_10105.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___408_10105.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___408_10105.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___408_10105.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___408_10105.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___408_10105.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___408_10105.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___408_10105.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___408_10105.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___408_10105.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___408_10105.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___408_10105.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___408_10105.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___408_10105.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___408_10105.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___408_10105.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___408_10105.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___408_10105.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___408_10105.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___408_10105.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___408_10105.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___408_10105.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___408_10105.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___408_10105.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___408_10105.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___408_10105.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___408_10105.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___408_10105.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___408_10105.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___408_10105.FStar_TypeChecker_Env.nbe)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____10138 =
                                  let uu____10143 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____10143 with
                                  | (usubst,uvs1) ->
                                      let uu____10166 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____10167 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____10166, uu____10167)
                                   in
                                (match uu____10138 with
                                 | (env2,lift2) ->
                                     let uu____10172 =
                                       let uu____10179 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____10179
                                        in
                                     (match uu____10172 with
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
                                              let uu____10205 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____10206 =
                                                let uu____10213 =
                                                  let uu____10214 =
                                                    let uu____10231 =
                                                      let uu____10242 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____10251 =
                                                        let uu____10262 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____10262]  in
                                                      uu____10242 ::
                                                        uu____10251
                                                       in
                                                    (lift_wp1, uu____10231)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10214
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____10213
                                                 in
                                              uu____10206
                                                FStar_Pervasives_Native.None
                                                uu____10205
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____10313 =
                                              let uu____10322 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____10329 =
                                                let uu____10338 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____10345 =
                                                  let uu____10354 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____10354]  in
                                                uu____10338 :: uu____10345
                                                 in
                                              uu____10322 :: uu____10329  in
                                            let uu____10385 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____10313 uu____10385
                                             in
                                          let uu____10388 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____10388 with
                                           | (expected_k2,uu____10398,uu____10399)
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
                                                    let uu____10407 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____10407))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____10415 =
                              let uu____10417 =
                                let uu____10419 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____10419
                                  FStar_List.length
                                 in
                              uu____10417 <> (Prims.parse_int "1")  in
                            if uu____10415
                            then
                              let uu____10441 =
                                let uu____10447 =
                                  let uu____10449 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10451 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10453 =
                                    let uu____10455 =
                                      let uu____10457 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10457
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10455
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10449 uu____10451 uu____10453
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10447)
                                 in
                              FStar_Errors.raise_error uu____10441 r
                            else ());
                           (let uu____10484 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____10487 =
                                   let uu____10489 =
                                     let uu____10492 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____10492
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____10489
                                     FStar_List.length
                                    in
                                 uu____10487 <> (Prims.parse_int "1"))
                               in
                            if uu____10484
                            then
                              let uu____10530 =
                                let uu____10536 =
                                  let uu____10538 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10540 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10542 =
                                    let uu____10544 =
                                      let uu____10546 =
                                        let uu____10549 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____10549
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10546
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10544
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10538 uu____10540 uu____10542
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10536)
                                 in
                              FStar_Errors.raise_error uu____10530 r
                            else ());
                           (let sub2 =
                              let uu___409_10592 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___409_10592.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___409_10592.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___410_10594 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___410_10594.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___410_10594.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___410_10594.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___410_10594.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let uu____10608 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (env, uvs, tps, c)
             else
               (let uu____10636 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____10636 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____10667 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____10667 c  in
                    let uu____10676 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____10676, uvs1, tps1, c1))
              in
           (match uu____10608 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____10698 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____10698 with
                 | (tps2,c2) ->
                     let uu____10715 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____10715 with
                      | (tps3,env3,us) ->
                          let uu____10735 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____10735 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____10763)::uu____10764 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____10783 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____10791 =
                                   let uu____10793 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____10793  in
                                 if uu____10791
                                 then
                                   let uu____10796 =
                                     let uu____10802 =
                                       let uu____10804 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____10806 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____10804 uu____10806
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____10802)
                                      in
                                   FStar_Errors.raise_error uu____10796 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____10814 =
                                   let uu____10815 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____10815
                                    in
                                 match uu____10814 with
                                 | (uvs2,t) ->
                                     let uu____10846 =
                                       let uu____10851 =
                                         let uu____10864 =
                                           let uu____10865 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10865.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____10864)  in
                                       match uu____10851 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____10880,c5)) -> ([], c5)
                                       | (uu____10922,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____10961 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____10846 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____10995 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____10995 with
                                              | (uu____11000,t1) ->
                                                  let uu____11002 =
                                                    let uu____11008 =
                                                      let uu____11010 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____11012 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____11016 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____11010
                                                        uu____11012
                                                        uu____11016
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____11008)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____11002 r)
                                           else ();
                                           (let se1 =
                                              let uu___411_11023 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags1));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___411_11023.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___411_11023.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___411_11023.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___411_11023.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____11030,uu____11031,uu____11032) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___375_11037  ->
                   match uu___375_11037 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11040 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____11046,uu____11047) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___375_11056  ->
                   match uu___375_11056 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____11059 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____11070 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____11070
             then
               let uu____11073 =
                 let uu____11079 =
                   let uu____11081 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____11081
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____11079)
                  in
               FStar_Errors.raise_error uu____11073 r
             else ());
            (let uu____11087 =
               let uu____11096 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____11096
               then
                 let uu____11107 =
                   tc_declare_typ
                     (let uu___412_11110 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___412_11110.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___412_11110.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___412_11110.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___412_11110.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___412_11110.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___412_11110.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___412_11110.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___412_11110.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___412_11110.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___412_11110.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___412_11110.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___412_11110.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___412_11110.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___412_11110.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___412_11110.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___412_11110.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___412_11110.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___412_11110.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___412_11110.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___412_11110.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___412_11110.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___412_11110.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___412_11110.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___412_11110.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___412_11110.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___412_11110.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___412_11110.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___412_11110.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___412_11110.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___412_11110.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___412_11110.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___412_11110.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___412_11110.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___412_11110.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___412_11110.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___412_11110.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___412_11110.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___412_11110.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___412_11110.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___412_11110.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___412_11110.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___412_11110.FStar_TypeChecker_Env.nbe)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____11107 with
                 | (uvs1,t1) ->
                     ((let uu____11135 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____11135
                       then
                         let uu____11140 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____11142 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____11140 uu____11142
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____11087 with
             | (uvs1,t1) ->
                 let uu____11177 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____11177 with
                  | (uvs2,t2) ->
                      ([(let uu___413_11207 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___413_11207.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___413_11207.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___413_11207.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___413_11207.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____11212 =
             let uu____11221 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____11221
             then
               let uu____11232 =
                 tc_assume
                   (let uu___414_11235 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___414_11235.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___414_11235.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___414_11235.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___414_11235.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___414_11235.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___414_11235.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___414_11235.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___414_11235.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___414_11235.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___414_11235.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___414_11235.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___414_11235.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___414_11235.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___414_11235.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___414_11235.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___414_11235.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___414_11235.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___414_11235.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___414_11235.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___414_11235.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___414_11235.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___414_11235.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___414_11235.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___414_11235.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___414_11235.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___414_11235.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___414_11235.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___414_11235.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___414_11235.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___414_11235.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___414_11235.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___414_11235.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___414_11235.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___414_11235.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___414_11235.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___414_11235.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___414_11235.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___414_11235.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___414_11235.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___414_11235.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___414_11235.FStar_TypeChecker_Env.nbe)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____11232 with
               | (uvs1,t1) ->
                   ((let uu____11261 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____11261
                     then
                       let uu____11266 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____11268 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____11266
                         uu____11268
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____11212 with
            | (uvs1,t1) ->
                let uu____11303 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____11303 with
                 | (uvs2,t2) ->
                     ([(let uu___415_11333 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___415_11333.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___415_11333.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___415_11333.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___415_11333.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____11337 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____11337 with
            | (e1,c,g1) ->
                let uu____11357 =
                  let uu____11364 =
                    let uu____11367 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____11367  in
                  let uu____11368 =
                    let uu____11373 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____11373)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____11364 uu____11368
                   in
                (match uu____11357 with
                 | (e2,uu____11385,g) ->
                     ((let uu____11388 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____11388);
                      (let se1 =
                         let uu___416_11390 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___416_11390.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___416_11390.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___416_11390.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___416_11390.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____11402 = FStar_Options.debug_any ()  in
             if uu____11402
             then
               let uu____11405 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____11407 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____11405
                 uu____11407
             else ());
            (let uu____11412 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____11412 with
             | (t1,uu____11430,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____11444 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____11444 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____11447 =
                              let uu____11453 =
                                let uu____11455 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____11457 =
                                  let uu____11459 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____11459
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____11455 uu____11457
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____11453)
                               in
                            FStar_Errors.raise_error uu____11447 r
                        | uu____11471 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___417_11476 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___417_11476.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___417_11476.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___417_11476.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___417_11476.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___417_11476.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___417_11476.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___417_11476.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___417_11476.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___417_11476.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___417_11476.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___417_11476.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___417_11476.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___417_11476.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___417_11476.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___417_11476.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___417_11476.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___417_11476.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___417_11476.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___417_11476.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___417_11476.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___417_11476.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___417_11476.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___417_11476.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___417_11476.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___417_11476.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___417_11476.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___417_11476.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___417_11476.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___417_11476.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___417_11476.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___417_11476.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___417_11476.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___417_11476.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___417_11476.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___417_11476.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___417_11476.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___417_11476.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___417_11476.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___417_11476.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___417_11476.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___417_11476.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___417_11476.FStar_TypeChecker_Env.nbe)
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
                 let uu____11544 =
                   let uu____11546 =
                     let uu____11555 = drop_logic val_q  in
                     let uu____11558 = drop_logic q'  in
                     (uu____11555, uu____11558)  in
                   match uu____11546 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____11544
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____11585 =
                      let uu____11591 =
                        let uu____11593 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____11595 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____11597 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____11593 uu____11595 uu____11597
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____11591)
                       in
                    FStar_Errors.raise_error uu____11585 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____11634 =
                   let uu____11635 = FStar_Syntax_Subst.compress def  in
                   uu____11635.FStar_Syntax_Syntax.n  in
                 match uu____11634 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____11647,uu____11648) -> binders
                 | uu____11673 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____11685;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____11790) -> val_bs1
                     | (uu____11821,[]) -> val_bs1
                     | ((body_bv,uu____11853)::bt,(val_bv,aqual)::vt) ->
                         let uu____11910 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____11934) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___418_11948 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___419_11951 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___419_11951.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___418_11948.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___418_11948.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____11910
                      in
                   let uu____11958 =
                     let uu____11965 =
                       let uu____11966 =
                         let uu____11981 = rename_binders1 def_bs val_bs  in
                         (uu____11981, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____11966  in
                     FStar_Syntax_Syntax.mk uu____11965  in
                   uu____11958 FStar_Pervasives_Native.None r1
               | uu____12003 -> typ1  in
             let uu___420_12004 = lb  in
             let uu____12005 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___420_12004.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___420_12004.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____12005;
               FStar_Syntax_Syntax.lbeff =
                 (uu___420_12004.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___420_12004.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___420_12004.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___420_12004.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____12008 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____12063  ->
                     fun lb  ->
                       match uu____12063 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____12109 =
                             let uu____12121 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____12121 with
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
                                   | uu____12201 ->
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
                                  (let uu____12248 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____12248, quals_opt1)))
                              in
                           (match uu____12109 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____12008 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____12352 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___376_12358  ->
                                match uu___376_12358 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____12363 -> false))
                         in
                      if uu____12352
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____12376 =
                    let uu____12383 =
                      let uu____12384 =
                        let uu____12398 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____12398)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____12384  in
                    FStar_Syntax_Syntax.mk uu____12383  in
                  uu____12376 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___421_12420 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___421_12420.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___421_12420.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___421_12420.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___421_12420.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___421_12420.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___421_12420.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___421_12420.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___421_12420.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___421_12420.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___421_12420.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___421_12420.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___421_12420.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___421_12420.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___421_12420.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___421_12420.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___421_12420.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___421_12420.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___421_12420.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___421_12420.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___421_12420.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___421_12420.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___421_12420.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___421_12420.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___421_12420.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___421_12420.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___421_12420.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___421_12420.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___421_12420.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___421_12420.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___421_12420.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___421_12420.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___421_12420.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___421_12420.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___421_12420.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___421_12420.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___421_12420.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___421_12420.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___421_12420.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___421_12420.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___421_12420.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___421_12420.FStar_TypeChecker_Env.nbe)
                  }  in
                let e1 =
                  let uu____12423 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____12423
                  then
                    let drop_lbtyp e_lax =
                      let uu____12432 =
                        let uu____12433 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____12433.FStar_Syntax_Syntax.n  in
                      match uu____12432 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____12455 =
                              let uu____12456 = FStar_Syntax_Subst.compress e
                                 in
                              uu____12456.FStar_Syntax_Syntax.n  in
                            match uu____12455 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____12460,lb1::[]),uu____12462) ->
                                let uu____12478 =
                                  let uu____12479 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____12479.FStar_Syntax_Syntax.n  in
                                (match uu____12478 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____12484 -> false)
                            | uu____12486 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___422_12490 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___423_12505 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___423_12505.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___423_12505.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___423_12505.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___423_12505.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___423_12505.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___423_12505.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___422_12490.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___422_12490.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____12508 -> e_lax  in
                    let e1 =
                      let uu____12510 =
                        let uu____12511 =
                          let uu____12512 =
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              (let uu___424_12521 = env'  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___424_12521.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___424_12521.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___424_12521.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___424_12521.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___424_12521.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___424_12521.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___424_12521.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___424_12521.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___424_12521.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___424_12521.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___424_12521.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___424_12521.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___424_12521.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___424_12521.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___424_12521.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___424_12521.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___424_12521.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___424_12521.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___424_12521.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___424_12521.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___424_12521.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 = true;
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___424_12521.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___424_12521.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___424_12521.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___424_12521.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___424_12521.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___424_12521.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___424_12521.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___424_12521.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___424_12521.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___424_12521.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___424_12521.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___424_12521.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___424_12521.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___424_12521.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___424_12521.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___424_12521.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___424_12521.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___424_12521.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___424_12521.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___424_12521.FStar_TypeChecker_Env.nbe)
                               }) e
                             in
                          FStar_All.pipe_right uu____12512
                            (fun uu____12534  ->
                               match uu____12534 with
                               | (e1,uu____12542,uu____12543) -> e1)
                           in
                        FStar_All.pipe_right uu____12511
                          (FStar_TypeChecker_Normalize.remove_uvar_solutions
                             env')
                         in
                      FStar_All.pipe_right uu____12510 drop_lbtyp  in
                    ((let uu____12545 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "TwoPhases")
                         in
                      if uu____12545
                      then
                        let uu____12550 =
                          FStar_Syntax_Print.term_to_string e1  in
                        FStar_Util.print1 "Let binding after phase 1: %s\n"
                          uu____12550
                      else ());
                     e1)
                  else e  in
                let uu____12557 =
                  let uu____12566 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____12566 with
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
                (match uu____12557 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___425_12671 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___425_12671.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___425_12671.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___425_12671.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___425_12671.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___426_12684 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___426_12684.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___426_12684.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___426_12684.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___426_12684.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___426_12684.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___426_12684.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____12685 =
                       let uu____12697 =
                         FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env'
                           e1
                          in
                       match uu____12697 with
                       | ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                            FStar_Syntax_Syntax.pos = uu____12717;
                            FStar_Syntax_Syntax.vars = uu____12718;_},uu____12719,g)
                           when FStar_TypeChecker_Env.is_trivial g ->
                           let lbs2 =
                             let uu____12749 =
                               FStar_All.pipe_right
                                 (FStar_Pervasives_Native.snd lbs1)
                                 (FStar_List.map rename_parameters)
                                in
                             ((FStar_Pervasives_Native.fst lbs1),
                               uu____12749)
                              in
                           let lbs3 =
                             let uu____12773 =
                               match post_tau with
                               | FStar_Pervasives_Native.Some tau ->
                                   FStar_List.map (postprocess_lb tau)
                                     (FStar_Pervasives_Native.snd lbs2)
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.snd lbs2
                                in
                             ((FStar_Pervasives_Native.fst lbs2),
                               uu____12773)
                              in
                           let quals1 =
                             match e2.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_meta
                                 (uu____12796,FStar_Syntax_Syntax.Meta_desugared
                                  (FStar_Syntax_Syntax.Masked_effect ))
                                 -> FStar_Syntax_Syntax.HasMaskedEffect ::
                                 quals
                             | uu____12801 -> quals  in
                           ((let uu___427_12810 = se1  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_let (lbs3, lids));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___427_12810.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals = quals1;
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___427_12810.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___427_12810.FStar_Syntax_Syntax.sigattrs)
                             }), lbs3)
                       | uu____12813 ->
                           failwith
                             "impossible (typechecking should preserve Tm_let)"
                        in
                     (match uu____12685 with
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
                           (let uu____12869 = log env1  in
                            if uu____12869
                            then
                              let uu____12872 =
                                let uu____12874 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs1)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let should_log =
                                            let uu____12894 =
                                              let uu____12903 =
                                                let uu____12904 =
                                                  let uu____12907 =
                                                    FStar_Util.right
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  uu____12907.FStar_Syntax_Syntax.fv_name
                                                   in
                                                uu____12904.FStar_Syntax_Syntax.v
                                                 in
                                              FStar_TypeChecker_Env.try_lookup_val_decl
                                                env1 uu____12903
                                               in
                                            match uu____12894 with
                                            | FStar_Pervasives_Native.None 
                                                -> true
                                            | uu____12916 -> false  in
                                          if should_log
                                          then
                                            let uu____12928 =
                                              FStar_Syntax_Print.lbname_to_string
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            let uu____12930 =
                                              FStar_Syntax_Print.term_to_string
                                                lb.FStar_Syntax_Syntax.lbtyp
                                               in
                                            FStar_Util.format2 "let %s : %s"
                                              uu____12928 uu____12930
                                          else ""))
                                   in
                                FStar_All.pipe_right uu____12874
                                  (FStar_String.concat "\n")
                                 in
                              FStar_Util.print1 "%s\n" uu____12872
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
      (let uu____12982 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____12982
       then
         let uu____12985 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____12985
       else ());
      (let uu____12990 = get_fail_se se  in
       match uu____12990 with
       | FStar_Pervasives_Native.Some (uu____13011,false ) when
           let uu____13028 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____13028 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___428_13054 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___428_13054.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___428_13054.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___428_13054.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___428_13054.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___428_13054.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___428_13054.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___428_13054.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___428_13054.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___428_13054.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___428_13054.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___428_13054.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___428_13054.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___428_13054.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___428_13054.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___428_13054.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___428_13054.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___428_13054.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___428_13054.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___428_13054.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___428_13054.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___428_13054.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___428_13054.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___428_13054.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___428_13054.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___428_13054.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___428_13054.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___428_13054.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___428_13054.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___428_13054.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___428_13054.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___428_13054.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___428_13054.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___428_13054.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___428_13054.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___428_13054.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___428_13054.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___428_13054.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___428_13054.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___428_13054.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___428_13054.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___428_13054.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___428_13054.FStar_TypeChecker_Env.nbe)
               }
             else env1  in
           ((let uu____13059 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____13059
             then
               let uu____13062 =
                 let uu____13064 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____13064
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____13062
             else ());
            (let uu____13078 =
               FStar_Errors.catch_errors
                 (fun uu____13108  ->
                    FStar_Options.with_saved_options
                      (fun uu____13120  -> tc_decl' env' se))
                in
             match uu____13078 with
             | (errs,uu____13132) ->
                 ((let uu____13162 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____13162
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____13197 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____13197  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____13209 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____13220 =
                            let uu____13230 =
                              check_multi_contained errnos1 actual  in
                            match uu____13230 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")))
                             in
                          (match uu____13220 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____13295 =
                                   let uu____13301 =
                                     let uu____13303 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____13306 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____13309 =
                                       FStar_Util.string_of_int e  in
                                     let uu____13311 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____13313 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____13303 uu____13306 uu____13309
                                       uu____13311 uu____13313
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____13301)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____13295)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____13340 .
    'Auu____13340 ->
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
               (fun uu___377_13383  ->
                  match uu___377_13383 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____13386 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____13397) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____13405 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____13415 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____13420 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____13436 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____13462 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13488) ->
            let uu____13497 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13497
            then
              let for_export_bundle se1 uu____13534 =
                match uu____13534 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____13573,uu____13574) ->
                         let dec =
                           let uu___429_13584 = se1  in
                           let uu____13585 =
                             let uu____13586 =
                               let uu____13593 =
                                 let uu____13594 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____13594  in
                               (l, us, uu____13593)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____13586
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____13585;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___429_13584.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___429_13584.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___429_13584.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____13604,uu____13605,uu____13606) ->
                         let dec =
                           let uu___430_13614 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___430_13614.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___430_13614.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___430_13614.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____13619 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____13642,uu____13643,uu____13644) ->
            let uu____13645 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13645 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____13669 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____13669
            then
              ([(let uu___431_13688 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___431_13688.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___431_13688.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___431_13688.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____13691 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___378_13697  ->
                         match uu___378_13697 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____13700 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____13706 ->
                             true
                         | uu____13708 -> false))
                  in
               if uu____13691 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____13729 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____13734 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____13739 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13744 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13762) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____13776 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____13776
            then ([], hidden)
            else
              (let dec =
                 let uu____13797 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____13797;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____13808 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13808
            then
              let uu____13819 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___432_13833 = se  in
                        let uu____13834 =
                          let uu____13835 =
                            let uu____13842 =
                              let uu____13843 =
                                let uu____13846 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____13846.FStar_Syntax_Syntax.fv_name  in
                              uu____13843.FStar_Syntax_Syntax.v  in
                            (uu____13842, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____13835  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____13834;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___432_13833.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___432_13833.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___432_13833.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____13819, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____13869 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____13869
       then
         let uu____13872 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____13872
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____13877 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____13895 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____13912) -> z3_reset_options env
       | FStar_Syntax_Syntax.Sig_pragma uu____13916 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____13926 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____13926) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____13927,uu____13928,uu____13929) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_13934  ->
                   match uu___379_13934 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13937 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____13939,uu____13940) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_13949  ->
                   match uu___379_13949 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13952 -> false))
           -> env
       | uu____13954 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____14023 se =
        match uu____14023 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____14076 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____14076
              then
                let uu____14079 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____14079
              else ());
             (let uu____14084 = tc_decl env1 se  in
              match uu____14084 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14137 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14137
                             then
                               let uu____14141 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____14141
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____14157 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____14157
                             then
                               let uu____14161 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____14161
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
                    (let uu____14178 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____14178
                     then
                       let uu____14183 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____14192 =
                                  let uu____14194 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____14194 "\n"  in
                                Prims.strcat s uu____14192) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____14183
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____14204 =
                       let uu____14213 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____14213
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____14255 se1 =
                            match uu____14255 with
                            | (exports1,hidden1) ->
                                let uu____14283 = for_export env3 hidden1 se1
                                   in
                                (match uu____14283 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____14204 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____14437 = acc  in
        match uu____14437 with
        | (uu____14472,uu____14473,env1,uu____14475) ->
            let uu____14488 =
              FStar_Util.record_time
                (fun uu____14535  -> process_one_decl acc se)
               in
            (match uu____14488 with
             | (r,ms_elapsed) ->
                 ((let uu____14601 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____14601
                   then
                     let uu____14605 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____14607 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____14605 uu____14607
                   else ());
                  r))
         in
      let uu____14612 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____14612 with
      | (ses1,exports,env1,uu____14660) ->
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
          let uu___433_14698 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___433_14698.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___433_14698.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___433_14698.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___433_14698.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___433_14698.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___433_14698.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___433_14698.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___433_14698.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___433_14698.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___433_14698.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___433_14698.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___433_14698.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___433_14698.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___433_14698.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___433_14698.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___433_14698.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___433_14698.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___433_14698.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___433_14698.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___433_14698.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___433_14698.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___433_14698.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___433_14698.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___433_14698.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___433_14698.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___433_14698.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___433_14698.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___433_14698.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___433_14698.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___433_14698.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___433_14698.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___433_14698.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___433_14698.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___433_14698.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___433_14698.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___433_14698.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___433_14698.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___433_14698.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___433_14698.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___433_14698.FStar_TypeChecker_Env.nbe)
          }  in
        let check_term lid univs1 t =
          let uu____14718 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____14718 with
          | (univs2,t1) ->
              ((let uu____14726 =
                  let uu____14728 =
                    let uu____14734 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____14734  in
                  FStar_All.pipe_left uu____14728
                    (FStar_Options.Other "Exports")
                   in
                if uu____14726
                then
                  let uu____14738 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____14740 =
                    let uu____14742 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____14742
                      (FStar_String.concat ", ")
                     in
                  let uu____14759 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____14738 uu____14740 uu____14759
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____14765 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____14765 (fun a1  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____14791 =
             let uu____14793 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____14795 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____14793 uu____14795
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____14791);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14806) ->
              let uu____14815 =
                let uu____14817 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14817  in
              if uu____14815
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____14831,uu____14832) ->
              let t =
                let uu____14844 =
                  let uu____14851 =
                    let uu____14852 =
                      let uu____14867 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____14867)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____14852  in
                  FStar_Syntax_Syntax.mk uu____14851  in
                uu____14844 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____14886,uu____14887,uu____14888) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____14898 =
                let uu____14900 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14900  in
              if uu____14898 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____14908,lbs),uu____14910) ->
              let uu____14921 =
                let uu____14923 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14923  in
              if uu____14921
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
              let uu____14946 =
                let uu____14948 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14948  in
              if uu____14946
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____14969 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____14970 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14977 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____14978 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____14979 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____14986 -> ()  in
        let uu____14987 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____14987 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____15093) -> true
             | uu____15095 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____15125 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____15164 ->
                   let uu____15165 =
                     let uu____15172 =
                       let uu____15173 =
                         let uu____15188 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____15188)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____15173  in
                     FStar_Syntax_Syntax.mk uu____15172  in
                   uu____15165 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____15208,uu____15209) ->
            let s1 =
              let uu___434_15219 = s  in
              let uu____15220 =
                let uu____15221 =
                  let uu____15228 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____15228)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____15221  in
              let uu____15229 =
                let uu____15232 =
                  let uu____15235 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____15235  in
                FStar_Syntax_Syntax.Assumption :: uu____15232  in
              {
                FStar_Syntax_Syntax.sigel = uu____15220;
                FStar_Syntax_Syntax.sigrng =
                  (uu___434_15219.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____15229;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___434_15219.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___434_15219.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____15238 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____15263 lbdef =
        match uu____15263 with
        | (uvs,t) ->
            let attrs =
              let uu____15274 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____15274
              then
                let uu____15279 =
                  let uu____15280 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____15280
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____15279 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___435_15283 = s  in
            let uu____15284 =
              let uu____15287 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____15287  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___435_15283.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____15284;
              FStar_Syntax_Syntax.sigmeta =
                (uu___435_15283.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____15305 -> failwith "Impossible!"  in
        let c_opt =
          let uu____15312 = FStar_Syntax_Util.is_unit t  in
          if uu____15312
          then
            let uu____15319 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____15319
          else
            (let uu____15326 =
               let uu____15327 = FStar_Syntax_Subst.compress t  in
               uu____15327.FStar_Syntax_Syntax.n  in
             match uu____15326 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____15334,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____15358 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____15370 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____15370
            then false
            else
              (let uu____15377 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____15377
               then true
               else
                 (let uu____15384 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____15384))
         in
      let extract_sigelt s =
        (let uu____15396 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____15396
         then
           let uu____15399 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____15399
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____15406 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____15426 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____15445 ->
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
                             (lid,uu____15491,uu____15492,uu____15493,uu____15494,uu____15495)
                             ->
                             ((let uu____15505 =
                                 let uu____15508 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____15508  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____15505);
                              (let uu____15601 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____15601 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____15605,uu____15606,uu____15607,uu____15608,uu____15609)
                             ->
                             ((let uu____15617 =
                                 let uu____15620 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____15620  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____15617);
                              sigelts1)
                         | uu____15713 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____15722 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15722
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____15732 =
                    let uu___436_15733 = s  in
                    let uu____15734 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___436_15733.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___436_15733.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15734;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___436_15733.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___436_15733.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15732])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____15745 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15745
             then []
             else
               (let uu____15752 = lbs  in
                match uu____15752 with
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
                        (fun uu____15814  ->
                           match uu____15814 with
                           | (uu____15822,t,uu____15824) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____15841  ->
                             match uu____15841 with
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
                           (fun uu____15868  ->
                              match uu____15868 with
                              | (uu____15876,t,uu____15878) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____15890,uu____15891) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____15899 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____15950 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____15950) uu____15899
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____15954 =
                    let uu___437_15955 = s  in
                    let uu____15956 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___437_15955.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___437_15955.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15956;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___437_15955.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___437_15955.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15954]
                else [])
             else
               (let uu____15963 =
                  let uu___438_15964 = s  in
                  let uu____15965 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___438_15964.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___438_15964.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____15965;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___438_15964.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___438_15964.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____15963])
         | FStar_Syntax_Syntax.Sig_new_effect uu____15968 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____15969 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15970 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____15983 -> [s])
         in
      let uu___439_15984 = m  in
      let uu____15985 =
        let uu____15986 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____15986 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___439_15984.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____15985;
        FStar_Syntax_Syntax.exports =
          (uu___439_15984.FStar_Syntax_Syntax.exports);
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
        (fun uu____16037  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____16085  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             solver.FStar_TypeChecker_Env.refresh (); env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____16101 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____16101
  
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
      (let uu____16190 = FStar_Options.debug_any ()  in
       if uu____16190
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
         let uu___440_16206 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___440_16206.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___440_16206.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___440_16206.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___440_16206.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___440_16206.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___440_16206.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___440_16206.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___440_16206.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___440_16206.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___440_16206.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___440_16206.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___440_16206.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___440_16206.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___440_16206.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___440_16206.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___440_16206.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___440_16206.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___440_16206.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___440_16206.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___440_16206.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___440_16206.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___440_16206.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___440_16206.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___440_16206.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___440_16206.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___440_16206.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___440_16206.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___440_16206.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___440_16206.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___440_16206.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___440_16206.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___440_16206.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___440_16206.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___440_16206.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___440_16206.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___440_16206.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___440_16206.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___440_16206.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___440_16206.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___440_16206.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___440_16206.FStar_TypeChecker_Env.nbe)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____16208 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____16208 with
       | (ses,exports,env3) ->
           ((let uu___441_16241 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___441_16241.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___441_16241.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___441_16241.FStar_Syntax_Syntax.is_interface)
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
        let uu____16270 = tc_decls env decls  in
        match uu____16270 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___442_16301 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___442_16301.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___442_16301.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___442_16301.FStar_Syntax_Syntax.is_interface)
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
        let uu____16362 = tc_partial_modul env01 m  in
        match uu____16362 with
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
                (let uu____16399 = FStar_Errors.get_err_count ()  in
                 uu____16399 = (Prims.parse_int "0"))
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____16410 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____16410
                then
                  let uu____16414 =
                    let uu____16416 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16416 then "" else " (in lax mode) "  in
                  let uu____16424 =
                    let uu____16426 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16426
                    then
                      let uu____16430 =
                        let uu____16432 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.strcat uu____16432 "\n"  in
                      Prims.strcat "\nfrom: " uu____16430
                    else ""  in
                  let uu____16439 =
                    let uu____16441 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16441
                    then
                      let uu____16445 =
                        let uu____16447 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.strcat uu____16447 "\n"  in
                      Prims.strcat "\nto: " uu____16445
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____16414
                    uu____16424 uu____16439
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.strcat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___443_16461 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___443_16461.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___443_16461.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___443_16461.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___443_16461.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___443_16461.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___443_16461.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___443_16461.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___443_16461.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___443_16461.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___443_16461.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___443_16461.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___443_16461.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___443_16461.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___443_16461.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___443_16461.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___443_16461.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___443_16461.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___443_16461.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___443_16461.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___443_16461.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___443_16461.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___443_16461.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___443_16461.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___443_16461.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___443_16461.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___443_16461.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___443_16461.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___443_16461.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___443_16461.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___443_16461.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___443_16461.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___443_16461.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___443_16461.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___443_16461.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___443_16461.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___443_16461.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___443_16461.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___443_16461.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___443_16461.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___443_16461.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___443_16461.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___443_16461.FStar_TypeChecker_Env.nbe)
                    }  in
                  let en02 =
                    let uu___444_16463 = en01  in
                    let uu____16464 =
                      let uu____16479 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____16479, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___444_16463.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___444_16463.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___444_16463.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___444_16463.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___444_16463.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___444_16463.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___444_16463.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___444_16463.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___444_16463.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___444_16463.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___444_16463.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___444_16463.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___444_16463.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___444_16463.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___444_16463.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___444_16463.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___444_16463.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___444_16463.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___444_16463.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___444_16463.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___444_16463.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___444_16463.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___444_16463.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___444_16463.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___444_16463.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___444_16463.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___444_16463.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___444_16463.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___444_16463.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___444_16463.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___444_16463.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____16464;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___444_16463.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___444_16463.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___444_16463.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___444_16463.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___444_16463.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___444_16463.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___444_16463.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___444_16463.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___444_16463.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___444_16463.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___444_16463.FStar_TypeChecker_Env.nbe)
                    }  in
                  let uu____16525 =
                    let uu____16527 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____16527  in
                  if uu____16525
                  then
                    ((let uu____16531 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____16531 (fun a2  -> ()));
                     z3_reset_options en02)
                  else en02  in
                let uu____16535 = tc_modul en0 modul_iface true  in
                match uu____16535 with
                | (modul_iface1,env) ->
                    ((let uu___445_16548 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___445_16548.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___445_16548.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___445_16548.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___446_16552 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___446_16552.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___446_16552.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___446_16552.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____16555 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____16555 FStar_Util.smap_clear);
               (let uu____16591 =
                  ((let uu____16595 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____16595) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____16598 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____16598)
                   in
                if uu____16591 then check_exports env modul exports else ());
               (let uu____16604 =
                  pop_context env
                    (Prims.strcat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____16604 (fun a3  -> ()));
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
                 env modul;
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ();
               (let uu____16609 =
                  let uu____16611 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____16611  in
                if uu____16609
                then
                  let uu____16614 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____16614 (fun a4  -> ())
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
        let uu____16631 =
          let uu____16633 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____16633  in
        push_context env uu____16631  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____16654 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____16665 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____16665 with | (uu____16672,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____16697 = FStar_Options.debug_any ()  in
         if uu____16697
         then
           let uu____16700 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____16700
         else ());
        (let uu____16712 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____16712
         then
           let uu____16715 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____16715
         else ());
        (let env1 =
           let uu___447_16721 = env  in
           let uu____16722 =
             let uu____16724 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____16724  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___447_16721.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___447_16721.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___447_16721.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___447_16721.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___447_16721.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___447_16721.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___447_16721.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___447_16721.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___447_16721.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___447_16721.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___447_16721.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___447_16721.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___447_16721.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___447_16721.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___447_16721.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___447_16721.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___447_16721.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___447_16721.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___447_16721.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___447_16721.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____16722;
             FStar_TypeChecker_Env.lax_universes =
               (uu___447_16721.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___447_16721.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___447_16721.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___447_16721.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___447_16721.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___447_16721.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___447_16721.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___447_16721.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___447_16721.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___447_16721.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___447_16721.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___447_16721.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___447_16721.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___447_16721.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___447_16721.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___447_16721.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___447_16721.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___447_16721.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___447_16721.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___447_16721.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___447_16721.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___447_16721.FStar_TypeChecker_Env.nbe)
           }  in
         let uu____16726 = tc_modul env1 m b  in
         match uu____16726 with
         | (m1,env2) ->
             ((let uu____16738 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____16738
               then
                 let uu____16741 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____16741
               else ());
              (let uu____16747 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____16747
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
                         let uu____16785 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____16785 with
                         | (univnames1,e) ->
                             let uu___448_16792 = lb  in
                             let uu____16793 =
                               let uu____16796 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____16796 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___448_16792.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___448_16792.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___448_16792.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___448_16792.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16793;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___448_16792.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___448_16792.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___449_16797 = se  in
                       let uu____16798 =
                         let uu____16799 =
                           let uu____16806 =
                             let uu____16807 = FStar_List.map update lbs  in
                             (b1, uu____16807)  in
                           (uu____16806, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____16799  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____16798;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___449_16797.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___449_16797.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___449_16797.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___449_16797.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____16815 -> se  in
                 let normalized_module =
                   let uu___450_16817 = m1  in
                   let uu____16818 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___450_16817.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____16818;
                     FStar_Syntax_Syntax.exports =
                       (uu___450_16817.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___450_16817.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____16819 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____16819
               else ());
              (m1, env2)))
  
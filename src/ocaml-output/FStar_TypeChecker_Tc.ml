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
                                                let uu____1194 =
                                                  let uu____1201 =
                                                    FStar_Syntax_Syntax.tabbrev
                                                      FStar_Parser_Const.range_lid
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____1201
                                                   in
                                                [uu____1194]  in
                                              FStar_Syntax_Util.abs
                                                uu____1193 bind_wp
                                                FStar_Pervasives_Native.None
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
                                         let uu____1253 =
                                           if
                                             ed1.FStar_Syntax_Syntax.spec_dm4f
                                           then
                                             let uu____1275 =
                                               elaborate_and_star dmff_env1
                                                 effect_binders1 []
                                                 (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                                in
                                             match uu____1275 with
                                             | (dmff_env2,uu____1301,return_wp,return_elab)
                                                 ->
                                                 (dmff_env2, return_wp,
                                                   return_elab)
                                           else
                                             (dmff_env1,
                                               (FStar_Pervasives_Native.snd
                                                  (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret),
                                               (FStar_Pervasives_Native.snd
                                                  (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret))
                                            in
                                         (match uu____1253 with
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
                                                  let uu____1356 =
                                                    FStar_Syntax_Syntax.new_bv
                                                      FStar_Pervasives_Native.None
                                                      FStar_Syntax_Util.ktype
                                                     in
                                                  FStar_Syntax_Syntax.mk_binder
                                                    uu____1356
                                                   in
                                                let t_b1 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    (FStar_Pervasives_Native.fst
                                                       b1)
                                                   in
                                                let bwp =
                                                  let uu____1361 =
                                                    let uu____1362 =
                                                      pure_wp_type t_b1  in
                                                    FStar_Syntax_Syntax.new_bv
                                                      FStar_Pervasives_Native.None
                                                      uu____1362
                                                     in
                                                  FStar_Syntax_Syntax.mk_binder
                                                    uu____1361
                                                   in
                                                let t_wp =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    (FStar_Pervasives_Native.fst
                                                       bwp)
                                                   in
                                                let b2 =
                                                  let uu____1367 =
                                                    FStar_Syntax_Syntax.new_bv
                                                      FStar_Pervasives_Native.None
                                                      t_b1
                                                     in
                                                  FStar_Syntax_Syntax.mk_binder
                                                    uu____1367
                                                   in
                                                let t_b2 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    (FStar_Pervasives_Native.fst
                                                       b2)
                                                   in
                                                let t =
                                                  let uu____1372 =
                                                    let uu____1373 =
                                                      let uu____1384 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t_b1
                                                         in
                                                      [uu____1384]  in
                                                    FStar_Syntax_Util.mk_app
                                                      wp_type1 uu____1373
                                                     in
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 uu____1372
                                                   in
                                                let uu____1409 =
                                                  FStar_Syntax_Util.arrow_formals_comp
                                                    t
                                                   in
                                                match uu____1409 with
                                                | (bs,r) ->
                                                    let t00 =
                                                      let uu____1445 =
                                                        let uu____1456 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            t_b1
                                                           in
                                                        let uu____1463 =
                                                          let uu____1472 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              t_b2
                                                             in
                                                          let uu____1479 =
                                                            FStar_List.map
                                                              (fun uu____1504
                                                                  ->
                                                                 match uu____1504
                                                                 with
                                                                 | (bv,q) ->
                                                                    let uu____1523
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv  in
                                                                    (uu____1523,
                                                                    q)) bs
                                                             in
                                                          uu____1472 ::
                                                            uu____1479
                                                           in
                                                        uu____1456 ::
                                                          uu____1463
                                                         in
                                                      FStar_Syntax_Util.mk_app
                                                        return_wp uu____1445
                                                       in
                                                    let t0 =
                                                      FStar_Syntax_Util.abs
                                                        [b2] t00
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    let t1 =
                                                      let uu____1556 =
                                                        let uu____1559 =
                                                          let uu____1570 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              t0
                                                             in
                                                          [uu____1570]  in
                                                        FStar_Syntax_Util.mk_app
                                                          t_wp uu____1559
                                                         in
                                                      FStar_Syntax_Util.abs
                                                        bs uu____1556
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
                                                    ((let uu____1618 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          (FStar_Options.Other
                                                             "ED")
                                                         in
                                                      if uu____1618
                                                      then
                                                        let uu____1623 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t21
                                                           in
                                                        FStar_Util.print1
                                                          "elaborated lift from PURE = %s\n"
                                                          uu____1623
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
                                                  (let uu____1653 =
                                                     let uu____1654 =
                                                       let uu____1655 =
                                                         let uu____1672 =
                                                           let uu____1683 =
                                                             FStar_Syntax_Util.args_of_binders
                                                               effect_binders1
                                                              in
                                                           FStar_Pervasives_Native.snd
                                                             uu____1683
                                                            in
                                                         (t, uu____1672)  in
                                                       FStar_Syntax_Syntax.Tm_app
                                                         uu____1655
                                                        in
                                                     mk1 uu____1654  in
                                                   FStar_Syntax_Subst.close
                                                     effect_binders1
                                                     uu____1653)
                                                 in
                                              let register name item =
                                                let uu____1717 =
                                                  let uu____1722 =
                                                    mk_lid name  in
                                                  let uu____1723 =
                                                    FStar_Syntax_Util.abs
                                                      effect_binders1 item
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  FStar_TypeChecker_Util.mk_toplevel_definition
                                                    env1 uu____1722
                                                    uu____1723
                                                   in
                                                match uu____1717 with
                                                | (sigelt,fv) ->
                                                    ((let uu____1727 =
                                                        let uu____1730 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____1730
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____1727);
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
                                              ((let uu____1828 =
                                                  let uu____1831 =
                                                    FStar_Syntax_Syntax.mk_sigelt
                                                      (FStar_Syntax_Syntax.Sig_pragma
                                                         (FStar_Syntax_Syntax.PushOptions
                                                            (FStar_Pervasives_Native.Some
                                                               "--admit_smt_queries true")))
                                                     in
                                                  let uu____1834 =
                                                    FStar_ST.op_Bang sigelts
                                                     in
                                                  uu____1831 :: uu____1834
                                                   in
                                                FStar_ST.op_Colon_Equals
                                                  sigelts uu____1828);
                                               (let return_elab1 =
                                                  register "return_elab"
                                                    return_elab
                                                   in
                                                (let uu____1930 =
                                                   let uu____1933 =
                                                     FStar_Syntax_Syntax.mk_sigelt
                                                       (FStar_Syntax_Syntax.Sig_pragma
                                                          FStar_Syntax_Syntax.PopOptions)
                                                      in
                                                   let uu____1934 =
                                                     FStar_ST.op_Bang sigelts
                                                      in
                                                   uu____1933 :: uu____1934
                                                    in
                                                 FStar_ST.op_Colon_Equals
                                                   sigelts uu____1930);
                                                (let bind_wp1 =
                                                   register "bind_wp" bind_wp
                                                    in
                                                 (let uu____2030 =
                                                    let uu____2033 =
                                                      FStar_Syntax_Syntax.mk_sigelt
                                                        (FStar_Syntax_Syntax.Sig_pragma
                                                           (FStar_Syntax_Syntax.PushOptions
                                                              (FStar_Pervasives_Native.Some
                                                                 "--admit_smt_queries true")))
                                                       in
                                                    let uu____2036 =
                                                      FStar_ST.op_Bang
                                                        sigelts
                                                       in
                                                    uu____2033 :: uu____2036
                                                     in
                                                  FStar_ST.op_Colon_Equals
                                                    sigelts uu____2030);
                                                 (let bind_elab1 =
                                                    register "bind_elab"
                                                      bind_elab
                                                     in
                                                  (let uu____2132 =
                                                     let uu____2135 =
                                                       FStar_Syntax_Syntax.mk_sigelt
                                                         (FStar_Syntax_Syntax.Sig_pragma
                                                            FStar_Syntax_Syntax.PopOptions)
                                                        in
                                                     let uu____2136 =
                                                       FStar_ST.op_Bang
                                                         sigelts
                                                        in
                                                     uu____2135 :: uu____2136
                                                      in
                                                   FStar_ST.op_Colon_Equals
                                                     sigelts uu____2132);
                                                  (let uu____2229 =
                                                     FStar_List.fold_left
                                                       (fun uu____2269  ->
                                                          fun action  ->
                                                            match uu____2269
                                                            with
                                                            | (dmff_env3,actions)
                                                                ->
                                                                let params_un
                                                                  =
                                                                  FStar_Syntax_Subst.open_binders
                                                                    action.FStar_Syntax_Syntax.action_params
                                                                   in
                                                                let uu____2290
                                                                  =
                                                                  let uu____2297
                                                                    =
                                                                    FStar_TypeChecker_DMFF.get_env
                                                                    dmff_env3
                                                                     in
                                                                  FStar_TypeChecker_TcTerm.tc_tparams
                                                                    uu____2297
                                                                    params_un
                                                                   in
                                                                (match uu____2290
                                                                 with
                                                                 | (action_params,env',uu____2306)
                                                                    ->
                                                                    let action_params1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____2332
                                                                     ->
                                                                    match uu____2332
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____2351
                                                                    =
                                                                    let uu___384_2352
                                                                    = bv  in
                                                                    let uu____2353
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___384_2352.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___384_2352.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____2353
                                                                    }  in
                                                                    (uu____2351,
                                                                    qual))
                                                                    action_params
                                                                     in
                                                                    let dmff_env'
                                                                    =
                                                                    FStar_TypeChecker_DMFF.set_env
                                                                    dmff_env3
                                                                    env'  in
                                                                    let uu____2359
                                                                    =
                                                                    elaborate_and_star
                                                                    dmff_env'
                                                                    effect_binders1
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                     in
                                                                    (match uu____2359
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
                                                                    uu____2402
                                                                    ->
                                                                    let uu____2403
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____2403
                                                                     in
                                                                    ((
                                                                    let uu____2407
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____2407
                                                                    then
                                                                    let uu____2412
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____2415
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____2418
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____2420
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____2412
                                                                    uu____2415
                                                                    uu____2418
                                                                    uu____2420
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
                                                                    let uu____2429
                                                                    =
                                                                    let uu____2432
                                                                    =
                                                                    let uu___385_2433
                                                                    = action
                                                                     in
                                                                    let uu____2434
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____2435
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___385_2433.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___385_2433.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___385_2433.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2434;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2435
                                                                    }  in
                                                                    uu____2432
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____2429))))))
                                                       (dmff_env2, [])
                                                       ed1.FStar_Syntax_Syntax.actions
                                                      in
                                                   match uu____2229 with
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
                                                              let uu____2484
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  a1
                                                                 in
                                                              let uu____2491
                                                                =
                                                                let uu____2500
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp
                                                                   in
                                                                [uu____2500]
                                                                 in
                                                              uu____2484 ::
                                                                uu____2491
                                                               in
                                                            let r =
                                                              let uu____2528
                                                                =
                                                                let uu____2531
                                                                  =
                                                                  let uu____2532
                                                                    =
                                                                    let uu____2533
                                                                    =
                                                                    let uu____2550
                                                                    =
                                                                    let uu____2561
                                                                    =
                                                                    let uu____2570
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    a1  in
                                                                    let uu____2573
                                                                    =
                                                                    FStar_Syntax_Syntax.as_implicit
                                                                    false  in
                                                                    (uu____2570,
                                                                    uu____2573)
                                                                     in
                                                                    [uu____2561]
                                                                     in
                                                                    (repr,
                                                                    uu____2550)
                                                                     in
                                                                    FStar_Syntax_Syntax.Tm_app
                                                                    uu____2533
                                                                     in
                                                                  mk1
                                                                    uu____2532
                                                                   in
                                                                let uu____2609
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    wp
                                                                   in
                                                                FStar_TypeChecker_DMFF.trans_F
                                                                  dmff_env3
                                                                  uu____2531
                                                                  uu____2609
                                                                 in
                                                              FStar_Syntax_Util.abs
                                                                binders
                                                                uu____2528
                                                                FStar_Pervasives_Native.None
                                                               in
                                                            r)
                                                          in
                                                       let uu____2610 =
                                                         recheck_debug "FC"
                                                           env1 repr1
                                                          in
                                                       let repr2 =
                                                         register "repr"
                                                           repr1
                                                          in
                                                       let uu____2614 =
                                                         let uu____2623 =
                                                           let uu____2624 =
                                                             let uu____2627 =
                                                               FStar_Syntax_Subst.compress
                                                                 wp_type1
                                                                in
                                                             FStar_All.pipe_left
                                                               FStar_Syntax_Util.unascribe
                                                               uu____2627
                                                              in
                                                           uu____2624.FStar_Syntax_Syntax.n
                                                            in
                                                         match uu____2623
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_abs
                                                             (type_param::effect_param,arrow1,uu____2641)
                                                             ->
                                                             let uu____2678 =
                                                               let uu____2699
                                                                 =
                                                                 FStar_Syntax_Subst.open_term
                                                                   (type_param
                                                                   ::
                                                                   effect_param)
                                                                   arrow1
                                                                  in
                                                               match uu____2699
                                                               with
                                                               | (b::bs,body)
                                                                   ->
                                                                   (b, bs,
                                                                    body)
                                                               | uu____2767
                                                                   ->
                                                                   failwith
                                                                    "Impossible : open_term nt preserving binders arity"
                                                                in
                                                             (match uu____2678
                                                              with
                                                              | (type_param1,effect_param1,arrow2)
                                                                  ->
                                                                  let uu____2832
                                                                    =
                                                                    let uu____2833
                                                                    =
                                                                    let uu____2836
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Util.unascribe
                                                                    uu____2836
                                                                     in
                                                                    uu____2833.FStar_Syntax_Syntax.n
                                                                     in
                                                                  (match uu____2832
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_arrow
                                                                    (wp_binders,c)
                                                                    ->
                                                                    let uu____2869
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                    (match uu____2869
                                                                    with
                                                                    | 
                                                                    (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2884
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2915
                                                                     ->
                                                                    match uu____2915
                                                                    with
                                                                    | 
                                                                    (bv,uu____2924)
                                                                    ->
                                                                    let uu____2929
                                                                    =
                                                                    let uu____2931
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2931
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2929
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____2884
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
                                                                    let uu____3023
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____3023
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____3033
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____3044
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____3044
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____3054
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____3057
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____3054,
                                                                    uu____3057)))
                                                                   | 
                                                                   uu____3072
                                                                    ->
                                                                    let uu____3073
                                                                    =
                                                                    let uu____3079
                                                                    =
                                                                    let uu____3081
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____3081
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____3079)
                                                                     in
                                                                    raise_error1
                                                                    uu____3073))
                                                         | uu____3093 ->
                                                             let uu____3094 =
                                                               let uu____3100
                                                                 =
                                                                 let uu____3102
                                                                   =
                                                                   FStar_Syntax_Print.term_to_string
                                                                    wp_type1
                                                                    in
                                                                 FStar_Util.format1
                                                                   "Impossible: pre/post abs %s"
                                                                   uu____3102
                                                                  in
                                                               (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                                 uu____3100)
                                                                in
                                                             raise_error1
                                                               uu____3094
                                                          in
                                                       (match uu____2614 with
                                                        | (pre,post) ->
                                                            ((let uu____3135
                                                                =
                                                                register
                                                                  "pre" pre
                                                                 in
                                                              ());
                                                             (let uu____3138
                                                                =
                                                                register
                                                                  "post" post
                                                                 in
                                                              ());
                                                             (let uu____3141
                                                                =
                                                                register "wp"
                                                                  wp_type1
                                                                 in
                                                              ());
                                                             (let ed2 =
                                                                let uu___386_3144
                                                                  = ed1  in
                                                                let uu____3145
                                                                  =
                                                                  FStar_Syntax_Subst.close_binders
                                                                    effect_binders1
                                                                   in
                                                                let uu____3146
                                                                  =
                                                                  let uu____3147
                                                                    =
                                                                    let uu____3148
                                                                    =
                                                                    apply_close
                                                                    return_wp1
                                                                     in
                                                                    ([],
                                                                    uu____3148)
                                                                     in
                                                                  let uu____3155
                                                                    =
                                                                    let uu____3156
                                                                    =
                                                                    apply_close
                                                                    bind_wp1
                                                                     in
                                                                    ([],
                                                                    uu____3156)
                                                                     in
                                                                  {
                                                                    FStar_Syntax_Syntax.monad_m
                                                                    =
                                                                    FStar_Syntax_Syntax.tun;
                                                                    FStar_Syntax_Syntax.monad_ret
                                                                    =
                                                                    uu____3147;
                                                                    FStar_Syntax_Syntax.monad_bind
                                                                    =
                                                                    uu____3155
                                                                  }  in
                                                                let uu____3163
                                                                  =
                                                                  FStar_Syntax_Subst.close
                                                                    effect_binders1
                                                                    effect_signature
                                                                   in
                                                                let uu____3164
                                                                  =
                                                                  let uu____3165
                                                                    =
                                                                    apply_close
                                                                    repr2  in
                                                                  let uu____3166
                                                                    =
                                                                    let uu____3167
                                                                    =
                                                                    apply_close
                                                                    return_elab1
                                                                     in
                                                                    ([],
                                                                    uu____3167)
                                                                     in
                                                                  let uu____3174
                                                                    =
                                                                    if
                                                                    ed1.FStar_Syntax_Syntax.spec_dm4f
                                                                    then
                                                                    let uu____3176
                                                                    =
                                                                    apply_close
                                                                    bind_elab1
                                                                     in
                                                                    ([],
                                                                    uu____3176)
                                                                    else
                                                                    (let uu____3185
                                                                    =
                                                                    let uu____3188
                                                                    =
                                                                    FStar_Ident.gen
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    [uu____3188]
                                                                     in
                                                                    let uu____3189
                                                                    =
                                                                    apply_close
                                                                    bind_elab1
                                                                     in
                                                                    (uu____3185,
                                                                    uu____3189))
                                                                     in
                                                                  {
                                                                    FStar_Syntax_Syntax.monad_m
                                                                    =
                                                                    uu____3165;
                                                                    FStar_Syntax_Syntax.monad_ret
                                                                    =
                                                                    uu____3166;
                                                                    FStar_Syntax_Syntax.monad_bind
                                                                    =
                                                                    uu____3174
                                                                  }  in
                                                                {
                                                                  FStar_Syntax_Syntax.cattributes
                                                                    =
                                                                    (
                                                                    uu___386_3144.FStar_Syntax_Syntax.cattributes);
                                                                  FStar_Syntax_Syntax.mname
                                                                    =
                                                                    (
                                                                    uu___386_3144.FStar_Syntax_Syntax.mname);
                                                                  FStar_Syntax_Syntax.univs
                                                                    =
                                                                    (
                                                                    uu___386_3144.FStar_Syntax_Syntax.univs);
                                                                  FStar_Syntax_Syntax.binders
                                                                    =
                                                                    uu____3145;
                                                                  FStar_Syntax_Syntax.spec
                                                                    =
                                                                    uu____3146;
                                                                  FStar_Syntax_Syntax.signature
                                                                    =
                                                                    uu____3163;
                                                                  FStar_Syntax_Syntax.if_then_else
                                                                    =
                                                                    (
                                                                    uu___386_3144.FStar_Syntax_Syntax.if_then_else);
                                                                  FStar_Syntax_Syntax.ite_wp
                                                                    =
                                                                    (
                                                                    uu___386_3144.FStar_Syntax_Syntax.ite_wp);
                                                                  FStar_Syntax_Syntax.stronger
                                                                    =
                                                                    (
                                                                    uu___386_3144.FStar_Syntax_Syntax.stronger);
                                                                  FStar_Syntax_Syntax.close_wp
                                                                    =
                                                                    (
                                                                    uu___386_3144.FStar_Syntax_Syntax.close_wp);
                                                                  FStar_Syntax_Syntax.assert_p
                                                                    =
                                                                    (
                                                                    uu___386_3144.FStar_Syntax_Syntax.assert_p);
                                                                  FStar_Syntax_Syntax.assume_p
                                                                    =
                                                                    (
                                                                    uu___386_3144.FStar_Syntax_Syntax.assume_p);
                                                                  FStar_Syntax_Syntax.null_wp
                                                                    =
                                                                    (
                                                                    uu___386_3144.FStar_Syntax_Syntax.null_wp);
                                                                  FStar_Syntax_Syntax.trivial
                                                                    =
                                                                    (
                                                                    uu___386_3144.FStar_Syntax_Syntax.trivial);
                                                                  FStar_Syntax_Syntax.repr
                                                                    =
                                                                    uu____3164;
                                                                  FStar_Syntax_Syntax.elaborated
                                                                    =
                                                                    (
                                                                    uu___386_3144.FStar_Syntax_Syntax.elaborated);
                                                                  FStar_Syntax_Syntax.spec_dm4f
                                                                    =
                                                                    (
                                                                    uu___386_3144.FStar_Syntax_Syntax.spec_dm4f);
                                                                  FStar_Syntax_Syntax.actions
                                                                    =
                                                                    actions1;
                                                                  FStar_Syntax_Syntax.eff_attrs
                                                                    =
                                                                    (
                                                                    uu___386_3144.FStar_Syntax_Syntax.eff_attrs)
                                                                }  in
                                                              let uu____3196
                                                                =
                                                                FStar_TypeChecker_DMFF.gen_wps_for_free
                                                                  env1
                                                                  effect_binders1
                                                                  a1 wp_a ed2
                                                                 in
                                                              match uu____3196
                                                              with
                                                              | (sigelts',ed3)
                                                                  ->
                                                                  ((let uu____3214
                                                                    =
                                                                    FStar_TypeChecker_Env.debug
                                                                    env1
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____3214
                                                                    then
                                                                    let uu____3218
                                                                    =
                                                                    FStar_Syntax_Print.eff_decl_to_string
                                                                    ed3  in
                                                                    FStar_Util.print_string
                                                                    uu____3218
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
                                                                    let uu____3237
                                                                    =
                                                                    let uu____3240
                                                                    =
                                                                    let uu____3241
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____3241)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3240
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
                                                                    uu____3237;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                    let uu____3248
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____3248
                                                                    else
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____3251
                                                                    =
                                                                    let uu____3254
                                                                    =
                                                                    let uu____3257
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                    FStar_List.rev
                                                                    uu____3257
                                                                     in
                                                                    FStar_List.append
                                                                    uu____3254
                                                                    sigelts'
                                                                     in
                                                                    (uu____3251,
                                                                    ed3,
                                                                    lift_from_pure_opt)))))))))))))))))))
  
let tc_eff_decl :
  'Auu____3318 .
    FStar_TypeChecker_Env.env ->
      'Auu____3318 ->
        FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun se  ->
      fun ed  ->
        (let uu____3335 =
           FStar_TypeChecker_Env.debug env0 (FStar_Options.Other "ED")  in
         if uu____3335
         then
           let uu____3339 = FStar_Syntax_Print.eff_decl_to_string ed  in
           FStar_Util.print1 "initial eff_decl :\n\t%s\n" uu____3339
         else ());
        (let uu____3344 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____3344 with
         | (open_annotated_univs,annotated_univ_names) ->
             let open_univs n_binders t =
               let uu____3376 =
                 FStar_Syntax_Subst.shift_subst n_binders
                   open_annotated_univs
                  in
               FStar_Syntax_Subst.subst uu____3376 t  in
             let open_univs_binders n_binders bs =
               let uu____3392 =
                 FStar_Syntax_Subst.shift_subst n_binders
                   open_annotated_univs
                  in
               FStar_Syntax_Subst.subst_binders uu____3392 bs  in
             let n_effect_params =
               FStar_List.length ed.FStar_Syntax_Syntax.binders  in
             let signature = ed.FStar_Syntax_Syntax.signature  in
             let uu____3403 =
               let uu____3410 =
                 open_univs_binders (Prims.parse_int "0")
                   ed.FStar_Syntax_Syntax.binders
                  in
               let uu____3412 = open_univs n_effect_params signature  in
               FStar_Syntax_Subst.open_term' uu____3410 uu____3412  in
             (match uu____3403 with
              | (effect_params_un,signature_un,opening) ->
                  let env =
                    FStar_TypeChecker_Env.push_univ_vars env0
                      annotated_univ_names
                     in
                  let uu____3423 =
                    FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un
                     in
                  (match uu____3423 with
                   | (effect_params,env1,uu____3432) ->
                       let uu____3433 =
                         FStar_TypeChecker_TcTerm.tc_trivial_guard env1
                           signature_un
                          in
                       (match uu____3433 with
                        | (signature1,uu____3439) ->
                            let ed1 =
                              let uu___387_3441 = ed  in
                              {
                                FStar_Syntax_Syntax.cattributes =
                                  (uu___387_3441.FStar_Syntax_Syntax.cattributes);
                                FStar_Syntax_Syntax.mname =
                                  (uu___387_3441.FStar_Syntax_Syntax.mname);
                                FStar_Syntax_Syntax.univs =
                                  (uu___387_3441.FStar_Syntax_Syntax.univs);
                                FStar_Syntax_Syntax.binders = effect_params;
                                FStar_Syntax_Syntax.spec =
                                  (uu___387_3441.FStar_Syntax_Syntax.spec);
                                FStar_Syntax_Syntax.signature = signature1;
                                FStar_Syntax_Syntax.if_then_else =
                                  (uu___387_3441.FStar_Syntax_Syntax.if_then_else);
                                FStar_Syntax_Syntax.ite_wp =
                                  (uu___387_3441.FStar_Syntax_Syntax.ite_wp);
                                FStar_Syntax_Syntax.stronger =
                                  (uu___387_3441.FStar_Syntax_Syntax.stronger);
                                FStar_Syntax_Syntax.close_wp =
                                  (uu___387_3441.FStar_Syntax_Syntax.close_wp);
                                FStar_Syntax_Syntax.assert_p =
                                  (uu___387_3441.FStar_Syntax_Syntax.assert_p);
                                FStar_Syntax_Syntax.assume_p =
                                  (uu___387_3441.FStar_Syntax_Syntax.assume_p);
                                FStar_Syntax_Syntax.null_wp =
                                  (uu___387_3441.FStar_Syntax_Syntax.null_wp);
                                FStar_Syntax_Syntax.trivial =
                                  (uu___387_3441.FStar_Syntax_Syntax.trivial);
                                FStar_Syntax_Syntax.repr =
                                  (uu___387_3441.FStar_Syntax_Syntax.repr);
                                FStar_Syntax_Syntax.elaborated =
                                  (uu___387_3441.FStar_Syntax_Syntax.elaborated);
                                FStar_Syntax_Syntax.spec_dm4f =
                                  (uu___387_3441.FStar_Syntax_Syntax.spec_dm4f);
                                FStar_Syntax_Syntax.actions =
                                  (uu___387_3441.FStar_Syntax_Syntax.actions);
                                FStar_Syntax_Syntax.eff_attrs =
                                  (uu___387_3441.FStar_Syntax_Syntax.eff_attrs)
                              }  in
                            let ed2 =
                              match (effect_params, annotated_univ_names)
                              with
                              | ([],[]) -> ed1
                              | uu____3469 ->
                                  let op uu____3501 =
                                    match uu____3501 with
                                    | (us,t) ->
                                        let n_us = FStar_List.length us  in
                                        let uu____3521 =
                                          let uu____3522 =
                                            FStar_Syntax_Subst.shift_subst
                                              n_us opening
                                             in
                                          let uu____3531 = open_univs n_us t
                                             in
                                          FStar_Syntax_Subst.subst uu____3522
                                            uu____3531
                                           in
                                        (us, uu____3521)
                                     in
                                  let uu___388_3540 = ed1  in
                                  let uu____3541 =
                                    let uu____3542 =
                                      let uu____3543 =
                                        op
                                          ([],
                                            ((ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m))
                                         in
                                      FStar_Pervasives_Native.snd uu____3543
                                       in
                                    let uu____3554 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                       in
                                    let uu____3555 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                       in
                                    {
                                      FStar_Syntax_Syntax.monad_m =
                                        uu____3542;
                                      FStar_Syntax_Syntax.monad_ret =
                                        uu____3554;
                                      FStar_Syntax_Syntax.monad_bind =
                                        uu____3555
                                    }  in
                                  let uu____3556 =
                                    op ed1.FStar_Syntax_Syntax.if_then_else
                                     in
                                  let uu____3557 =
                                    op ed1.FStar_Syntax_Syntax.ite_wp  in
                                  let uu____3558 =
                                    op ed1.FStar_Syntax_Syntax.stronger  in
                                  let uu____3559 =
                                    op ed1.FStar_Syntax_Syntax.close_wp  in
                                  let uu____3560 =
                                    op ed1.FStar_Syntax_Syntax.assert_p  in
                                  let uu____3561 =
                                    op ed1.FStar_Syntax_Syntax.assume_p  in
                                  let uu____3562 =
                                    op ed1.FStar_Syntax_Syntax.null_wp  in
                                  let uu____3563 =
                                    op ed1.FStar_Syntax_Syntax.trivial  in
                                  let uu____3564 =
                                    let uu____3565 =
                                      let uu____3566 =
                                        op
                                          ([],
                                            ((ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m))
                                         in
                                      FStar_Pervasives_Native.snd uu____3566
                                       in
                                    let uu____3577 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                       in
                                    let uu____3578 =
                                      op
                                        (ed1.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                       in
                                    {
                                      FStar_Syntax_Syntax.monad_m =
                                        uu____3565;
                                      FStar_Syntax_Syntax.monad_ret =
                                        uu____3577;
                                      FStar_Syntax_Syntax.monad_bind =
                                        uu____3578
                                    }  in
                                  let uu____3579 =
                                    FStar_List.map
                                      (fun a  ->
                                         let uu___389_3587 = a  in
                                         let uu____3588 =
                                           let uu____3589 =
                                             op
                                               ((a.FStar_Syntax_Syntax.action_univs),
                                                 (a.FStar_Syntax_Syntax.action_defn))
                                              in
                                           FStar_Pervasives_Native.snd
                                             uu____3589
                                            in
                                         let uu____3600 =
                                           let uu____3601 =
                                             op
                                               ((a.FStar_Syntax_Syntax.action_univs),
                                                 (a.FStar_Syntax_Syntax.action_typ))
                                              in
                                           FStar_Pervasives_Native.snd
                                             uu____3601
                                            in
                                         {
                                           FStar_Syntax_Syntax.action_name =
                                             (uu___389_3587.FStar_Syntax_Syntax.action_name);
                                           FStar_Syntax_Syntax.action_unqualified_name
                                             =
                                             (uu___389_3587.FStar_Syntax_Syntax.action_unqualified_name);
                                           FStar_Syntax_Syntax.action_univs =
                                             (uu___389_3587.FStar_Syntax_Syntax.action_univs);
                                           FStar_Syntax_Syntax.action_params
                                             =
                                             (uu___389_3587.FStar_Syntax_Syntax.action_params);
                                           FStar_Syntax_Syntax.action_defn =
                                             uu____3588;
                                           FStar_Syntax_Syntax.action_typ =
                                             uu____3600
                                         }) ed1.FStar_Syntax_Syntax.actions
                                     in
                                  {
                                    FStar_Syntax_Syntax.cattributes =
                                      (uu___388_3540.FStar_Syntax_Syntax.cattributes);
                                    FStar_Syntax_Syntax.mname =
                                      (uu___388_3540.FStar_Syntax_Syntax.mname);
                                    FStar_Syntax_Syntax.univs =
                                      annotated_univ_names;
                                    FStar_Syntax_Syntax.binders =
                                      (uu___388_3540.FStar_Syntax_Syntax.binders);
                                    FStar_Syntax_Syntax.spec = uu____3541;
                                    FStar_Syntax_Syntax.signature =
                                      (uu___388_3540.FStar_Syntax_Syntax.signature);
                                    FStar_Syntax_Syntax.if_then_else =
                                      uu____3556;
                                    FStar_Syntax_Syntax.ite_wp = uu____3557;
                                    FStar_Syntax_Syntax.stronger = uu____3558;
                                    FStar_Syntax_Syntax.close_wp = uu____3559;
                                    FStar_Syntax_Syntax.assert_p = uu____3560;
                                    FStar_Syntax_Syntax.assume_p = uu____3561;
                                    FStar_Syntax_Syntax.null_wp = uu____3562;
                                    FStar_Syntax_Syntax.trivial = uu____3563;
                                    FStar_Syntax_Syntax.repr = uu____3564;
                                    FStar_Syntax_Syntax.elaborated =
                                      (uu___388_3540.FStar_Syntax_Syntax.elaborated);
                                    FStar_Syntax_Syntax.spec_dm4f =
                                      (uu___388_3540.FStar_Syntax_Syntax.spec_dm4f);
                                    FStar_Syntax_Syntax.actions = uu____3579;
                                    FStar_Syntax_Syntax.eff_attrs =
                                      (uu___388_3540.FStar_Syntax_Syntax.eff_attrs)
                                  }
                               in
                            ((let uu____3613 =
                                FStar_TypeChecker_Env.debug env0
                                  (FStar_Options.Other "ED")
                                 in
                              if uu____3613
                              then
                                let uu____3617 =
                                  FStar_Syntax_Print.eff_decl_to_string ed2
                                   in
                                FStar_Util.print1
                                  "eff_decl after opening:\n\t%s\n"
                                  uu____3617
                              else ());
                             (let wp_with_fresh_result_type env2 mname
                                signature2 =
                                let fail1 t =
                                  let uu____3656 =
                                    FStar_TypeChecker_Err.unexpected_signature_for_monad
                                      env2 mname t
                                     in
                                  let uu____3662 =
                                    FStar_Ident.range_of_lid mname  in
                                  FStar_Errors.raise_error uu____3656
                                    uu____3662
                                   in
                                let uu____3669 =
                                  let uu____3670 =
                                    FStar_Syntax_Subst.compress signature2
                                     in
                                  uu____3670.FStar_Syntax_Syntax.n  in
                                match uu____3669 with
                                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                    let bs1 =
                                      FStar_Syntax_Subst.open_binders bs  in
                                    (match bs1 with
                                     | (a,uu____3709)::(wp,uu____3711)::[] ->
                                         (a, (wp.FStar_Syntax_Syntax.sort))
                                     | uu____3740 -> fail1 signature2)
                                | uu____3741 -> fail1 signature2  in
                              let uu____3742 =
                                wp_with_fresh_result_type env1
                                  ed2.FStar_Syntax_Syntax.mname signature1
                                 in
                              match uu____3742 with
                              | (a,wp_a) ->
                                  let fresh_effect_signature uu____3766 =
                                    match annotated_univ_names with
                                    | [] ->
                                        let uu____3773 =
                                          FStar_TypeChecker_TcTerm.tc_trivial_guard
                                            env1 signature_un
                                           in
                                        (match uu____3773 with
                                         | (signature2,uu____3785) ->
                                             wp_with_fresh_result_type env1
                                               ed2.FStar_Syntax_Syntax.mname
                                               signature2)
                                    | uu____3786 ->
                                        let uu____3789 =
                                          let uu____3794 =
                                            let uu____3795 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                annotated_univ_names
                                                signature1
                                               in
                                            (annotated_univ_names,
                                              uu____3795)
                                             in
                                          FStar_TypeChecker_Env.inst_tscheme
                                            uu____3794
                                           in
                                        (match uu____3789 with
                                         | (uu____3808,signature2) ->
                                             wp_with_fresh_result_type env1
                                               ed2.FStar_Syntax_Syntax.mname
                                               signature2)
                                     in
                                  let env2 =
                                    let uu____3811 =
                                      FStar_Syntax_Syntax.new_bv
                                        FStar_Pervasives_Native.None
                                        signature1
                                       in
                                    FStar_TypeChecker_Env.push_bv env1
                                      uu____3811
                                     in
                                  ((let uu____3813 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env0)
                                        (FStar_Options.Other "ED")
                                       in
                                    if uu____3813
                                    then
                                      let uu____3818 =
                                        FStar_Syntax_Print.lid_to_string
                                          ed2.FStar_Syntax_Syntax.mname
                                         in
                                      let uu____3820 =
                                        FStar_Syntax_Print.binders_to_string
                                          " " ed2.FStar_Syntax_Syntax.binders
                                         in
                                      let uu____3823 =
                                        FStar_Syntax_Print.term_to_string
                                          signature1
                                         in
                                      let uu____3825 =
                                        let uu____3827 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Print.term_to_string
                                          uu____3827
                                         in
                                      let uu____3828 =
                                        FStar_Syntax_Print.term_to_string
                                          a.FStar_Syntax_Syntax.sort
                                         in
                                      FStar_Util.print5
                                        "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                                        uu____3818 uu____3820 uu____3823
                                        uu____3825 uu____3828
                                    else ());
                                   (let check_and_gen' env3 uu____3863 k =
                                      match uu____3863 with
                                      | (us,t) ->
                                          (match annotated_univ_names with
                                           | [] -> check_and_gen env3 t k
                                           | uu____3899::uu____3900 ->
                                               let uu____3903 =
                                                 FStar_Syntax_Subst.subst_tscheme
                                                   open_annotated_univs
                                                   (us, t)
                                                  in
                                               (match uu____3903 with
                                                | (us1,t1) ->
                                                    let uu____3926 =
                                                      FStar_Syntax_Subst.open_univ_vars
                                                        us1 t1
                                                       in
                                                    (match uu____3926 with
                                                     | (us2,t2) ->
                                                         let uu____3941 =
                                                           let uu____3942 =
                                                             FStar_TypeChecker_Env.push_univ_vars
                                                               env3 us2
                                                              in
                                                           tc_check_trivial_guard
                                                             uu____3942 t2 k
                                                            in
                                                         let uu____3943 =
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             us2 t2
                                                            in
                                                         (us2, uu____3943))))
                                       in
                                    let return_wp =
                                      let expected_k =
                                        let uu____3962 =
                                          let uu____3971 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____3978 =
                                            let uu____3987 =
                                              let uu____3994 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____3994
                                               in
                                            [uu____3987]  in
                                          uu____3971 :: uu____3978  in
                                        let uu____4013 =
                                          FStar_Syntax_Syntax.mk_GTotal wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____3962
                                          uu____4013
                                         in
                                      check_and_gen' env2
                                        (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                        expected_k
                                       in
                                    let bind_wp =
                                      let uu____4017 =
                                        fresh_effect_signature ()  in
                                      match uu____4017 with
                                      | (b,wp_b) ->
                                          let a_wp_b =
                                            let uu____4033 =
                                              let uu____4042 =
                                                let uu____4049 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____4049
                                                 in
                                              [uu____4042]  in
                                            let uu____4062 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_b
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4033 uu____4062
                                             in
                                          let expected_k =
                                            let uu____4068 =
                                              let uu____4077 =
                                                FStar_Syntax_Syntax.null_binder
                                                  FStar_Syntax_Syntax.t_range
                                                 in
                                              let uu____4084 =
                                                let uu____4093 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____4100 =
                                                  let uu____4109 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____4116 =
                                                    let uu____4125 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_a
                                                       in
                                                    let uu____4132 =
                                                      let uu____4141 =
                                                        FStar_Syntax_Syntax.null_binder
                                                          a_wp_b
                                                         in
                                                      [uu____4141]  in
                                                    uu____4125 :: uu____4132
                                                     in
                                                  uu____4109 :: uu____4116
                                                   in
                                                uu____4093 :: uu____4100  in
                                              uu____4077 :: uu____4084  in
                                            let uu____4184 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_b
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4068 uu____4184
                                             in
                                          check_and_gen' env2
                                            (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                            expected_k
                                       in
                                    let if_then_else1 =
                                      let p =
                                        let uu____4197 =
                                          let uu____4200 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4200
                                           in
                                        let uu____4201 =
                                          let uu____4202 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4202
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4197
                                          uu____4201
                                         in
                                      let expected_k =
                                        let uu____4214 =
                                          let uu____4223 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4230 =
                                            let uu____4239 =
                                              FStar_Syntax_Syntax.mk_binder p
                                               in
                                            let uu____4246 =
                                              let uu____4255 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              let uu____4262 =
                                                let uu____4271 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____4271]  in
                                              uu____4255 :: uu____4262  in
                                            uu____4239 :: uu____4246  in
                                          uu____4223 :: uu____4230  in
                                        let uu____4308 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4214
                                          uu____4308
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.if_then_else
                                        expected_k
                                       in
                                    let ite_wp =
                                      let expected_k =
                                        let uu____4323 =
                                          let uu____4332 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4339 =
                                            let uu____4348 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____4348]  in
                                          uu____4332 :: uu____4339  in
                                        let uu____4373 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4323
                                          uu____4373
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.ite_wp
                                        expected_k
                                       in
                                    let stronger =
                                      let uu____4377 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____4377 with
                                      | (t,uu____4383) ->
                                          let expected_k =
                                            let uu____4387 =
                                              let uu____4396 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4403 =
                                                let uu____4412 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____4419 =
                                                  let uu____4428 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____4428]  in
                                                uu____4412 :: uu____4419  in
                                              uu____4396 :: uu____4403  in
                                            let uu____4459 =
                                              FStar_Syntax_Syntax.mk_Total t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4387 uu____4459
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.stronger
                                            expected_k
                                       in
                                    let close_wp =
                                      let b =
                                        let uu____4472 =
                                          let uu____4475 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4475
                                           in
                                        let uu____4476 =
                                          let uu____4477 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4477
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4472
                                          uu____4476
                                         in
                                      let b_wp_a =
                                        let uu____4489 =
                                          let uu____4498 =
                                            let uu____4505 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                b
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____4505
                                             in
                                          [uu____4498]  in
                                        let uu____4518 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4489
                                          uu____4518
                                         in
                                      let expected_k =
                                        let uu____4524 =
                                          let uu____4533 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4540 =
                                            let uu____4549 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4556 =
                                              let uu____4565 =
                                                FStar_Syntax_Syntax.null_binder
                                                  b_wp_a
                                                 in
                                              [uu____4565]  in
                                            uu____4549 :: uu____4556  in
                                          uu____4533 :: uu____4540  in
                                        let uu____4596 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4524
                                          uu____4596
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.close_wp
                                        expected_k
                                       in
                                    let assert_p =
                                      let expected_k =
                                        let uu____4611 =
                                          let uu____4620 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4627 =
                                            let uu____4636 =
                                              let uu____4643 =
                                                let uu____4644 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____4644
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4643
                                               in
                                            let uu____4653 =
                                              let uu____4662 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____4662]  in
                                            uu____4636 :: uu____4653  in
                                          uu____4620 :: uu____4627  in
                                        let uu____4693 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4611
                                          uu____4693
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.assert_p
                                        expected_k
                                       in
                                    let assume_p =
                                      let expected_k =
                                        let uu____4708 =
                                          let uu____4717 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4724 =
                                            let uu____4733 =
                                              let uu____4740 =
                                                let uu____4741 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____4741
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4740
                                               in
                                            let uu____4750 =
                                              let uu____4759 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____4759]  in
                                            uu____4733 :: uu____4750  in
                                          uu____4717 :: uu____4724  in
                                        let uu____4790 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4708
                                          uu____4790
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.assume_p
                                        expected_k
                                       in
                                    let null_wp =
                                      let expected_k =
                                        let uu____4805 =
                                          let uu____4814 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          [uu____4814]  in
                                        let uu____4833 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4805
                                          uu____4833
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.null_wp
                                        expected_k
                                       in
                                    let trivial_wp =
                                      let uu____4837 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____4837 with
                                      | (t,uu____4843) ->
                                          let expected_k =
                                            let uu____4847 =
                                              let uu____4856 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4863 =
                                                let uu____4872 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____4872]  in
                                              uu____4856 :: uu____4863  in
                                            let uu____4897 =
                                              FStar_Syntax_Syntax.mk_GTotal t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4847 uu____4897
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.trivial
                                            expected_k
                                       in
                                    let uu____4900 =
                                      let uu____4913 =
                                        let uu____4918 =
                                          let uu____4919 =
                                            FStar_Syntax_Subst.compress
                                              (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                             in
                                          uu____4919.FStar_Syntax_Syntax.n
                                           in
                                        let uu____4922 =
                                          let uu____4923 =
                                            FStar_Syntax_Subst.compress
                                              (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m
                                             in
                                          uu____4923.FStar_Syntax_Syntax.n
                                           in
                                        (uu____4918, uu____4922)  in
                                      if ed2.FStar_Syntax_Syntax.spec_dm4f
                                      then
                                        let repr =
                                          let uu____4939 =
                                            FStar_Syntax_Util.type_u ()  in
                                          match uu____4939 with
                                          | (t,uu____4945) ->
                                              let expected_k =
                                                let uu____4949 =
                                                  let uu____4958 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____4965 =
                                                    let uu____4974 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_a
                                                       in
                                                    [uu____4974]  in
                                                  uu____4958 :: uu____4965
                                                   in
                                                let uu____4999 =
                                                  FStar_Syntax_Syntax.mk_GTotal
                                                    t
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____4949 uu____4999
                                                 in
                                              ((let uu____5003 =
                                                  FStar_TypeChecker_Env.debug
                                                    env2
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____5003
                                                then
                                                  let uu____5007 =
                                                    FStar_Syntax_Print.term_to_string
                                                      (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                                     in
                                                  let uu____5009 =
                                                    FStar_Syntax_Print.term_to_string
                                                      expected_k
                                                     in
                                                  FStar_Util.print2
                                                    "About to check repr=%s\nat type %s\n"
                                                    uu____5007 uu____5009
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
                                          let uu____5028 =
                                            let uu____5035 =
                                              let uu____5036 =
                                                let uu____5053 =
                                                  let uu____5064 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      t
                                                     in
                                                  let uu____5073 =
                                                    let uu____5084 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        wp
                                                       in
                                                    [uu____5084]  in
                                                  uu____5064 :: uu____5073
                                                   in
                                                (repr1, uu____5053)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____5036
                                               in
                                            FStar_Syntax_Syntax.mk uu____5035
                                             in
                                          uu____5028
                                            FStar_Pervasives_Native.None
                                            FStar_Range.dummyRange
                                           in
                                        let mk_repr a1 wp =
                                          let uu____5145 =
                                            FStar_Syntax_Syntax.bv_to_name a1
                                             in
                                          mk_repr' uu____5145 wp  in
                                        let destruct_repr t =
                                          let uu____5160 =
                                            let uu____5161 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____5161.FStar_Syntax_Syntax.n
                                             in
                                          match uu____5160 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____5172,(t1,uu____5174)::
                                               (wp,uu____5176)::[])
                                              -> (t1, wp)
                                          | uu____5235 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let bind_repr =
                                          let r =
                                            let uu____5247 =
                                              FStar_Syntax_Syntax.lid_as_fv
                                                FStar_Parser_Const.range_0
                                                FStar_Syntax_Syntax.delta_constant
                                                FStar_Pervasives_Native.None
                                               in
                                            FStar_All.pipe_right uu____5247
                                              FStar_Syntax_Syntax.fv_to_tm
                                             in
                                          let uu____5248 =
                                            fresh_effect_signature ()  in
                                          match uu____5248 with
                                          | (b,wp_b) ->
                                              let a_wp_b =
                                                let uu____5264 =
                                                  let uu____5273 =
                                                    let uu____5280 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        a
                                                       in
                                                    FStar_Syntax_Syntax.null_binder
                                                      uu____5280
                                                     in
                                                  [uu____5273]  in
                                                let uu____5293 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    wp_b
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____5264 uu____5293
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
                                                let uu____5301 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____5301
                                                 in
                                              let wp_g_x =
                                                let uu____5306 =
                                                  let uu____5311 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      wp_g
                                                     in
                                                  let uu____5312 =
                                                    let uu____5313 =
                                                      let uu____5322 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x_a
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.as_arg
                                                        uu____5322
                                                       in
                                                    [uu____5313]  in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____5311 uu____5312
                                                   in
                                                uu____5306
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____5355 =
                                                    let uu____5360 =
                                                      let uu____5361 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          bind_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____5361
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____5370 =
                                                      let uu____5371 =
                                                        let uu____5374 =
                                                          let uu____5377 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          let uu____5378 =
                                                            let uu____5381 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                b
                                                               in
                                                            let uu____5382 =
                                                              let uu____5385
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_f
                                                                 in
                                                              let uu____5386
                                                                =
                                                                let uu____5389
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                   in
                                                                [uu____5389]
                                                                 in
                                                              uu____5385 ::
                                                                uu____5386
                                                               in
                                                            uu____5381 ::
                                                              uu____5382
                                                             in
                                                          uu____5377 ::
                                                            uu____5378
                                                           in
                                                        r :: uu____5374  in
                                                      FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg
                                                        uu____5371
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____5360 uu____5370
                                                     in
                                                  uu____5355
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr b wp  in
                                              let maybe_range_arg =
                                                let uu____5409 =
                                                  FStar_Util.for_some
                                                    (FStar_Syntax_Util.attr_eq
                                                       FStar_Syntax_Util.dm4f_bind_range_attr)
                                                    ed2.FStar_Syntax_Syntax.eff_attrs
                                                   in
                                                if uu____5409
                                                then
                                                  let uu____5420 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      FStar_Syntax_Syntax.t_range
                                                     in
                                                  let uu____5427 =
                                                    let uu____5436 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        FStar_Syntax_Syntax.t_range
                                                       in
                                                    [uu____5436]  in
                                                  uu____5420 :: uu____5427
                                                else []  in
                                              let expected_k =
                                                let uu____5472 =
                                                  let uu____5481 =
                                                    let uu____5490 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a
                                                       in
                                                    let uu____5497 =
                                                      let uu____5506 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          b
                                                         in
                                                      [uu____5506]  in
                                                    uu____5490 :: uu____5497
                                                     in
                                                  let uu____5531 =
                                                    let uu____5540 =
                                                      let uu____5549 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          wp_f
                                                         in
                                                      let uu____5556 =
                                                        let uu____5565 =
                                                          let uu____5572 =
                                                            let uu____5573 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            mk_repr a
                                                              uu____5573
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____5572
                                                           in
                                                        let uu____5574 =
                                                          let uu____5583 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              wp_g
                                                             in
                                                          let uu____5590 =
                                                            let uu____5599 =
                                                              let uu____5606
                                                                =
                                                                let uu____5607
                                                                  =
                                                                  let uu____5616
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                  [uu____5616]
                                                                   in
                                                                let uu____5635
                                                                  =
                                                                  let uu____5638
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____5638
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  uu____5607
                                                                  uu____5635
                                                                 in
                                                              FStar_Syntax_Syntax.null_binder
                                                                uu____5606
                                                               in
                                                            [uu____5599]  in
                                                          uu____5583 ::
                                                            uu____5590
                                                           in
                                                        uu____5565 ::
                                                          uu____5574
                                                         in
                                                      uu____5549 ::
                                                        uu____5556
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____5540
                                                     in
                                                  FStar_List.append
                                                    uu____5481 uu____5531
                                                   in
                                                let uu____5683 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____5472 uu____5683
                                                 in
                                              ((let uu____5687 =
                                                  FStar_TypeChecker_Env.debug
                                                    env2
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____5687
                                                then
                                                  let uu____5691 =
                                                    FStar_Syntax_Print.term_to_string
                                                      expected_k
                                                     in
                                                  FStar_Util.print1
                                                    "About to check expected_k %s\n"
                                                    uu____5691
                                                else ());
                                               (let uu____5696 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env2 expected_k
                                                   in
                                                match uu____5696 with
                                                | (expected_k1,uu____5704,uu____5705)
                                                    ->
                                                    ((let uu____5707 =
                                                        FStar_TypeChecker_Env.debug
                                                          env2
                                                          (FStar_Options.Other
                                                             "ED")
                                                         in
                                                      if uu____5707
                                                      then
                                                        let uu____5711 =
                                                          FStar_Syntax_Print.term_to_string
                                                            (FStar_Pervasives_Native.snd
                                                               (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind)
                                                           in
                                                        let uu____5717 =
                                                          FStar_Syntax_Print.term_to_string
                                                            expected_k1
                                                           in
                                                        FStar_Util.print2
                                                          "About to check bind=%s\n\n, at type %s\n"
                                                          uu____5711
                                                          uu____5717
                                                      else ());
                                                     (let env3 =
                                                        FStar_TypeChecker_Env.set_range
                                                          env2
                                                          (FStar_Pervasives_Native.snd
                                                             (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind).FStar_Syntax_Syntax.pos
                                                         in
                                                      let env4 =
                                                        let uu___390_5728 =
                                                          env3  in
                                                        {
                                                          FStar_TypeChecker_Env.solver
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.solver);
                                                          FStar_TypeChecker_Env.range
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.range);
                                                          FStar_TypeChecker_Env.curmodule
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.curmodule);
                                                          FStar_TypeChecker_Env.gamma
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.gamma);
                                                          FStar_TypeChecker_Env.gamma_sig
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.gamma_sig);
                                                          FStar_TypeChecker_Env.gamma_cache
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.gamma_cache);
                                                          FStar_TypeChecker_Env.modules
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.modules);
                                                          FStar_TypeChecker_Env.expected_typ
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.expected_typ);
                                                          FStar_TypeChecker_Env.sigtab
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.sigtab);
                                                          FStar_TypeChecker_Env.attrtab
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.attrtab);
                                                          FStar_TypeChecker_Env.is_pattern
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.is_pattern);
                                                          FStar_TypeChecker_Env.instantiate_imp
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.instantiate_imp);
                                                          FStar_TypeChecker_Env.effects
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.effects);
                                                          FStar_TypeChecker_Env.generalize
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.generalize);
                                                          FStar_TypeChecker_Env.letrecs
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.letrecs);
                                                          FStar_TypeChecker_Env.top_level
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.top_level);
                                                          FStar_TypeChecker_Env.check_uvars
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.check_uvars);
                                                          FStar_TypeChecker_Env.use_eq
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.use_eq);
                                                          FStar_TypeChecker_Env.is_iface
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.is_iface);
                                                          FStar_TypeChecker_Env.admit
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.admit);
                                                          FStar_TypeChecker_Env.lax
                                                            = true;
                                                          FStar_TypeChecker_Env.lax_universes
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.lax_universes);
                                                          FStar_TypeChecker_Env.phase1
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.phase1);
                                                          FStar_TypeChecker_Env.failhard
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.failhard);
                                                          FStar_TypeChecker_Env.nosynth
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.nosynth);
                                                          FStar_TypeChecker_Env.uvar_subtyping
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.uvar_subtyping);
                                                          FStar_TypeChecker_Env.tc_term
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.tc_term);
                                                          FStar_TypeChecker_Env.type_of
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.type_of);
                                                          FStar_TypeChecker_Env.universe_of
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.universe_of);
                                                          FStar_TypeChecker_Env.check_type_of
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.check_type_of);
                                                          FStar_TypeChecker_Env.use_bv_sorts
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.use_bv_sorts);
                                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                          FStar_TypeChecker_Env.normalized_eff_names
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.normalized_eff_names);
                                                          FStar_TypeChecker_Env.fv_delta_depths
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.fv_delta_depths);
                                                          FStar_TypeChecker_Env.proof_ns
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.proof_ns);
                                                          FStar_TypeChecker_Env.synth_hook
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.synth_hook);
                                                          FStar_TypeChecker_Env.splice
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.splice);
                                                          FStar_TypeChecker_Env.postprocess
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.postprocess);
                                                          FStar_TypeChecker_Env.is_native_tactic
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.is_native_tactic);
                                                          FStar_TypeChecker_Env.identifier_info
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.identifier_info);
                                                          FStar_TypeChecker_Env.tc_hooks
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.tc_hooks);
                                                          FStar_TypeChecker_Env.dsenv
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.dsenv);
                                                          FStar_TypeChecker_Env.nbe
                                                            =
                                                            (uu___390_5728.FStar_TypeChecker_Env.nbe)
                                                        }  in
                                                      let br =
                                                        check_and_gen' env4
                                                          (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                                          expected_k1
                                                         in
                                                      (let uu____5740 =
                                                         FStar_TypeChecker_Env.debug
                                                           env4
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____5740
                                                       then
                                                         let uu____5744 =
                                                           FStar_Syntax_Print.tscheme_to_string
                                                             br
                                                            in
                                                         let uu____5746 =
                                                           FStar_Syntax_Print.term_to_string
                                                             expected_k1
                                                            in
                                                         FStar_Util.print2
                                                           "After checking bind_repr is %s\nexpected_k is %s\n"
                                                           uu____5744
                                                           uu____5746
                                                       else ());
                                                      br))))
                                           in
                                        let return_repr =
                                          let x_a =
                                            let uu____5753 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.gen_bv "x_a"
                                              FStar_Pervasives_Native.None
                                              uu____5753
                                             in
                                          let res =
                                            let wp =
                                              let uu____5761 =
                                                let uu____5766 =
                                                  let uu____5767 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      return_wp
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____5767
                                                    FStar_Pervasives_Native.snd
                                                   in
                                                let uu____5776 =
                                                  let uu____5777 =
                                                    let uu____5780 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        a
                                                       in
                                                    let uu____5781 =
                                                      let uu____5784 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x_a
                                                         in
                                                      [uu____5784]  in
                                                    uu____5780 :: uu____5781
                                                     in
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.as_arg
                                                    uu____5777
                                                   in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____5766 uu____5776
                                                 in
                                              uu____5761
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            mk_repr a wp  in
                                          let expected_k =
                                            let uu____5798 =
                                              let uu____5807 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____5814 =
                                                let uu____5823 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    x_a
                                                   in
                                                [uu____5823]  in
                                              uu____5807 :: uu____5814  in
                                            let uu____5848 =
                                              FStar_Syntax_Syntax.mk_Total
                                                res
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5798 uu____5848
                                             in
                                          let uu____5851 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k
                                             in
                                          match uu____5851 with
                                          | (expected_k1,uu____5859,uu____5860)
                                              ->
                                              let env3 =
                                                FStar_TypeChecker_Env.set_range
                                                  env2
                                                  (FStar_Pervasives_Native.snd
                                                     (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret).FStar_Syntax_Syntax.pos
                                                 in
                                              let uu____5866 =
                                                check_and_gen' env3
                                                  (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                                  expected_k1
                                                 in
                                              (match uu____5866 with
                                               | (univs1,repr1) ->
                                                   (match univs1 with
                                                    | [] -> ([], repr1)
                                                    | uu____5889 ->
                                                        FStar_Errors.raise_error
                                                          (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                            "Unexpected universe-polymorphic return for effect")
                                                          repr1.FStar_Syntax_Syntax.pos))
                                           in
                                        let actions =
                                          let check_action act =
                                            let uu____5904 =
                                              if
                                                act.FStar_Syntax_Syntax.action_univs
                                                  = []
                                              then (env2, act)
                                              else
                                                (let uu____5918 =
                                                   FStar_Syntax_Subst.univ_var_opening
                                                     act.FStar_Syntax_Syntax.action_univs
                                                    in
                                                 match uu____5918 with
                                                 | (usubst,uvs) ->
                                                     let uu____5941 =
                                                       FStar_TypeChecker_Env.push_univ_vars
                                                         env2 uvs
                                                        in
                                                     let uu____5942 =
                                                       let uu___391_5943 =
                                                         act  in
                                                       let uu____5944 =
                                                         FStar_Syntax_Subst.subst_binders
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_params
                                                          in
                                                       let uu____5945 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____5946 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___391_5943.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___391_5943.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = uvs;
                                                         FStar_Syntax_Syntax.action_params
                                                           = uu____5944;
                                                         FStar_Syntax_Syntax.action_defn
                                                           = uu____5945;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____5946
                                                       }  in
                                                     (uu____5941, uu____5942))
                                               in
                                            match uu____5904 with
                                            | (env3,act1) ->
                                                let act_typ =
                                                  let uu____5950 =
                                                    let uu____5951 =
                                                      FStar_Syntax_Subst.compress
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                       in
                                                    uu____5951.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____5950 with
                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                      (bs,c) ->
                                                      let c1 =
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                          c
                                                         in
                                                      let uu____5977 =
                                                        FStar_Ident.lid_equals
                                                          c1.FStar_Syntax_Syntax.effect_name
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      if uu____5977
                                                      then
                                                        let uu____5980 =
                                                          let uu____5983 =
                                                            let uu____5984 =
                                                              let uu____5985
                                                                =
                                                                FStar_List.hd
                                                                  c1.FStar_Syntax_Syntax.effect_args
                                                                 in
                                                              FStar_Pervasives_Native.fst
                                                                uu____5985
                                                               in
                                                            mk_repr'
                                                              c1.FStar_Syntax_Syntax.result_typ
                                                              uu____5984
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total
                                                            uu____5983
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          bs uu____5980
                                                      else
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                  | uu____6008 ->
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                   in
                                                let uu____6009 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env3 act_typ
                                                   in
                                                (match uu____6009 with
                                                 | (act_typ1,uu____6017,g_t)
                                                     ->
                                                     let env' =
                                                       let uu___392_6020 =
                                                         FStar_TypeChecker_Env.set_expected_typ
                                                           env3 act_typ1
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.is_pattern
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.is_pattern);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           = false;
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.lax);
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___392_6020.FStar_TypeChecker_Env.nbe)
                                                       }  in
                                                     ((let uu____6023 =
                                                         FStar_TypeChecker_Env.debug
                                                           env3
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____6023
                                                       then
                                                         let uu____6027 =
                                                           FStar_Ident.text_of_lid
                                                             act1.FStar_Syntax_Syntax.action_name
                                                            in
                                                         let uu____6029 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____6031 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act_typ1
                                                            in
                                                         FStar_Util.print3
                                                           "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                           uu____6027
                                                           uu____6029
                                                           uu____6031
                                                       else ());
                                                      (let uu____6036 =
                                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                           env'
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       match uu____6036 with
                                                       | (act_defn,uu____6044,g_a)
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
                                                           let uu____6048 =
                                                             let act_typ3 =
                                                               FStar_Syntax_Subst.compress
                                                                 act_typ2
                                                                in
                                                             match act_typ3.FStar_Syntax_Syntax.n
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____6084
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                    in
                                                                 (match uu____6084
                                                                  with
                                                                  | (bs1,uu____6096)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6103
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____6103
                                                                     in
                                                                    let uu____6106
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____6106
                                                                    with
                                                                    | 
                                                                    (k1,uu____6120,g)
                                                                    ->
                                                                    (k1, g)))
                                                             | uu____6124 ->
                                                                 let uu____6125
                                                                   =
                                                                   let uu____6131
                                                                    =
                                                                    let uu____6133
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____6135
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____6133
                                                                    uu____6135
                                                                     in
                                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____6131)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____6125
                                                                   act_defn1.FStar_Syntax_Syntax.pos
                                                              in
                                                           (match uu____6048
                                                            with
                                                            | (expected_k,g_k)
                                                                ->
                                                                let g =
                                                                  FStar_TypeChecker_Rel.teq
                                                                    env3
                                                                    act_typ2
                                                                    expected_k
                                                                   in
                                                                ((let uu____6153
                                                                    =
                                                                    let uu____6154
                                                                    =
                                                                    let uu____6155
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____6155
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____6154
                                                                     in
                                                                  FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env3
                                                                    uu____6153);
                                                                 (let act_typ3
                                                                    =
                                                                    let uu____6157
                                                                    =
                                                                    let uu____6158
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____6158.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____6157
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____6183
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____6183
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____6190
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____6190
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____6210
                                                                    =
                                                                    let uu____6211
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____6211]
                                                                     in
                                                                    let uu____6212
                                                                    =
                                                                    let uu____6223
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____6223]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6210;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6212;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____6248
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____6248))
                                                                    | 
                                                                    uu____6251
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                  let uu____6253
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                    else
                                                                    (let uu____6275
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____6275))
                                                                     in
                                                                  match uu____6253
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
                                                                    let uu___393_6294
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___393_6294.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___393_6294.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___393_6294.FStar_Syntax_Syntax.action_params);
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
                                        (match uu____4913 with
                                         | (uu____6303,uu____6304) ->
                                             (((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m),
                                               ((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind),
                                               ((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret),
                                               (ed2.FStar_Syntax_Syntax.actions)))
                                       in
                                    match uu____4900 with
                                    | (repr,bind_repr,return_repr,actions) ->
                                        let t0 =
                                          let uu____6324 =
                                            FStar_Syntax_Syntax.mk_Total
                                              signature1
                                             in
                                          FStar_Syntax_Util.arrow
                                            ed2.FStar_Syntax_Syntax.binders
                                            uu____6324
                                           in
                                        let uu____6327 =
                                          let uu____6332 =
                                            FStar_TypeChecker_Util.generalize_universes
                                              env0 t0
                                             in
                                          match uu____6332 with
                                          | (gen_univs,t) ->
                                              (match annotated_univ_names
                                               with
                                               | [] -> (gen_univs, t)
                                               | uu____6351 ->
                                                   let uu____6354 =
                                                     ((FStar_List.length
                                                         gen_univs)
                                                        =
                                                        (FStar_List.length
                                                           annotated_univ_names))
                                                       &&
                                                       (FStar_List.forall2
                                                          (fun u1  ->
                                                             fun u2  ->
                                                               let uu____6361
                                                                 =
                                                                 FStar_Syntax_Syntax.order_univ_name
                                                                   u1 u2
                                                                  in
                                                               uu____6361 =
                                                                 (Prims.parse_int "0"))
                                                          gen_univs
                                                          annotated_univ_names)
                                                      in
                                                   if uu____6354
                                                   then (gen_univs, t)
                                                   else
                                                     (let uu____6372 =
                                                        let uu____6378 =
                                                          let uu____6380 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 annotated_univ_names)
                                                             in
                                                          let uu____6382 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 gen_univs)
                                                             in
                                                          FStar_Util.format2
                                                            "Expected an effect definition with %s universes; but found %s"
                                                            uu____6380
                                                            uu____6382
                                                           in
                                                        (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                          uu____6378)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____6372
                                                        signature1.FStar_Syntax_Syntax.pos))
                                           in
                                        (match uu____6327 with
                                         | (univs1,t) ->
                                             let signature2 =
                                               let uu____6393 =
                                                 let uu____6406 =
                                                   let uu____6407 =
                                                     FStar_Syntax_Subst.compress
                                                       t
                                                      in
                                                   uu____6407.FStar_Syntax_Syntax.n
                                                    in
                                                 (effect_params, uu____6406)
                                                  in
                                               match uu____6393 with
                                               | ([],uu____6418) -> t
                                               | (uu____6433,FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____6434,c)) ->
                                                   FStar_Syntax_Util.comp_result
                                                     c
                                               | uu____6472 ->
                                                   failwith
                                                     "Impossible : t is an arrow"
                                                in
                                             let close1 n1 ts =
                                               let ts1 =
                                                 let uu____6500 =
                                                   FStar_Syntax_Subst.close_tscheme
                                                     effect_params ts
                                                    in
                                                 FStar_Syntax_Subst.close_univ_vars_tscheme
                                                   univs1 uu____6500
                                                  in
                                               let m =
                                                 FStar_List.length
                                                   (FStar_Pervasives_Native.fst
                                                      ts1)
                                                  in
                                               (let uu____6507 =
                                                  ((n1 >=
                                                      (Prims.parse_int "0"))
                                                     &&
                                                     (let uu____6511 =
                                                        FStar_Syntax_Util.is_unknown
                                                          (FStar_Pervasives_Native.snd
                                                             ts1)
                                                         in
                                                      Prims.op_Negation
                                                        uu____6511))
                                                    && (m <> n1)
                                                   in
                                                if uu____6507
                                                then
                                                  let err_msg uu____6529 =
                                                    let error =
                                                      if m < n1
                                                      then
                                                        "not universe-polymorphic enough"
                                                      else
                                                        "too universe-polymorphic"
                                                       in
                                                    let uu____6544 =
                                                      FStar_Util.string_of_int
                                                        m
                                                       in
                                                    let uu____6552 =
                                                      FStar_Util.string_of_int
                                                        n1
                                                       in
                                                    let uu____6554 =
                                                      FStar_Syntax_Print.tscheme_to_string
                                                        ts1
                                                       in
                                                    FStar_Util.format4
                                                      "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                      error uu____6544
                                                      uu____6552 uu____6554
                                                     in
                                                  let uu____6557 =
                                                    let uu____6563 =
                                                      err_msg ()  in
                                                    (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                      uu____6563)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____6557
                                                    (FStar_Pervasives_Native.snd
                                                       ts1).FStar_Syntax_Syntax.pos
                                                else ());
                                               ts1  in
                                             let close_action act =
                                               let uu____6578 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               match uu____6578 with
                                               | (univs2,defn) ->
                                                   let uu____6594 =
                                                     close1
                                                       (~-
                                                          (Prims.parse_int "1"))
                                                       ((act.FStar_Syntax_Syntax.action_univs),
                                                         (act.FStar_Syntax_Syntax.action_typ))
                                                      in
                                                   (match uu____6594 with
                                                    | (univs',typ) ->
                                                        let uu___394_6611 =
                                                          act  in
                                                        {
                                                          FStar_Syntax_Syntax.action_name
                                                            =
                                                            (uu___394_6611.FStar_Syntax_Syntax.action_name);
                                                          FStar_Syntax_Syntax.action_unqualified_name
                                                            =
                                                            (uu___394_6611.FStar_Syntax_Syntax.action_unqualified_name);
                                                          FStar_Syntax_Syntax.action_univs
                                                            = univs2;
                                                          FStar_Syntax_Syntax.action_params
                                                            =
                                                            (uu___394_6611.FStar_Syntax_Syntax.action_params);
                                                          FStar_Syntax_Syntax.action_defn
                                                            = defn;
                                                          FStar_Syntax_Syntax.action_typ
                                                            = typ
                                                        })
                                                in
                                             let ed3 =
                                               let uu___395_6614 = ed2  in
                                               let uu____6615 =
                                                 let uu____6616 =
                                                   close1
                                                     (Prims.parse_int "0")
                                                     return_wp
                                                    in
                                                 let uu____6618 =
                                                   close1
                                                     (Prims.parse_int "1")
                                                     bind_wp
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     =
                                                     FStar_Syntax_Syntax.tun;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____6616;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____6618
                                                 }  in
                                               let uu____6620 =
                                                 close1 (Prims.parse_int "0")
                                                   if_then_else1
                                                  in
                                               let uu____6622 =
                                                 close1 (Prims.parse_int "0")
                                                   ite_wp
                                                  in
                                               let uu____6624 =
                                                 close1 (Prims.parse_int "0")
                                                   stronger
                                                  in
                                               let uu____6626 =
                                                 close1 (Prims.parse_int "1")
                                                   close_wp
                                                  in
                                               let uu____6628 =
                                                 close1 (Prims.parse_int "0")
                                                   assert_p
                                                  in
                                               let uu____6630 =
                                                 close1 (Prims.parse_int "0")
                                                   assume_p
                                                  in
                                               let uu____6632 =
                                                 close1 (Prims.parse_int "0")
                                                   null_wp
                                                  in
                                               let uu____6634 =
                                                 close1 (Prims.parse_int "0")
                                                   trivial_wp
                                                  in
                                               let uu____6636 =
                                                 let uu____6637 =
                                                   let uu____6638 =
                                                     close1
                                                       (Prims.parse_int "0")
                                                       ([], repr)
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____6638
                                                    in
                                                 let uu____6656 =
                                                   close1
                                                     (Prims.parse_int "0")
                                                     return_repr
                                                    in
                                                 let uu____6658 =
                                                   close1
                                                     (Prims.parse_int "1")
                                                     bind_repr
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     = uu____6637;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____6656;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____6658
                                                 }  in
                                               let uu____6660 =
                                                 FStar_List.map close_action
                                                   actions
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.cattributes
                                                   =
                                                   (uu___395_6614.FStar_Syntax_Syntax.cattributes);
                                                 FStar_Syntax_Syntax.mname =
                                                   (uu___395_6614.FStar_Syntax_Syntax.mname);
                                                 FStar_Syntax_Syntax.univs =
                                                   univs1;
                                                 FStar_Syntax_Syntax.binders
                                                   = effect_params;
                                                 FStar_Syntax_Syntax.spec =
                                                   uu____6615;
                                                 FStar_Syntax_Syntax.signature
                                                   = signature2;
                                                 FStar_Syntax_Syntax.if_then_else
                                                   = uu____6620;
                                                 FStar_Syntax_Syntax.ite_wp =
                                                   uu____6622;
                                                 FStar_Syntax_Syntax.stronger
                                                   = uu____6624;
                                                 FStar_Syntax_Syntax.close_wp
                                                   = uu____6626;
                                                 FStar_Syntax_Syntax.assert_p
                                                   = uu____6628;
                                                 FStar_Syntax_Syntax.assume_p
                                                   = uu____6630;
                                                 FStar_Syntax_Syntax.null_wp
                                                   = uu____6632;
                                                 FStar_Syntax_Syntax.trivial
                                                   = uu____6634;
                                                 FStar_Syntax_Syntax.repr =
                                                   uu____6636;
                                                 FStar_Syntax_Syntax.elaborated
                                                   =
                                                   (uu___395_6614.FStar_Syntax_Syntax.elaborated);
                                                 FStar_Syntax_Syntax.spec_dm4f
                                                   =
                                                   (uu___395_6614.FStar_Syntax_Syntax.spec_dm4f);
                                                 FStar_Syntax_Syntax.actions
                                                   = uu____6660;
                                                 FStar_Syntax_Syntax.eff_attrs
                                                   =
                                                   (uu___395_6614.FStar_Syntax_Syntax.eff_attrs)
                                               }  in
                                             ed3)))))))))
  
let tc_lex_t :
  'Auu____6674 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____6674 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____6709 = FStar_List.hd ses  in
            uu____6709.FStar_Syntax_Syntax.sigrng  in
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
           | uu____6714 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____6720,[],t,uu____6722,uu____6723);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____6725;
               FStar_Syntax_Syntax.sigattrs = uu____6726;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____6728,_t_top,_lex_t_top,_0_1,uu____6731);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____6733;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____6734;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____6736,_t_cons,_lex_t_cons,_0_2,uu____6739);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____6741;
                 FStar_Syntax_Syntax.sigattrs = uu____6742;_}::[]
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
                 let uu____6793 =
                   let uu____6800 =
                     let uu____6801 =
                       let uu____6808 =
                         let uu____6811 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____6811
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____6808, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____6801  in
                   FStar_Syntax_Syntax.mk uu____6800  in
                 uu____6793 FStar_Pervasives_Native.None r1  in
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
                   let uu____6829 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6829
                    in
                 let hd1 =
                   let uu____6831 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6831
                    in
                 let tl1 =
                   let uu____6833 =
                     let uu____6834 =
                       let uu____6841 =
                         let uu____6842 =
                           let uu____6849 =
                             let uu____6852 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____6852
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____6849, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____6842  in
                       FStar_Syntax_Syntax.mk uu____6841  in
                     uu____6834 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6833
                    in
                 let res =
                   let uu____6861 =
                     let uu____6868 =
                       let uu____6869 =
                         let uu____6876 =
                           let uu____6879 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____6879
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____6876,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____6869  in
                     FStar_Syntax_Syntax.mk uu____6868  in
                   uu____6861 FStar_Pervasives_Native.None r2  in
                 let uu____6885 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____6885
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
               let uu____6924 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____6924;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____6929 ->
               let err_msg =
                 let uu____6934 =
                   let uu____6936 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____6936  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____6934
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
    fun uu____6961  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____6961 with
          | (uvs,t) ->
              let uu____6974 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____6974 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____6986 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____6986 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____7004 =
                        let uu____7007 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____7007
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____7004)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7030 =
          let uu____7031 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7031 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7030 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7056 =
          let uu____7057 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7057 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7056 r
  
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
          (let uu____7106 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____7106
           then
             let uu____7109 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____7109
           else ());
          (let uu____7114 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____7114 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____7145 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____7145 FStar_List.flatten  in
               ((let uu____7159 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____7162 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____7162)
                    in
                 if uu____7159
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
                           let uu____7178 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____7188,uu____7189,uu____7190,uu____7191,uu____7192)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____7201 -> failwith "Impossible!"  in
                           match uu____7178 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.strcat "Inductive type "
                                      (Prims.strcat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____7220 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____7230,uu____7231,ty_lid,uu____7233,uu____7234)
                               -> (data_lid, ty_lid)
                           | uu____7241 -> failwith "Impossible"  in
                         match uu____7220 with
                         | (data_lid,ty_lid) ->
                             let uu____7249 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____7252 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____7252)
                                in
                             if uu____7249
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.strcat "Exception "
                                      (Prims.strcat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____7266 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____7271,uu____7272,uu____7273,uu____7274,uu____7275)
                         -> lid
                     | uu____7284 -> failwith "Impossible"  in
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
                   let uu____7302 =
                     (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____7302
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
          let pop1 uu____7377 =
            let uu____7378 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___397_7388  ->
               match () with
               | () ->
                   let uu____7395 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____7395 (fun r  -> pop1 (); r)) ()
          with | uu___396_7426 -> (pop1 (); FStar_Exn.raise uu___396_7426)
  
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en  ->
    let env =
      let uu____7447 = FStar_Options.using_facts_from ()  in
      FStar_TypeChecker_Env.set_proof_ns uu____7447 en  in
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
      | uu____7751 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____7809 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____7809 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____7834 .
    'Auu____7834 FStar_Pervasives_Native.option -> 'Auu____7834 Prims.list
  =
  fun uu___374_7843  ->
    match uu___374_7843 with
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
            let uu____7923 = collect1 tl1  in
            (match uu____7923 with
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
        | ((e,n1)::uu____8161,[]) ->
            FStar_Pervasives_Native.Some (e, n1, (Prims.parse_int "0"))
        | ([],(e,n1)::uu____8217) ->
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
          let uu____8445 =
            let uu____8447 = FStar_Options.ide ()  in
            Prims.op_Negation uu____8447  in
          if uu____8445
          then
            let uu____8450 =
              let uu____8455 = FStar_TypeChecker_Env.dsenv env  in
              let uu____8456 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____8455 uu____8456  in
            (match uu____8450 with
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
                              let uu____8489 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____8490 =
                                let uu____8496 =
                                  let uu____8498 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____8500 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____8498 uu____8500
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____8496)
                                 in
                              FStar_Errors.log_issue uu____8489 uu____8490
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____8507 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____8508 =
                                   let uu____8514 =
                                     let uu____8516 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____8516
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____8514)
                                    in
                                 FStar_Errors.log_issue uu____8507 uu____8508)
                              else ())
                         else ())))
          else ()
      | uu____8526 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____8571 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____8599 ->
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
             let uu____8659 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____8659
             then
               let ses1 =
                 let uu____8667 =
                   let uu____8668 =
                     let uu____8669 =
                       tc_inductive
                         (let uu___398_8678 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___398_8678.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___398_8678.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___398_8678.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___398_8678.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___398_8678.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___398_8678.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___398_8678.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___398_8678.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___398_8678.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___398_8678.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___398_8678.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___398_8678.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___398_8678.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___398_8678.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___398_8678.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___398_8678.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___398_8678.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___398_8678.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___398_8678.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___398_8678.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___398_8678.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___398_8678.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___398_8678.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___398_8678.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___398_8678.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___398_8678.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___398_8678.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___398_8678.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___398_8678.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___398_8678.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___398_8678.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___398_8678.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___398_8678.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___398_8678.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___398_8678.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___398_8678.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___398_8678.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___398_8678.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___398_8678.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___398_8678.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___398_8678.FStar_TypeChecker_Env.nbe)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____8669
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____8668
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____8667
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____8692 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____8692
                 then
                   let uu____8697 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___399_8701 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___399_8701.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___399_8701.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___399_8701.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___399_8701.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____8697
                 else ());
                ses1)
             else ses  in
           let uu____8711 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____8711 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___400_8735 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___400_8735.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___400_8735.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___400_8735.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___400_8735.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let forfree =
             let uu____8749 =
               let uu____8750 =
                 FStar_Syntax_Subst.compress
                   (ne.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                  in
               uu____8750.FStar_Syntax_Syntax.n  in
             match uu____8749 with
             | FStar_Syntax_Syntax.Tm_unknown  -> false
             | uu____8755 ->
                 Prims.op_Negation ne.FStar_Syntax_Syntax.elaborated
              in
           if forfree
           then
             ((let uu____8768 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____8768
               then FStar_Util.print_string "Beginning DM4F run\n"
               else ());
              (let uu____8775 = cps_and_elaborate_ed env0 ne  in
               match uu____8775 with
               | (ses,ne1,lift_from_pure_opt) ->
                   let ne2 =
                     let uu___401_8808 = ne1  in
                     {
                       FStar_Syntax_Syntax.cattributes =
                         (uu___401_8808.FStar_Syntax_Syntax.cattributes);
                       FStar_Syntax_Syntax.mname =
                         (uu___401_8808.FStar_Syntax_Syntax.mname);
                       FStar_Syntax_Syntax.univs =
                         (uu___401_8808.FStar_Syntax_Syntax.univs);
                       FStar_Syntax_Syntax.binders =
                         (uu___401_8808.FStar_Syntax_Syntax.binders);
                       FStar_Syntax_Syntax.spec =
                         (uu___401_8808.FStar_Syntax_Syntax.spec);
                       FStar_Syntax_Syntax.signature =
                         (uu___401_8808.FStar_Syntax_Syntax.signature);
                       FStar_Syntax_Syntax.if_then_else =
                         (uu___401_8808.FStar_Syntax_Syntax.if_then_else);
                       FStar_Syntax_Syntax.ite_wp =
                         (uu___401_8808.FStar_Syntax_Syntax.ite_wp);
                       FStar_Syntax_Syntax.stronger =
                         (uu___401_8808.FStar_Syntax_Syntax.stronger);
                       FStar_Syntax_Syntax.close_wp =
                         (uu___401_8808.FStar_Syntax_Syntax.close_wp);
                       FStar_Syntax_Syntax.assert_p =
                         (uu___401_8808.FStar_Syntax_Syntax.assert_p);
                       FStar_Syntax_Syntax.assume_p =
                         (uu___401_8808.FStar_Syntax_Syntax.assume_p);
                       FStar_Syntax_Syntax.null_wp =
                         (uu___401_8808.FStar_Syntax_Syntax.null_wp);
                       FStar_Syntax_Syntax.trivial =
                         (uu___401_8808.FStar_Syntax_Syntax.trivial);
                       FStar_Syntax_Syntax.repr =
                         (uu___401_8808.FStar_Syntax_Syntax.repr);
                       FStar_Syntax_Syntax.elaborated = true;
                       FStar_Syntax_Syntax.spec_dm4f =
                         (uu___401_8808.FStar_Syntax_Syntax.spec_dm4f);
                       FStar_Syntax_Syntax.actions =
                         (uu___401_8808.FStar_Syntax_Syntax.actions);
                       FStar_Syntax_Syntax.eff_attrs =
                         (uu___401_8808.FStar_Syntax_Syntax.eff_attrs)
                     }  in
                   let effect_and_lift_ses =
                     match lift_from_pure_opt with
                     | FStar_Pervasives_Native.Some lift ->
                         [(let uu___402_8817 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne2);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___402_8817.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___402_8817.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___402_8817.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___402_8817.FStar_Syntax_Syntax.sigattrs)
                           });
                         lift]
                     | FStar_Pervasives_Native.None  ->
                         [(let uu___403_8819 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne2);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___403_8819.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___403_8819.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___403_8819.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___403_8819.FStar_Syntax_Syntax.sigattrs)
                           })]
                      in
                   ([], (FStar_List.append ses effect_and_lift_ses), env0)))
           else
             (let ne1 =
                let uu____8827 =
                  (FStar_Options.use_two_phase_tc ()) &&
                    (FStar_TypeChecker_Env.should_verify env)
                   in
                if uu____8827
                then
                  let ne1 =
                    let uu____8831 =
                      let uu____8832 =
                        let uu____8833 =
                          tc_eff_decl
                            (let uu___404_8835 = env  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___404_8835.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___404_8835.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___404_8835.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___404_8835.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___404_8835.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___404_8835.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___404_8835.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___404_8835.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___404_8835.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___404_8835.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___404_8835.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___404_8835.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___404_8835.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___404_8835.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___404_8835.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___404_8835.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___404_8835.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___404_8835.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___404_8835.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___404_8835.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___404_8835.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 = true;
                               FStar_TypeChecker_Env.failhard =
                                 (uu___404_8835.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___404_8835.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___404_8835.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___404_8835.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___404_8835.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___404_8835.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___404_8835.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___404_8835.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___404_8835.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___404_8835.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___404_8835.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___404_8835.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___404_8835.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___404_8835.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___404_8835.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___404_8835.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___404_8835.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___404_8835.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___404_8835.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___404_8835.FStar_TypeChecker_Env.nbe)
                             }) se ne
                           in
                        FStar_All.pipe_right uu____8833
                          (fun ne1  ->
                             let uu___405_8841 = se  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___405_8841.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___405_8841.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___405_8841.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___405_8841.FStar_Syntax_Syntax.sigattrs)
                             })
                         in
                      FStar_All.pipe_right uu____8832
                        (FStar_TypeChecker_Normalize.elim_uvars env)
                       in
                    FStar_All.pipe_right uu____8831
                      FStar_Syntax_Util.eff_decl_of_new_effect
                     in
                  ((let uu____8843 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "TwoPhases")
                       in
                    if uu____8843
                    then
                      let uu____8848 =
                        FStar_Syntax_Print.sigelt_to_string
                          (let uu___406_8852 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne1);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___406_8852.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___406_8852.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___406_8852.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___406_8852.FStar_Syntax_Syntax.sigattrs)
                           })
                         in
                      FStar_Util.print1 "Effect decl after phase 1: %s\n"
                        uu____8848
                    else ());
                   ne1)
                else ne  in
              let ne2 = tc_eff_decl env se ne1  in
              let se1 =
                let uu___407_8860 = se  in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_new_effect ne2);
                  FStar_Syntax_Syntax.sigrng =
                    (uu___407_8860.FStar_Syntax_Syntax.sigrng);
                  FStar_Syntax_Syntax.sigquals =
                    (uu___407_8860.FStar_Syntax_Syntax.sigquals);
                  FStar_Syntax_Syntax.sigmeta =
                    (uu___407_8860.FStar_Syntax_Syntax.sigmeta);
                  FStar_Syntax_Syntax.sigattrs =
                    (uu___407_8860.FStar_Syntax_Syntax.sigattrs)
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
           let uu____8868 =
             let uu____8875 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____8875
              in
           (match uu____8868 with
            | (a,wp_a_src) ->
                let uu____8892 =
                  let uu____8899 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____8899
                   in
                (match uu____8892 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____8917 =
                         let uu____8920 =
                           let uu____8921 =
                             let uu____8928 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____8928)  in
                           FStar_Syntax_Syntax.NT uu____8921  in
                         [uu____8920]  in
                       FStar_Syntax_Subst.subst uu____8917 wp_b_tgt  in
                     let expected_k =
                       let uu____8936 =
                         let uu____8945 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____8952 =
                           let uu____8961 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____8961]  in
                         uu____8945 :: uu____8952  in
                       let uu____8986 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____8936 uu____8986  in
                     let repr_type eff_name a1 wp =
                       (let uu____9008 =
                          let uu____9010 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____9010  in
                        if uu____9008
                        then
                          let uu____9013 =
                            let uu____9019 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____9019)
                             in
                          let uu____9023 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____9013 uu____9023
                        else ());
                       (let uu____9026 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____9026 with
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
                            let uu____9063 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____9064 =
                              let uu____9071 =
                                let uu____9072 =
                                  let uu____9089 =
                                    let uu____9100 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____9109 =
                                      let uu____9120 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____9120]  in
                                    uu____9100 :: uu____9109  in
                                  (repr, uu____9089)  in
                                FStar_Syntax_Syntax.Tm_app uu____9072  in
                              FStar_Syntax_Syntax.mk uu____9071  in
                            uu____9064 FStar_Pervasives_Native.None
                              uu____9063)
                        in
                     let uu____9168 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____9341 =
                             if
                               (FStar_List.length uvs) >
                                 (Prims.parse_int "0")
                             then
                               let uu____9352 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____9352 with
                               | (usubst,uvs1) ->
                                   let uu____9375 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____9376 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____9375, uu____9376)
                             else (env, lift_wp)  in
                           (match uu____9341 with
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
                                     let uu____9426 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____9426))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____9497 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____9512 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____9512 with
                               | (usubst,uvs) ->
                                   let uu____9537 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____9537)
                             else ([], lift)  in
                           (match uu____9497 with
                            | (uvs,lift1) ->
                                ((let uu____9573 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____9573
                                  then
                                    let uu____9577 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____9577
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____9583 =
                                    let uu____9590 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____9590 lift1
                                     in
                                  match uu____9583 with
                                  | (lift2,comp,uu____9615) ->
                                      let uu____9616 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____9616 with
                                       | (uu____9645,lift_wp,lift_elab) ->
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
                                             let uu____9677 =
                                               let uu____9688 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____9688
                                                in
                                             let uu____9705 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____9677, uu____9705)
                                           else
                                             (let uu____9734 =
                                                let uu____9745 =
                                                  let uu____9754 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____9754)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____9745
                                                 in
                                              let uu____9769 =
                                                let uu____9778 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____9778)  in
                                              (uu____9734, uu____9769))))))
                        in
                     (match uu____9168 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___408_9852 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___408_9852.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___408_9852.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___408_9852.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___408_9852.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___408_9852.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___408_9852.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___408_9852.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___408_9852.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___408_9852.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___408_9852.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___408_9852.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___408_9852.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___408_9852.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___408_9852.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___408_9852.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___408_9852.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___408_9852.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___408_9852.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___408_9852.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___408_9852.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___408_9852.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___408_9852.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___408_9852.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___408_9852.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___408_9852.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___408_9852.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___408_9852.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___408_9852.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___408_9852.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___408_9852.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___408_9852.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___408_9852.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___408_9852.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___408_9852.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___408_9852.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___408_9852.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___408_9852.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___408_9852.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___408_9852.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___408_9852.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___408_9852.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___408_9852.FStar_TypeChecker_Env.nbe)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____9885 =
                                  let uu____9890 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____9890 with
                                  | (usubst,uvs1) ->
                                      let uu____9913 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____9914 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____9913, uu____9914)
                                   in
                                (match uu____9885 with
                                 | (env2,lift2) ->
                                     let uu____9919 =
                                       let uu____9926 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____9926
                                        in
                                     (match uu____9919 with
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
                                              let uu____9952 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____9953 =
                                                let uu____9960 =
                                                  let uu____9961 =
                                                    let uu____9978 =
                                                      let uu____9989 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____9998 =
                                                        let uu____10009 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____10009]  in
                                                      uu____9989 ::
                                                        uu____9998
                                                       in
                                                    (lift_wp1, uu____9978)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____9961
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____9960
                                                 in
                                              uu____9953
                                                FStar_Pervasives_Native.None
                                                uu____9952
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____10060 =
                                              let uu____10069 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____10076 =
                                                let uu____10085 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____10092 =
                                                  let uu____10101 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____10101]  in
                                                uu____10085 :: uu____10092
                                                 in
                                              uu____10069 :: uu____10076  in
                                            let uu____10132 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____10060 uu____10132
                                             in
                                          let uu____10135 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____10135 with
                                           | (expected_k2,uu____10145,uu____10146)
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
                                                    let uu____10154 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____10154))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____10162 =
                              let uu____10164 =
                                let uu____10166 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____10166
                                  FStar_List.length
                                 in
                              uu____10164 <> (Prims.parse_int "1")  in
                            if uu____10162
                            then
                              let uu____10188 =
                                let uu____10194 =
                                  let uu____10196 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10198 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10200 =
                                    let uu____10202 =
                                      let uu____10204 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10204
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10202
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10196 uu____10198 uu____10200
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10194)
                                 in
                              FStar_Errors.raise_error uu____10188 r
                            else ());
                           (let uu____10231 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____10234 =
                                   let uu____10236 =
                                     let uu____10239 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____10239
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____10236
                                     FStar_List.length
                                    in
                                 uu____10234 <> (Prims.parse_int "1"))
                               in
                            if uu____10231
                            then
                              let uu____10277 =
                                let uu____10283 =
                                  let uu____10285 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10287 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10289 =
                                    let uu____10291 =
                                      let uu____10293 =
                                        let uu____10296 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____10296
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10293
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10291
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10285 uu____10287 uu____10289
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10283)
                                 in
                              FStar_Errors.raise_error uu____10277 r
                            else ());
                           (let sub2 =
                              let uu___409_10339 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___409_10339.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___409_10339.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___410_10341 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___410_10341.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___410_10341.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___410_10341.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___410_10341.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let uu____10355 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (env, uvs, tps, c)
             else
               (let uu____10383 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____10383 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____10414 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____10414 c  in
                    let uu____10423 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____10423, uvs1, tps1, c1))
              in
           (match uu____10355 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____10445 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____10445 with
                 | (tps2,c2) ->
                     let uu____10462 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____10462 with
                      | (tps3,env3,us) ->
                          let uu____10482 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____10482 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____10510)::uu____10511 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____10530 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____10538 =
                                   let uu____10540 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____10540  in
                                 if uu____10538
                                 then
                                   let uu____10543 =
                                     let uu____10549 =
                                       let uu____10551 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____10553 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____10551 uu____10553
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____10549)
                                      in
                                   FStar_Errors.raise_error uu____10543 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____10561 =
                                   let uu____10562 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____10562
                                    in
                                 match uu____10561 with
                                 | (uvs2,t) ->
                                     let uu____10593 =
                                       let uu____10598 =
                                         let uu____10611 =
                                           let uu____10612 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10612.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____10611)  in
                                       match uu____10598 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____10627,c5)) -> ([], c5)
                                       | (uu____10669,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____10708 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____10593 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____10742 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____10742 with
                                              | (uu____10747,t1) ->
                                                  let uu____10749 =
                                                    let uu____10755 =
                                                      let uu____10757 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____10759 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____10763 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____10757
                                                        uu____10759
                                                        uu____10763
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____10755)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____10749 r)
                                           else ();
                                           (let se1 =
                                              let uu___411_10770 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags1));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___411_10770.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___411_10770.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___411_10770.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___411_10770.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____10777,uu____10778,uu____10779) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___375_10784  ->
                   match uu___375_10784 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____10787 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____10793,uu____10794) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___375_10803  ->
                   match uu___375_10803 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____10806 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____10817 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____10817
             then
               let uu____10820 =
                 let uu____10826 =
                   let uu____10828 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____10828
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____10826)
                  in
               FStar_Errors.raise_error uu____10820 r
             else ());
            (let uu____10834 =
               let uu____10843 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____10843
               then
                 let uu____10854 =
                   tc_declare_typ
                     (let uu___412_10857 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___412_10857.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___412_10857.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___412_10857.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___412_10857.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___412_10857.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___412_10857.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___412_10857.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___412_10857.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___412_10857.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___412_10857.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___412_10857.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___412_10857.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___412_10857.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___412_10857.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___412_10857.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___412_10857.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___412_10857.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___412_10857.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___412_10857.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___412_10857.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___412_10857.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___412_10857.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___412_10857.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___412_10857.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___412_10857.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___412_10857.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___412_10857.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___412_10857.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___412_10857.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___412_10857.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___412_10857.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___412_10857.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___412_10857.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___412_10857.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___412_10857.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___412_10857.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___412_10857.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___412_10857.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___412_10857.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___412_10857.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___412_10857.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___412_10857.FStar_TypeChecker_Env.nbe)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____10854 with
                 | (uvs1,t1) ->
                     ((let uu____10882 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____10882
                       then
                         let uu____10887 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____10889 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____10887 uu____10889
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____10834 with
             | (uvs1,t1) ->
                 let uu____10924 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____10924 with
                  | (uvs2,t2) ->
                      ([(let uu___413_10954 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___413_10954.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___413_10954.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___413_10954.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___413_10954.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____10959 =
             let uu____10968 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____10968
             then
               let uu____10979 =
                 tc_assume
                   (let uu___414_10982 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___414_10982.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___414_10982.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___414_10982.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___414_10982.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___414_10982.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___414_10982.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___414_10982.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___414_10982.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___414_10982.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___414_10982.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___414_10982.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___414_10982.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___414_10982.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___414_10982.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___414_10982.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___414_10982.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___414_10982.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___414_10982.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___414_10982.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___414_10982.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___414_10982.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___414_10982.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___414_10982.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___414_10982.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___414_10982.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___414_10982.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___414_10982.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___414_10982.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___414_10982.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___414_10982.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___414_10982.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___414_10982.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___414_10982.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___414_10982.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___414_10982.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___414_10982.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___414_10982.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___414_10982.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___414_10982.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___414_10982.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___414_10982.FStar_TypeChecker_Env.nbe)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____10979 with
               | (uvs1,t1) ->
                   ((let uu____11008 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____11008
                     then
                       let uu____11013 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____11015 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____11013
                         uu____11015
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____10959 with
            | (uvs1,t1) ->
                let uu____11050 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____11050 with
                 | (uvs2,t2) ->
                     ([(let uu___415_11080 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___415_11080.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___415_11080.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___415_11080.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___415_11080.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____11084 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____11084 with
            | (e1,c,g1) ->
                let uu____11104 =
                  let uu____11111 =
                    let uu____11114 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____11114  in
                  let uu____11115 =
                    let uu____11120 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____11120)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____11111 uu____11115
                   in
                (match uu____11104 with
                 | (e2,uu____11132,g) ->
                     ((let uu____11135 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____11135);
                      (let se1 =
                         let uu___416_11137 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___416_11137.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___416_11137.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___416_11137.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___416_11137.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____11149 = FStar_Options.debug_any ()  in
             if uu____11149
             then
               let uu____11152 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____11154 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____11152
                 uu____11154
             else ());
            (let uu____11159 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____11159 with
             | (t1,uu____11177,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____11191 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____11191 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____11194 =
                              let uu____11200 =
                                let uu____11202 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____11204 =
                                  let uu____11206 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____11206
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____11202 uu____11204
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____11200)
                               in
                            FStar_Errors.raise_error uu____11194 r
                        | uu____11218 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___417_11223 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___417_11223.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___417_11223.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___417_11223.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___417_11223.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___417_11223.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___417_11223.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___417_11223.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___417_11223.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___417_11223.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___417_11223.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___417_11223.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___417_11223.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___417_11223.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___417_11223.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___417_11223.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___417_11223.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___417_11223.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___417_11223.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___417_11223.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___417_11223.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___417_11223.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___417_11223.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___417_11223.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___417_11223.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___417_11223.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___417_11223.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___417_11223.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___417_11223.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___417_11223.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___417_11223.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___417_11223.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___417_11223.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___417_11223.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___417_11223.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___417_11223.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___417_11223.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___417_11223.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___417_11223.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___417_11223.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___417_11223.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___417_11223.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___417_11223.FStar_TypeChecker_Env.nbe)
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
                 let uu____11291 =
                   let uu____11293 =
                     let uu____11302 = drop_logic val_q  in
                     let uu____11305 = drop_logic q'  in
                     (uu____11302, uu____11305)  in
                   match uu____11293 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____11291
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____11332 =
                      let uu____11338 =
                        let uu____11340 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____11342 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____11344 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____11340 uu____11342 uu____11344
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____11338)
                       in
                    FStar_Errors.raise_error uu____11332 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____11381 =
                   let uu____11382 = FStar_Syntax_Subst.compress def  in
                   uu____11382.FStar_Syntax_Syntax.n  in
                 match uu____11381 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____11394,uu____11395) -> binders
                 | uu____11420 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____11432;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____11537) -> val_bs1
                     | (uu____11568,[]) -> val_bs1
                     | ((body_bv,uu____11600)::bt,(val_bv,aqual)::vt) ->
                         let uu____11657 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____11681) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___418_11695 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___419_11698 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___419_11698.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___418_11695.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___418_11695.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____11657
                      in
                   let uu____11705 =
                     let uu____11712 =
                       let uu____11713 =
                         let uu____11728 = rename_binders1 def_bs val_bs  in
                         (uu____11728, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____11713  in
                     FStar_Syntax_Syntax.mk uu____11712  in
                   uu____11705 FStar_Pervasives_Native.None r1
               | uu____11750 -> typ1  in
             let uu___420_11751 = lb  in
             let uu____11752 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___420_11751.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___420_11751.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____11752;
               FStar_Syntax_Syntax.lbeff =
                 (uu___420_11751.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___420_11751.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___420_11751.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___420_11751.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____11755 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____11810  ->
                     fun lb  ->
                       match uu____11810 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____11856 =
                             let uu____11868 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____11868 with
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
                                   | uu____11948 ->
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
                                  (let uu____11995 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____11995, quals_opt1)))
                              in
                           (match uu____11856 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____11755 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____12099 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___376_12105  ->
                                match uu___376_12105 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____12110 -> false))
                         in
                      if uu____12099
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____12123 =
                    let uu____12130 =
                      let uu____12131 =
                        let uu____12145 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____12145)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____12131  in
                    FStar_Syntax_Syntax.mk uu____12130  in
                  uu____12123 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___421_12167 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___421_12167.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___421_12167.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___421_12167.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___421_12167.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___421_12167.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___421_12167.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___421_12167.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___421_12167.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___421_12167.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___421_12167.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___421_12167.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___421_12167.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___421_12167.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___421_12167.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___421_12167.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___421_12167.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___421_12167.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___421_12167.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___421_12167.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___421_12167.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___421_12167.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___421_12167.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___421_12167.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___421_12167.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___421_12167.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___421_12167.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___421_12167.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___421_12167.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___421_12167.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___421_12167.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___421_12167.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___421_12167.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___421_12167.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___421_12167.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___421_12167.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___421_12167.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___421_12167.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___421_12167.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___421_12167.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___421_12167.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___421_12167.FStar_TypeChecker_Env.nbe)
                  }  in
                let e1 =
                  let uu____12170 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____12170
                  then
                    let drop_lbtyp e_lax =
                      let uu____12179 =
                        let uu____12180 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____12180.FStar_Syntax_Syntax.n  in
                      match uu____12179 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____12202 =
                              let uu____12203 = FStar_Syntax_Subst.compress e
                                 in
                              uu____12203.FStar_Syntax_Syntax.n  in
                            match uu____12202 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____12207,lb1::[]),uu____12209) ->
                                let uu____12225 =
                                  let uu____12226 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____12226.FStar_Syntax_Syntax.n  in
                                (match uu____12225 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____12231 -> false)
                            | uu____12233 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___422_12237 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___423_12252 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___423_12252.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___423_12252.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___423_12252.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___423_12252.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___423_12252.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___423_12252.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___422_12237.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___422_12237.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____12255 -> e_lax  in
                    let e1 =
                      let uu____12257 =
                        let uu____12258 =
                          let uu____12259 =
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              (let uu___424_12268 = env'  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___424_12268.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___424_12268.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___424_12268.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___424_12268.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___424_12268.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___424_12268.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___424_12268.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___424_12268.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___424_12268.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___424_12268.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___424_12268.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___424_12268.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___424_12268.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___424_12268.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___424_12268.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___424_12268.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___424_12268.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___424_12268.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___424_12268.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___424_12268.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___424_12268.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 = true;
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___424_12268.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___424_12268.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___424_12268.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___424_12268.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___424_12268.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___424_12268.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___424_12268.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___424_12268.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___424_12268.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___424_12268.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___424_12268.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___424_12268.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___424_12268.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___424_12268.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___424_12268.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___424_12268.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___424_12268.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___424_12268.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___424_12268.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___424_12268.FStar_TypeChecker_Env.nbe)
                               }) e
                             in
                          FStar_All.pipe_right uu____12259
                            (fun uu____12281  ->
                               match uu____12281 with
                               | (e1,uu____12289,uu____12290) -> e1)
                           in
                        FStar_All.pipe_right uu____12258
                          (FStar_TypeChecker_Normalize.remove_uvar_solutions
                             env')
                         in
                      FStar_All.pipe_right uu____12257 drop_lbtyp  in
                    ((let uu____12292 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "TwoPhases")
                         in
                      if uu____12292
                      then
                        let uu____12297 =
                          FStar_Syntax_Print.term_to_string e1  in
                        FStar_Util.print1 "Let binding after phase 1: %s\n"
                          uu____12297
                      else ());
                     e1)
                  else e  in
                let uu____12304 =
                  let uu____12313 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____12313 with
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
                (match uu____12304 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___425_12418 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___425_12418.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___425_12418.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___425_12418.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___425_12418.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___426_12431 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___426_12431.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___426_12431.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___426_12431.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___426_12431.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___426_12431.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___426_12431.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____12432 =
                       let uu____12444 =
                         FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env'
                           e1
                          in
                       match uu____12444 with
                       | ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                            FStar_Syntax_Syntax.pos = uu____12464;
                            FStar_Syntax_Syntax.vars = uu____12465;_},uu____12466,g)
                           when FStar_TypeChecker_Env.is_trivial g ->
                           let lbs2 =
                             let uu____12496 =
                               FStar_All.pipe_right
                                 (FStar_Pervasives_Native.snd lbs1)
                                 (FStar_List.map rename_parameters)
                                in
                             ((FStar_Pervasives_Native.fst lbs1),
                               uu____12496)
                              in
                           let lbs3 =
                             let uu____12520 =
                               match post_tau with
                               | FStar_Pervasives_Native.Some tau ->
                                   FStar_List.map (postprocess_lb tau)
                                     (FStar_Pervasives_Native.snd lbs2)
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.snd lbs2
                                in
                             ((FStar_Pervasives_Native.fst lbs2),
                               uu____12520)
                              in
                           let quals1 =
                             match e2.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_meta
                                 (uu____12543,FStar_Syntax_Syntax.Meta_desugared
                                  (FStar_Syntax_Syntax.Masked_effect ))
                                 -> FStar_Syntax_Syntax.HasMaskedEffect ::
                                 quals
                             | uu____12548 -> quals  in
                           ((let uu___427_12557 = se1  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_let (lbs3, lids));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___427_12557.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals = quals1;
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___427_12557.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___427_12557.FStar_Syntax_Syntax.sigattrs)
                             }), lbs3)
                       | uu____12560 ->
                           failwith
                             "impossible (typechecking should preserve Tm_let)"
                        in
                     (match uu____12432 with
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
                           (let uu____12616 = log env1  in
                            if uu____12616
                            then
                              let uu____12619 =
                                let uu____12621 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs1)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let should_log =
                                            let uu____12641 =
                                              let uu____12650 =
                                                let uu____12651 =
                                                  let uu____12654 =
                                                    FStar_Util.right
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  uu____12654.FStar_Syntax_Syntax.fv_name
                                                   in
                                                uu____12651.FStar_Syntax_Syntax.v
                                                 in
                                              FStar_TypeChecker_Env.try_lookup_val_decl
                                                env1 uu____12650
                                               in
                                            match uu____12641 with
                                            | FStar_Pervasives_Native.None 
                                                -> true
                                            | uu____12663 -> false  in
                                          if should_log
                                          then
                                            let uu____12675 =
                                              FStar_Syntax_Print.lbname_to_string
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            let uu____12677 =
                                              FStar_Syntax_Print.term_to_string
                                                lb.FStar_Syntax_Syntax.lbtyp
                                               in
                                            FStar_Util.format2 "let %s : %s"
                                              uu____12675 uu____12677
                                          else ""))
                                   in
                                FStar_All.pipe_right uu____12621
                                  (FStar_String.concat "\n")
                                 in
                              FStar_Util.print1 "%s\n" uu____12619
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
      (let uu____12729 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____12729
       then
         let uu____12732 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____12732
       else ());
      (let uu____12737 = get_fail_se se  in
       match uu____12737 with
       | FStar_Pervasives_Native.Some (uu____12758,false ) when
           let uu____12775 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____12775 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___428_12801 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___428_12801.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___428_12801.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___428_12801.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___428_12801.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___428_12801.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___428_12801.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___428_12801.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___428_12801.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___428_12801.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___428_12801.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___428_12801.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___428_12801.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___428_12801.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___428_12801.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___428_12801.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___428_12801.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___428_12801.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___428_12801.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___428_12801.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___428_12801.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___428_12801.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___428_12801.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___428_12801.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___428_12801.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___428_12801.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___428_12801.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___428_12801.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___428_12801.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___428_12801.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___428_12801.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___428_12801.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___428_12801.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___428_12801.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___428_12801.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___428_12801.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___428_12801.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___428_12801.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___428_12801.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___428_12801.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___428_12801.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___428_12801.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___428_12801.FStar_TypeChecker_Env.nbe)
               }
             else env1  in
           ((let uu____12806 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____12806
             then
               let uu____12809 =
                 let uu____12811 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____12811
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____12809
             else ());
            (let uu____12825 =
               FStar_Errors.catch_errors
                 (fun uu____12855  ->
                    FStar_Options.with_saved_options
                      (fun uu____12867  -> tc_decl' env' se))
                in
             match uu____12825 with
             | (errs,uu____12879) ->
                 ((let uu____12909 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____12909
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____12944 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____12944  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____12956 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____12967 =
                            let uu____12977 =
                              check_multi_contained errnos1 actual  in
                            match uu____12977 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")))
                             in
                          (match uu____12967 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____13042 =
                                   let uu____13048 =
                                     let uu____13050 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____13053 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____13056 =
                                       FStar_Util.string_of_int e  in
                                     let uu____13058 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____13060 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____13050 uu____13053 uu____13056
                                       uu____13058 uu____13060
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____13048)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____13042)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____13087 .
    'Auu____13087 ->
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
               (fun uu___377_13130  ->
                  match uu___377_13130 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____13133 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____13144) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____13152 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____13162 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____13167 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____13183 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____13209 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13235) ->
            let uu____13244 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13244
            then
              let for_export_bundle se1 uu____13281 =
                match uu____13281 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____13320,uu____13321) ->
                         let dec =
                           let uu___429_13331 = se1  in
                           let uu____13332 =
                             let uu____13333 =
                               let uu____13340 =
                                 let uu____13341 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____13341  in
                               (l, us, uu____13340)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____13333
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____13332;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___429_13331.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___429_13331.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___429_13331.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____13351,uu____13352,uu____13353) ->
                         let dec =
                           let uu___430_13361 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___430_13361.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___430_13361.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___430_13361.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____13366 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____13389,uu____13390,uu____13391) ->
            let uu____13392 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13392 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____13416 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____13416
            then
              ([(let uu___431_13435 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___431_13435.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___431_13435.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___431_13435.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____13438 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___378_13444  ->
                         match uu___378_13444 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____13447 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____13453 ->
                             true
                         | uu____13455 -> false))
                  in
               if uu____13438 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____13476 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____13481 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____13486 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13491 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13509) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____13523 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____13523
            then ([], hidden)
            else
              (let dec =
                 let uu____13544 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____13544;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____13555 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13555
            then
              let uu____13566 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___432_13580 = se  in
                        let uu____13581 =
                          let uu____13582 =
                            let uu____13589 =
                              let uu____13590 =
                                let uu____13593 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____13593.FStar_Syntax_Syntax.fv_name  in
                              uu____13590.FStar_Syntax_Syntax.v  in
                            (uu____13589, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____13582  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____13581;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___432_13580.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___432_13580.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___432_13580.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____13566, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____13616 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____13616
       then
         let uu____13619 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____13619
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____13624 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____13642 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____13659) -> z3_reset_options env
       | FStar_Syntax_Syntax.Sig_pragma uu____13663 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____13673 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____13673) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____13674,uu____13675,uu____13676) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_13681  ->
                   match uu___379_13681 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13684 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____13686,uu____13687) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_13696  ->
                   match uu___379_13696 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13699 -> false))
           -> env
       | uu____13701 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____13770 se =
        match uu____13770 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____13823 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____13823
              then
                let uu____13826 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____13826
              else ());
             (let uu____13831 = tc_decl env1 se  in
              match uu____13831 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____13884 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____13884
                             then
                               let uu____13888 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____13888
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____13904 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____13904
                             then
                               let uu____13908 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____13908
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
                    (let uu____13925 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____13925
                     then
                       let uu____13930 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____13939 =
                                  let uu____13941 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____13941 "\n"  in
                                Prims.strcat s uu____13939) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____13930
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____13951 =
                       let uu____13960 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____13960
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____14002 se1 =
                            match uu____14002 with
                            | (exports1,hidden1) ->
                                let uu____14030 = for_export env3 hidden1 se1
                                   in
                                (match uu____14030 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____13951 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____14184 = acc  in
        match uu____14184 with
        | (uu____14219,uu____14220,env1,uu____14222) ->
            let uu____14235 =
              FStar_Util.record_time
                (fun uu____14282  -> process_one_decl acc se)
               in
            (match uu____14235 with
             | (r,ms_elapsed) ->
                 ((let uu____14348 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____14348
                   then
                     let uu____14352 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____14354 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____14352 uu____14354
                   else ());
                  r))
         in
      let uu____14359 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____14359 with
      | (ses1,exports,env1,uu____14407) ->
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
          let uu___433_14445 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___433_14445.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___433_14445.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___433_14445.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___433_14445.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___433_14445.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___433_14445.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___433_14445.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___433_14445.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___433_14445.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___433_14445.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___433_14445.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___433_14445.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___433_14445.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___433_14445.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___433_14445.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___433_14445.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___433_14445.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___433_14445.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___433_14445.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___433_14445.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___433_14445.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___433_14445.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___433_14445.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___433_14445.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___433_14445.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___433_14445.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___433_14445.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___433_14445.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___433_14445.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___433_14445.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___433_14445.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___433_14445.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___433_14445.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___433_14445.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___433_14445.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___433_14445.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___433_14445.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___433_14445.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___433_14445.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___433_14445.FStar_TypeChecker_Env.nbe)
          }  in
        let check_term lid univs1 t =
          let uu____14465 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____14465 with
          | (univs2,t1) ->
              ((let uu____14473 =
                  let uu____14475 =
                    let uu____14481 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____14481  in
                  FStar_All.pipe_left uu____14475
                    (FStar_Options.Other "Exports")
                   in
                if uu____14473
                then
                  let uu____14485 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____14487 =
                    let uu____14489 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____14489
                      (FStar_String.concat ", ")
                     in
                  let uu____14506 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____14485 uu____14487 uu____14506
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____14512 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____14512 (fun a1  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____14538 =
             let uu____14540 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____14542 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____14540 uu____14542
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____14538);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14553) ->
              let uu____14562 =
                let uu____14564 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14564  in
              if uu____14562
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____14578,uu____14579) ->
              let t =
                let uu____14591 =
                  let uu____14598 =
                    let uu____14599 =
                      let uu____14614 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____14614)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____14599  in
                  FStar_Syntax_Syntax.mk uu____14598  in
                uu____14591 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____14633,uu____14634,uu____14635) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____14645 =
                let uu____14647 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14647  in
              if uu____14645 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____14655,lbs),uu____14657) ->
              let uu____14668 =
                let uu____14670 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14670  in
              if uu____14668
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
              let uu____14693 =
                let uu____14695 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14695  in
              if uu____14693
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____14716 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____14717 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14724 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____14725 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____14726 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____14733 -> ()  in
        let uu____14734 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____14734 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____14840) -> true
             | uu____14842 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____14872 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____14911 ->
                   let uu____14912 =
                     let uu____14919 =
                       let uu____14920 =
                         let uu____14935 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____14935)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____14920  in
                     FStar_Syntax_Syntax.mk uu____14919  in
                   uu____14912 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____14955,uu____14956) ->
            let s1 =
              let uu___434_14966 = s  in
              let uu____14967 =
                let uu____14968 =
                  let uu____14975 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____14975)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____14968  in
              let uu____14976 =
                let uu____14979 =
                  let uu____14982 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____14982  in
                FStar_Syntax_Syntax.Assumption :: uu____14979  in
              {
                FStar_Syntax_Syntax.sigel = uu____14967;
                FStar_Syntax_Syntax.sigrng =
                  (uu___434_14966.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____14976;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___434_14966.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___434_14966.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____14985 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____15010 lbdef =
        match uu____15010 with
        | (uvs,t) ->
            let attrs =
              let uu____15021 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____15021
              then
                let uu____15026 =
                  let uu____15027 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____15027
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____15026 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___435_15030 = s  in
            let uu____15031 =
              let uu____15034 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____15034  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___435_15030.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____15031;
              FStar_Syntax_Syntax.sigmeta =
                (uu___435_15030.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____15052 -> failwith "Impossible!"  in
        let c_opt =
          let uu____15059 = FStar_Syntax_Util.is_unit t  in
          if uu____15059
          then
            let uu____15066 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____15066
          else
            (let uu____15073 =
               let uu____15074 = FStar_Syntax_Subst.compress t  in
               uu____15074.FStar_Syntax_Syntax.n  in
             match uu____15073 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____15081,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____15105 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____15117 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____15117
            then false
            else
              (let uu____15124 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____15124
               then true
               else
                 (let uu____15131 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____15131))
         in
      let extract_sigelt s =
        (let uu____15143 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____15143
         then
           let uu____15146 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____15146
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____15153 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____15173 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____15192 ->
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
                             (lid,uu____15238,uu____15239,uu____15240,uu____15241,uu____15242)
                             ->
                             ((let uu____15252 =
                                 let uu____15255 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____15255  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____15252);
                              (let uu____15348 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____15348 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____15352,uu____15353,uu____15354,uu____15355,uu____15356)
                             ->
                             ((let uu____15364 =
                                 let uu____15367 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____15367  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____15364);
                              sigelts1)
                         | uu____15460 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____15469 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15469
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____15479 =
                    let uu___436_15480 = s  in
                    let uu____15481 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___436_15480.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___436_15480.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15481;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___436_15480.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___436_15480.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15479])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____15492 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15492
             then []
             else
               (let uu____15499 = lbs  in
                match uu____15499 with
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
                        (fun uu____15561  ->
                           match uu____15561 with
                           | (uu____15569,t,uu____15571) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____15588  ->
                             match uu____15588 with
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
                           (fun uu____15615  ->
                              match uu____15615 with
                              | (uu____15623,t,uu____15625) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____15637,uu____15638) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____15646 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____15697 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____15697) uu____15646
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____15701 =
                    let uu___437_15702 = s  in
                    let uu____15703 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___437_15702.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___437_15702.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15703;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___437_15702.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___437_15702.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15701]
                else [])
             else
               (let uu____15710 =
                  let uu___438_15711 = s  in
                  let uu____15712 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___438_15711.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___438_15711.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____15712;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___438_15711.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___438_15711.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____15710])
         | FStar_Syntax_Syntax.Sig_new_effect uu____15715 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____15716 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15717 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____15730 -> [s])
         in
      let uu___439_15731 = m  in
      let uu____15732 =
        let uu____15733 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____15733 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___439_15731.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____15732;
        FStar_Syntax_Syntax.exports =
          (uu___439_15731.FStar_Syntax_Syntax.exports);
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
        (fun uu____15784  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____15832  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             solver.FStar_TypeChecker_Env.refresh (); env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____15848 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____15848
  
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
      (let uu____15937 = FStar_Options.debug_any ()  in
       if uu____15937
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
         let uu___440_15953 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___440_15953.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___440_15953.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___440_15953.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___440_15953.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___440_15953.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___440_15953.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___440_15953.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___440_15953.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___440_15953.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___440_15953.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___440_15953.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___440_15953.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___440_15953.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___440_15953.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___440_15953.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___440_15953.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___440_15953.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___440_15953.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___440_15953.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___440_15953.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___440_15953.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___440_15953.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___440_15953.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___440_15953.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___440_15953.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___440_15953.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___440_15953.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___440_15953.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___440_15953.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___440_15953.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___440_15953.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___440_15953.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___440_15953.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___440_15953.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___440_15953.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___440_15953.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___440_15953.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___440_15953.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___440_15953.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___440_15953.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___440_15953.FStar_TypeChecker_Env.nbe)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____15955 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____15955 with
       | (ses,exports,env3) ->
           ((let uu___441_15988 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___441_15988.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___441_15988.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___441_15988.FStar_Syntax_Syntax.is_interface)
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
        let uu____16017 = tc_decls env decls  in
        match uu____16017 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___442_16048 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___442_16048.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___442_16048.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___442_16048.FStar_Syntax_Syntax.is_interface)
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
        let uu____16109 = tc_partial_modul env01 m  in
        match uu____16109 with
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
                (let uu____16146 = FStar_Errors.get_err_count ()  in
                 uu____16146 = (Prims.parse_int "0"))
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____16157 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____16157
                then
                  let uu____16161 =
                    let uu____16163 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16163 then "" else " (in lax mode) "  in
                  let uu____16171 =
                    let uu____16173 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16173
                    then
                      let uu____16177 =
                        let uu____16179 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.strcat uu____16179 "\n"  in
                      Prims.strcat "\nfrom: " uu____16177
                    else ""  in
                  let uu____16186 =
                    let uu____16188 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16188
                    then
                      let uu____16192 =
                        let uu____16194 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.strcat uu____16194 "\n"  in
                      Prims.strcat "\nto: " uu____16192
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____16161
                    uu____16171 uu____16186
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.strcat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___443_16208 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___443_16208.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___443_16208.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___443_16208.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___443_16208.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___443_16208.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___443_16208.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___443_16208.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___443_16208.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___443_16208.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___443_16208.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___443_16208.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___443_16208.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___443_16208.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___443_16208.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___443_16208.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___443_16208.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___443_16208.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___443_16208.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___443_16208.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___443_16208.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___443_16208.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___443_16208.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___443_16208.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___443_16208.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___443_16208.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___443_16208.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___443_16208.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___443_16208.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___443_16208.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___443_16208.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___443_16208.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___443_16208.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___443_16208.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___443_16208.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___443_16208.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___443_16208.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___443_16208.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___443_16208.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___443_16208.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___443_16208.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___443_16208.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___443_16208.FStar_TypeChecker_Env.nbe)
                    }  in
                  let en02 =
                    let uu___444_16210 = en01  in
                    let uu____16211 =
                      let uu____16226 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____16226, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___444_16210.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___444_16210.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___444_16210.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___444_16210.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___444_16210.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___444_16210.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___444_16210.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___444_16210.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___444_16210.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___444_16210.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___444_16210.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___444_16210.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___444_16210.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___444_16210.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___444_16210.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___444_16210.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___444_16210.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___444_16210.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___444_16210.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___444_16210.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___444_16210.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___444_16210.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___444_16210.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___444_16210.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___444_16210.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___444_16210.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___444_16210.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___444_16210.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___444_16210.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___444_16210.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___444_16210.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____16211;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___444_16210.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___444_16210.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___444_16210.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___444_16210.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___444_16210.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___444_16210.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___444_16210.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___444_16210.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___444_16210.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___444_16210.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___444_16210.FStar_TypeChecker_Env.nbe)
                    }  in
                  let uu____16272 =
                    let uu____16274 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____16274  in
                  if uu____16272
                  then
                    ((let uu____16278 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____16278 (fun a2  -> ()));
                     z3_reset_options en02)
                  else en02  in
                let uu____16282 = tc_modul en0 modul_iface true  in
                match uu____16282 with
                | (modul_iface1,env) ->
                    ((let uu___445_16295 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___445_16295.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___445_16295.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___445_16295.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___446_16299 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___446_16299.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___446_16299.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___446_16299.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____16302 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____16302 FStar_Util.smap_clear);
               (let uu____16338 =
                  ((let uu____16342 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____16342) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____16345 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____16345)
                   in
                if uu____16338 then check_exports env modul exports else ());
               (let uu____16351 =
                  pop_context env
                    (Prims.strcat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____16351 (fun a3  -> ()));
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
                 env modul;
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ();
               (let uu____16356 =
                  let uu____16358 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____16358  in
                if uu____16356
                then
                  let uu____16361 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____16361 (fun a4  -> ())
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
        let uu____16378 =
          let uu____16380 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____16380  in
        push_context env uu____16378  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____16401 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____16412 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____16412 with | (uu____16419,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____16444 = FStar_Options.debug_any ()  in
         if uu____16444
         then
           let uu____16447 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____16447
         else ());
        (let uu____16459 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____16459
         then
           let uu____16462 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____16462
         else ());
        (let env1 =
           let uu___447_16468 = env  in
           let uu____16469 =
             let uu____16471 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____16471  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___447_16468.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___447_16468.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___447_16468.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___447_16468.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___447_16468.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___447_16468.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___447_16468.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___447_16468.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___447_16468.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___447_16468.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___447_16468.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___447_16468.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___447_16468.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___447_16468.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___447_16468.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___447_16468.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___447_16468.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___447_16468.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___447_16468.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___447_16468.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____16469;
             FStar_TypeChecker_Env.lax_universes =
               (uu___447_16468.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___447_16468.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___447_16468.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___447_16468.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___447_16468.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___447_16468.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___447_16468.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___447_16468.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___447_16468.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___447_16468.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___447_16468.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___447_16468.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___447_16468.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___447_16468.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___447_16468.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___447_16468.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___447_16468.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___447_16468.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___447_16468.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___447_16468.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___447_16468.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___447_16468.FStar_TypeChecker_Env.nbe)
           }  in
         let uu____16473 = tc_modul env1 m b  in
         match uu____16473 with
         | (m1,env2) ->
             ((let uu____16485 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____16485
               then
                 let uu____16488 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____16488
               else ());
              (let uu____16494 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____16494
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
                         let uu____16532 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____16532 with
                         | (univnames1,e) ->
                             let uu___448_16539 = lb  in
                             let uu____16540 =
                               let uu____16543 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____16543 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___448_16539.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___448_16539.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___448_16539.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___448_16539.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16540;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___448_16539.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___448_16539.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___449_16544 = se  in
                       let uu____16545 =
                         let uu____16546 =
                           let uu____16553 =
                             let uu____16554 = FStar_List.map update lbs  in
                             (b1, uu____16554)  in
                           (uu____16553, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____16546  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____16545;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___449_16544.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___449_16544.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___449_16544.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___449_16544.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____16562 -> se  in
                 let normalized_module =
                   let uu___450_16564 = m1  in
                   let uu____16565 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___450_16564.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____16565;
                     FStar_Syntax_Syntax.exports =
                       (uu___450_16564.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___450_16564.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____16566 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____16566
               else ());
              (m1, env2)))
  
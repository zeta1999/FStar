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
                                    let if_then_else1 =
                                      let p =
                                        let uu____4236 =
                                          let uu____4239 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4239
                                           in
                                        let uu____4240 =
                                          let uu____4241 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4241
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4236
                                          uu____4240
                                         in
                                      let expected_k =
                                        let uu____4253 =
                                          let uu____4262 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4269 =
                                            let uu____4278 =
                                              FStar_Syntax_Syntax.mk_binder p
                                               in
                                            let uu____4285 =
                                              let uu____4294 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              let uu____4301 =
                                                let uu____4310 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____4310]  in
                                              uu____4294 :: uu____4301  in
                                            uu____4278 :: uu____4285  in
                                          uu____4262 :: uu____4269  in
                                        let uu____4347 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4253
                                          uu____4347
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.if_then_else
                                        expected_k
                                       in
                                    let ite_wp =
                                      let expected_k =
                                        let uu____4362 =
                                          let uu____4371 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4378 =
                                            let uu____4387 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_a
                                               in
                                            [uu____4387]  in
                                          uu____4371 :: uu____4378  in
                                        let uu____4412 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4362
                                          uu____4412
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.ite_wp
                                        expected_k
                                       in
                                    let stronger =
                                      let uu____4416 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____4416 with
                                      | (t,uu____4422) ->
                                          let expected_k =
                                            let uu____4426 =
                                              let uu____4435 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4442 =
                                                let uu____4451 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                let uu____4458 =
                                                  let uu____4467 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_a
                                                     in
                                                  [uu____4467]  in
                                                uu____4451 :: uu____4458  in
                                              uu____4435 :: uu____4442  in
                                            let uu____4498 =
                                              FStar_Syntax_Syntax.mk_Total t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4426 uu____4498
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.stronger
                                            expected_k
                                       in
                                    let close_wp =
                                      let b =
                                        let uu____4511 =
                                          let uu____4514 =
                                            FStar_Ident.range_of_lid
                                              ed2.FStar_Syntax_Syntax.mname
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____4514
                                           in
                                        let uu____4515 =
                                          let uu____4516 =
                                            FStar_Syntax_Util.type_u ()  in
                                          FStar_All.pipe_right uu____4516
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_Syntax_Syntax.new_bv uu____4511
                                          uu____4515
                                         in
                                      let b_wp_a =
                                        let uu____4528 =
                                          let uu____4537 =
                                            let uu____4544 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                b
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____4544
                                             in
                                          [uu____4537]  in
                                        let uu____4557 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4528
                                          uu____4557
                                         in
                                      let expected_k =
                                        let uu____4563 =
                                          let uu____4572 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4579 =
                                            let uu____4588 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4595 =
                                              let uu____4604 =
                                                FStar_Syntax_Syntax.null_binder
                                                  b_wp_a
                                                 in
                                              [uu____4604]  in
                                            uu____4588 :: uu____4595  in
                                          uu____4572 :: uu____4579  in
                                        let uu____4635 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4563
                                          uu____4635
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.close_wp
                                        expected_k
                                       in
                                    let assert_p =
                                      let expected_k =
                                        let uu____4650 =
                                          let uu____4659 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4666 =
                                            let uu____4675 =
                                              let uu____4682 =
                                                let uu____4683 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____4683
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4682
                                               in
                                            let uu____4692 =
                                              let uu____4701 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____4701]  in
                                            uu____4675 :: uu____4692  in
                                          uu____4659 :: uu____4666  in
                                        let uu____4732 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4650
                                          uu____4732
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.assert_p
                                        expected_k
                                       in
                                    let assume_p =
                                      let expected_k =
                                        let uu____4747 =
                                          let uu____4756 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4763 =
                                            let uu____4772 =
                                              let uu____4779 =
                                                let uu____4780 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____4780
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____4779
                                               in
                                            let uu____4789 =
                                              let uu____4798 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_a
                                                 in
                                              [uu____4798]  in
                                            uu____4772 :: uu____4789  in
                                          uu____4756 :: uu____4763  in
                                        let uu____4829 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4747
                                          uu____4829
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.assume_p
                                        expected_k
                                       in
                                    let null_wp =
                                      let expected_k =
                                        let uu____4844 =
                                          let uu____4853 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          [uu____4853]  in
                                        let uu____4872 =
                                          FStar_Syntax_Syntax.mk_Total wp_a
                                           in
                                        FStar_Syntax_Util.arrow uu____4844
                                          uu____4872
                                         in
                                      check_and_gen' env2
                                        ed2.FStar_Syntax_Syntax.null_wp
                                        expected_k
                                       in
                                    let trivial_wp =
                                      let uu____4876 =
                                        FStar_Syntax_Util.type_u ()  in
                                      match uu____4876 with
                                      | (t,uu____4882) ->
                                          let expected_k =
                                            let uu____4886 =
                                              let uu____4895 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4902 =
                                                let uu____4911 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_a
                                                   in
                                                [uu____4911]  in
                                              uu____4895 :: uu____4902  in
                                            let uu____4936 =
                                              FStar_Syntax_Syntax.mk_GTotal t
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4886 uu____4936
                                             in
                                          check_and_gen' env2
                                            ed2.FStar_Syntax_Syntax.trivial
                                            expected_k
                                       in
                                    let uu____4939 =
                                      let uu____4952 =
                                        let uu____4957 =
                                          let uu____4958 =
                                            FStar_Syntax_Subst.compress
                                              (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                             in
                                          uu____4958.FStar_Syntax_Syntax.n
                                           in
                                        let uu____4961 =
                                          let uu____4962 =
                                            FStar_Syntax_Subst.compress
                                              (ed2.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m
                                             in
                                          uu____4962.FStar_Syntax_Syntax.n
                                           in
                                        (uu____4957, uu____4961)  in
                                      if ed2.FStar_Syntax_Syntax.spec_dm4f
                                      then
                                        let repr =
                                          let uu____4978 =
                                            FStar_Syntax_Util.type_u ()  in
                                          match uu____4978 with
                                          | (t,uu____4984) ->
                                              let expected_k =
                                                let uu____4988 =
                                                  let uu____4997 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____5004 =
                                                    let uu____5013 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_a
                                                       in
                                                    [uu____5013]  in
                                                  uu____4997 :: uu____5004
                                                   in
                                                let uu____5038 =
                                                  FStar_Syntax_Syntax.mk_GTotal
                                                    t
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____4988 uu____5038
                                                 in
                                              ((let uu____5042 =
                                                  FStar_TypeChecker_Env.debug
                                                    env2
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____5042
                                                then
                                                  let uu____5046 =
                                                    FStar_Syntax_Print.term_to_string
                                                      (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                                     in
                                                  let uu____5048 =
                                                    FStar_Syntax_Print.term_to_string
                                                      expected_k
                                                     in
                                                  FStar_Util.print2
                                                    "About to check repr=%s\nat type %s\n"
                                                    uu____5046 uu____5048
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
                                          let uu____5067 =
                                            let uu____5074 =
                                              let uu____5075 =
                                                let uu____5092 =
                                                  let uu____5103 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      t
                                                     in
                                                  let uu____5112 =
                                                    let uu____5123 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        wp
                                                       in
                                                    [uu____5123]  in
                                                  uu____5103 :: uu____5112
                                                   in
                                                (repr1, uu____5092)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____5075
                                               in
                                            FStar_Syntax_Syntax.mk uu____5074
                                             in
                                          uu____5067
                                            FStar_Pervasives_Native.None
                                            FStar_Range.dummyRange
                                           in
                                        let mk_repr a1 wp =
                                          let uu____5184 =
                                            FStar_Syntax_Syntax.bv_to_name a1
                                             in
                                          mk_repr' uu____5184 wp  in
                                        let destruct_repr t =
                                          let uu____5199 =
                                            let uu____5200 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____5200.FStar_Syntax_Syntax.n
                                             in
                                          match uu____5199 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____5211,(t1,uu____5213)::
                                               (wp,uu____5215)::[])
                                              -> (t1, wp)
                                          | uu____5274 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let bind_repr =
                                          let r =
                                            let uu____5286 =
                                              FStar_Syntax_Syntax.lid_as_fv
                                                FStar_Parser_Const.range_0
                                                FStar_Syntax_Syntax.delta_constant
                                                FStar_Pervasives_Native.None
                                               in
                                            FStar_All.pipe_right uu____5286
                                              FStar_Syntax_Syntax.fv_to_tm
                                             in
                                          let uu____5287 =
                                            fresh_effect_signature ()  in
                                          match uu____5287 with
                                          | (b,wp_b) ->
                                              let a_wp_b =
                                                let uu____5303 =
                                                  let uu____5312 =
                                                    let uu____5319 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        a
                                                       in
                                                    FStar_Syntax_Syntax.null_binder
                                                      uu____5319
                                                     in
                                                  [uu____5312]  in
                                                let uu____5332 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    wp_b
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____5303 uu____5332
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
                                                let uu____5340 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____5340
                                                 in
                                              let wp_g_x =
                                                let uu____5345 =
                                                  let uu____5350 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      wp_g
                                                     in
                                                  let uu____5351 =
                                                    let uu____5352 =
                                                      let uu____5361 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x_a
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.as_arg
                                                        uu____5361
                                                       in
                                                    [uu____5352]  in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____5350 uu____5351
                                                   in
                                                uu____5345
                                                  FStar_Pervasives_Native.None
                                                  FStar_Range.dummyRange
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____5394 =
                                                    let uu____5399 =
                                                      let uu____5400 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          bind_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____5400
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____5409 =
                                                      let uu____5410 =
                                                        let uu____5413 =
                                                          let uu____5416 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          let uu____5417 =
                                                            let uu____5420 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                b
                                                               in
                                                            let uu____5421 =
                                                              let uu____5424
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  wp_f
                                                                 in
                                                              let uu____5425
                                                                =
                                                                let uu____5428
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                   in
                                                                [uu____5428]
                                                                 in
                                                              uu____5424 ::
                                                                uu____5425
                                                               in
                                                            uu____5420 ::
                                                              uu____5421
                                                             in
                                                          uu____5416 ::
                                                            uu____5417
                                                           in
                                                        r :: uu____5413  in
                                                      FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg
                                                        uu____5410
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____5399 uu____5409
                                                     in
                                                  uu____5394
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr b wp  in
                                              let maybe_range_arg =
                                                let uu____5448 =
                                                  FStar_Util.for_some
                                                    (FStar_Syntax_Util.attr_eq
                                                       FStar_Syntax_Util.dm4f_bind_range_attr)
                                                    ed2.FStar_Syntax_Syntax.eff_attrs
                                                   in
                                                if uu____5448
                                                then
                                                  let uu____5459 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      FStar_Syntax_Syntax.t_range
                                                     in
                                                  let uu____5466 =
                                                    let uu____5475 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        FStar_Syntax_Syntax.t_range
                                                       in
                                                    [uu____5475]  in
                                                  uu____5459 :: uu____5466
                                                else []  in
                                              let expected_k =
                                                let uu____5511 =
                                                  let uu____5520 =
                                                    let uu____5529 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a
                                                       in
                                                    let uu____5536 =
                                                      let uu____5545 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          b
                                                         in
                                                      [uu____5545]  in
                                                    uu____5529 :: uu____5536
                                                     in
                                                  let uu____5570 =
                                                    let uu____5579 =
                                                      let uu____5588 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          wp_f
                                                         in
                                                      let uu____5595 =
                                                        let uu____5604 =
                                                          let uu____5611 =
                                                            let uu____5612 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                wp_f
                                                               in
                                                            mk_repr a
                                                              uu____5612
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____5611
                                                           in
                                                        let uu____5613 =
                                                          let uu____5622 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              wp_g
                                                             in
                                                          let uu____5629 =
                                                            let uu____5638 =
                                                              let uu____5645
                                                                =
                                                                let uu____5646
                                                                  =
                                                                  let uu____5655
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                  [uu____5655]
                                                                   in
                                                                let uu____5674
                                                                  =
                                                                  let uu____5677
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                  FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____5677
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  uu____5646
                                                                  uu____5674
                                                                 in
                                                              FStar_Syntax_Syntax.null_binder
                                                                uu____5645
                                                               in
                                                            [uu____5638]  in
                                                          uu____5622 ::
                                                            uu____5629
                                                           in
                                                        uu____5604 ::
                                                          uu____5613
                                                         in
                                                      uu____5588 ::
                                                        uu____5595
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____5579
                                                     in
                                                  FStar_List.append
                                                    uu____5520 uu____5570
                                                   in
                                                let uu____5722 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____5511 uu____5722
                                                 in
                                              ((let uu____5726 =
                                                  FStar_TypeChecker_Env.debug
                                                    env2
                                                    (FStar_Options.Other "ED")
                                                   in
                                                if uu____5726
                                                then
                                                  let uu____5730 =
                                                    FStar_Syntax_Print.term_to_string
                                                      expected_k
                                                     in
                                                  FStar_Util.print1
                                                    "About to check expected_k %s\n"
                                                    uu____5730
                                                else ());
                                               (let uu____5735 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env2 expected_k
                                                   in
                                                match uu____5735 with
                                                | (expected_k1,uu____5743,uu____5744)
                                                    ->
                                                    ((let uu____5746 =
                                                        FStar_TypeChecker_Env.debug
                                                          env2
                                                          (FStar_Options.Other
                                                             "ED")
                                                         in
                                                      if uu____5746
                                                      then
                                                        let uu____5750 =
                                                          FStar_Syntax_Print.term_to_string
                                                            (FStar_Pervasives_Native.snd
                                                               (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind)
                                                           in
                                                        let uu____5756 =
                                                          FStar_Syntax_Print.term_to_string
                                                            expected_k1
                                                           in
                                                        FStar_Util.print2
                                                          "About to check bind=%s\n\n, at type %s\n"
                                                          uu____5750
                                                          uu____5756
                                                      else ());
                                                     (let env3 =
                                                        FStar_TypeChecker_Env.set_range
                                                          env2
                                                          (FStar_Pervasives_Native.snd
                                                             (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind).FStar_Syntax_Syntax.pos
                                                         in
                                                      let env4 =
                                                        let uu___390_5767 =
                                                          env3  in
                                                        {
                                                          FStar_TypeChecker_Env.solver
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.solver);
                                                          FStar_TypeChecker_Env.range
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.range);
                                                          FStar_TypeChecker_Env.curmodule
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.curmodule);
                                                          FStar_TypeChecker_Env.gamma
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.gamma);
                                                          FStar_TypeChecker_Env.gamma_sig
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.gamma_sig);
                                                          FStar_TypeChecker_Env.gamma_cache
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.gamma_cache);
                                                          FStar_TypeChecker_Env.modules
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.modules);
                                                          FStar_TypeChecker_Env.expected_typ
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.expected_typ);
                                                          FStar_TypeChecker_Env.sigtab
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.sigtab);
                                                          FStar_TypeChecker_Env.attrtab
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.attrtab);
                                                          FStar_TypeChecker_Env.is_pattern
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.is_pattern);
                                                          FStar_TypeChecker_Env.instantiate_imp
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.instantiate_imp);
                                                          FStar_TypeChecker_Env.effects
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.effects);
                                                          FStar_TypeChecker_Env.generalize
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.generalize);
                                                          FStar_TypeChecker_Env.letrecs
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.letrecs);
                                                          FStar_TypeChecker_Env.top_level
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.top_level);
                                                          FStar_TypeChecker_Env.check_uvars
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.check_uvars);
                                                          FStar_TypeChecker_Env.use_eq
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.use_eq);
                                                          FStar_TypeChecker_Env.is_iface
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.is_iface);
                                                          FStar_TypeChecker_Env.admit
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.admit);
                                                          FStar_TypeChecker_Env.lax
                                                            = true;
                                                          FStar_TypeChecker_Env.lax_universes
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.lax_universes);
                                                          FStar_TypeChecker_Env.phase1
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.phase1);
                                                          FStar_TypeChecker_Env.failhard
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.failhard);
                                                          FStar_TypeChecker_Env.nosynth
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.nosynth);
                                                          FStar_TypeChecker_Env.uvar_subtyping
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.uvar_subtyping);
                                                          FStar_TypeChecker_Env.tc_term
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.tc_term);
                                                          FStar_TypeChecker_Env.type_of
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.type_of);
                                                          FStar_TypeChecker_Env.universe_of
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.universe_of);
                                                          FStar_TypeChecker_Env.check_type_of
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.check_type_of);
                                                          FStar_TypeChecker_Env.use_bv_sorts
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.use_bv_sorts);
                                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                          FStar_TypeChecker_Env.normalized_eff_names
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.normalized_eff_names);
                                                          FStar_TypeChecker_Env.fv_delta_depths
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.fv_delta_depths);
                                                          FStar_TypeChecker_Env.proof_ns
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.proof_ns);
                                                          FStar_TypeChecker_Env.synth_hook
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.synth_hook);
                                                          FStar_TypeChecker_Env.splice
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.splice);
                                                          FStar_TypeChecker_Env.postprocess
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.postprocess);
                                                          FStar_TypeChecker_Env.is_native_tactic
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.is_native_tactic);
                                                          FStar_TypeChecker_Env.identifier_info
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.identifier_info);
                                                          FStar_TypeChecker_Env.tc_hooks
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.tc_hooks);
                                                          FStar_TypeChecker_Env.dsenv
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.dsenv);
                                                          FStar_TypeChecker_Env.nbe
                                                            =
                                                            (uu___390_5767.FStar_TypeChecker_Env.nbe)
                                                        }  in
                                                      let br =
                                                        check_and_gen' env4
                                                          (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                                          expected_k1
                                                         in
                                                      (let uu____5779 =
                                                         FStar_TypeChecker_Env.debug
                                                           env4
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____5779
                                                       then
                                                         let uu____5783 =
                                                           FStar_Syntax_Print.tscheme_to_string
                                                             br
                                                            in
                                                         let uu____5785 =
                                                           FStar_Syntax_Print.term_to_string
                                                             expected_k1
                                                            in
                                                         FStar_Util.print2
                                                           "After checking bind_repr is %s\nexpected_k is %s\n"
                                                           uu____5783
                                                           uu____5785
                                                       else ());
                                                      br))))
                                           in
                                        let return_repr =
                                          let x_a =
                                            let uu____5792 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.gen_bv "x_a"
                                              FStar_Pervasives_Native.None
                                              uu____5792
                                             in
                                          let res =
                                            let wp =
                                              let uu____5800 =
                                                let uu____5805 =
                                                  let uu____5806 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      return_wp
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____5806
                                                    FStar_Pervasives_Native.snd
                                                   in
                                                let uu____5815 =
                                                  let uu____5816 =
                                                    let uu____5819 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        a
                                                       in
                                                    let uu____5820 =
                                                      let uu____5823 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          x_a
                                                         in
                                                      [uu____5823]  in
                                                    uu____5819 :: uu____5820
                                                     in
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.as_arg
                                                    uu____5816
                                                   in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  uu____5805 uu____5815
                                                 in
                                              uu____5800
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                               in
                                            mk_repr a wp  in
                                          let expected_k =
                                            let uu____5837 =
                                              let uu____5846 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____5853 =
                                                let uu____5862 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    x_a
                                                   in
                                                [uu____5862]  in
                                              uu____5846 :: uu____5853  in
                                            let uu____5887 =
                                              FStar_Syntax_Syntax.mk_Total
                                                res
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5837 uu____5887
                                             in
                                          let uu____5890 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k
                                             in
                                          match uu____5890 with
                                          | (expected_k1,uu____5898,uu____5899)
                                              ->
                                              let env3 =
                                                FStar_TypeChecker_Env.set_range
                                                  env2
                                                  (FStar_Pervasives_Native.snd
                                                     (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret).FStar_Syntax_Syntax.pos
                                                 in
                                              let uu____5905 =
                                                check_and_gen' env3
                                                  (ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                                  expected_k1
                                                 in
                                              (match uu____5905 with
                                               | (univs1,repr1) ->
                                                   (match univs1 with
                                                    | [] -> ([], repr1)
                                                    | uu____5928 ->
                                                        FStar_Errors.raise_error
                                                          (FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn,
                                                            "Unexpected universe-polymorphic return for effect")
                                                          repr1.FStar_Syntax_Syntax.pos))
                                           in
                                        let actions =
                                          let check_action act =
                                            let uu____5943 =
                                              if
                                                act.FStar_Syntax_Syntax.action_univs
                                                  = []
                                              then (env2, act)
                                              else
                                                (let uu____5957 =
                                                   FStar_Syntax_Subst.univ_var_opening
                                                     act.FStar_Syntax_Syntax.action_univs
                                                    in
                                                 match uu____5957 with
                                                 | (usubst,uvs) ->
                                                     let uu____5980 =
                                                       FStar_TypeChecker_Env.push_univ_vars
                                                         env2 uvs
                                                        in
                                                     let uu____5981 =
                                                       let uu___391_5982 =
                                                         act  in
                                                       let uu____5983 =
                                                         FStar_Syntax_Subst.subst_binders
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_params
                                                          in
                                                       let uu____5984 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____5985 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___391_5982.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___391_5982.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = uvs;
                                                         FStar_Syntax_Syntax.action_params
                                                           = uu____5983;
                                                         FStar_Syntax_Syntax.action_defn
                                                           = uu____5984;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____5985
                                                       }  in
                                                     (uu____5980, uu____5981))
                                               in
                                            match uu____5943 with
                                            | (env3,act1) ->
                                                let act_typ =
                                                  let uu____5989 =
                                                    let uu____5990 =
                                                      FStar_Syntax_Subst.compress
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                       in
                                                    uu____5990.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____5989 with
                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                      (bs,c) ->
                                                      let c1 =
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                          c
                                                         in
                                                      let uu____6016 =
                                                        FStar_Ident.lid_equals
                                                          c1.FStar_Syntax_Syntax.effect_name
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      if uu____6016
                                                      then
                                                        let uu____6019 =
                                                          let uu____6022 =
                                                            let uu____6023 =
                                                              let uu____6024
                                                                =
                                                                FStar_List.hd
                                                                  c1.FStar_Syntax_Syntax.effect_args
                                                                 in
                                                              FStar_Pervasives_Native.fst
                                                                uu____6024
                                                               in
                                                            mk_repr'
                                                              c1.FStar_Syntax_Syntax.result_typ
                                                              uu____6023
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total
                                                            uu____6022
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          bs uu____6019
                                                      else
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                  | uu____6047 ->
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                   in
                                                let uu____6048 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env3 act_typ
                                                   in
                                                (match uu____6048 with
                                                 | (act_typ1,uu____6056,g_t)
                                                     ->
                                                     let env' =
                                                       let uu___392_6059 =
                                                         FStar_TypeChecker_Env.set_expected_typ
                                                           env3 act_typ1
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.is_pattern
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.is_pattern);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           = false;
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.lax);
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___392_6059.FStar_TypeChecker_Env.nbe)
                                                       }  in
                                                     ((let uu____6062 =
                                                         FStar_TypeChecker_Env.debug
                                                           env3
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____6062
                                                       then
                                                         let uu____6066 =
                                                           FStar_Ident.text_of_lid
                                                             act1.FStar_Syntax_Syntax.action_name
                                                            in
                                                         let uu____6068 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____6070 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act_typ1
                                                            in
                                                         FStar_Util.print3
                                                           "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                           uu____6066
                                                           uu____6068
                                                           uu____6070
                                                       else ());
                                                      (let uu____6075 =
                                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                           env'
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       match uu____6075 with
                                                       | (act_defn,uu____6083,g_a)
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
                                                           let uu____6087 =
                                                             let act_typ3 =
                                                               FStar_Syntax_Subst.compress
                                                                 act_typ2
                                                                in
                                                             match act_typ3.FStar_Syntax_Syntax.n
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs,c) ->
                                                                 let uu____6123
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs c
                                                                    in
                                                                 (match uu____6123
                                                                  with
                                                                  | (bs1,uu____6135)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6142
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____6142
                                                                     in
                                                                    let uu____6145
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env3 k
                                                                     in
                                                                    (match uu____6145
                                                                    with
                                                                    | 
                                                                    (k1,uu____6159,g)
                                                                    ->
                                                                    (k1, g)))
                                                             | uu____6163 ->
                                                                 let uu____6164
                                                                   =
                                                                   let uu____6170
                                                                    =
                                                                    let uu____6172
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____6174
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____6172
                                                                    uu____6174
                                                                     in
                                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____6170)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____6164
                                                                   act_defn1.FStar_Syntax_Syntax.pos
                                                              in
                                                           (match uu____6087
                                                            with
                                                            | (expected_k,g_k)
                                                                ->
                                                                let g =
                                                                  FStar_TypeChecker_Rel.teq
                                                                    env3
                                                                    act_typ2
                                                                    expected_k
                                                                   in
                                                                ((let uu____6192
                                                                    =
                                                                    let uu____6193
                                                                    =
                                                                    let uu____6194
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____6194
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____6193
                                                                     in
                                                                  FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env3
                                                                    uu____6192);
                                                                 (let act_typ3
                                                                    =
                                                                    let uu____6196
                                                                    =
                                                                    let uu____6197
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____6197.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____6196
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs,c) ->
                                                                    let uu____6222
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs c  in
                                                                    (match uu____6222
                                                                    with
                                                                    | 
                                                                    (bs1,c1)
                                                                    ->
                                                                    let uu____6229
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____6229
                                                                    with
                                                                    | 
                                                                    (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____6249
                                                                    =
                                                                    let uu____6250
                                                                    =
                                                                    env3.FStar_TypeChecker_Env.universe_of
                                                                    env3 a1
                                                                     in
                                                                    [uu____6250]
                                                                     in
                                                                    let uu____6251
                                                                    =
                                                                    let uu____6262
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____6262]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6249;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a1;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6251;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____6287
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____6287))
                                                                    | 
                                                                    uu____6290
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                  let uu____6292
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env3
                                                                    act_defn1
                                                                    else
                                                                    (let uu____6314
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____6314))
                                                                     in
                                                                  match uu____6292
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
                                                                    let uu___393_6333
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___393_6333.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___393_6333.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___393_6333.FStar_Syntax_Syntax.action_params);
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
                                        (match uu____4952 with
                                         | (uu____6342,uu____6343) ->
                                             (((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m),
                                               ((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind),
                                               ((ed2.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret),
                                               (ed2.FStar_Syntax_Syntax.actions)))
                                       in
                                    match uu____4939 with
                                    | (repr,bind_repr,return_repr,actions) ->
                                        let t0 =
                                          let uu____6363 =
                                            FStar_Syntax_Syntax.mk_Total
                                              signature1
                                             in
                                          FStar_Syntax_Util.arrow
                                            ed2.FStar_Syntax_Syntax.binders
                                            uu____6363
                                           in
                                        let uu____6366 =
                                          let uu____6371 =
                                            FStar_TypeChecker_Util.generalize_universes
                                              env0 t0
                                             in
                                          match uu____6371 with
                                          | (gen_univs,t) ->
                                              (match annotated_univ_names
                                               with
                                               | [] -> (gen_univs, t)
                                               | uu____6390 ->
                                                   let uu____6393 =
                                                     ((FStar_List.length
                                                         gen_univs)
                                                        =
                                                        (FStar_List.length
                                                           annotated_univ_names))
                                                       &&
                                                       (FStar_List.forall2
                                                          (fun u1  ->
                                                             fun u2  ->
                                                               let uu____6400
                                                                 =
                                                                 FStar_Syntax_Syntax.order_univ_name
                                                                   u1 u2
                                                                  in
                                                               uu____6400 =
                                                                 (Prims.parse_int "0"))
                                                          gen_univs
                                                          annotated_univ_names)
                                                      in
                                                   if uu____6393
                                                   then (gen_univs, t)
                                                   else
                                                     (let uu____6411 =
                                                        let uu____6417 =
                                                          let uu____6419 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 annotated_univ_names)
                                                             in
                                                          let uu____6421 =
                                                            FStar_Util.string_of_int
                                                              (FStar_List.length
                                                                 gen_univs)
                                                             in
                                                          FStar_Util.format2
                                                            "Expected an effect definition with %s universes; but found %s"
                                                            uu____6419
                                                            uu____6421
                                                           in
                                                        (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                          uu____6417)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____6411
                                                        signature1.FStar_Syntax_Syntax.pos))
                                           in
                                        (match uu____6366 with
                                         | (univs1,t) ->
                                             let signature2 =
                                               let uu____6432 =
                                                 let uu____6445 =
                                                   let uu____6446 =
                                                     FStar_Syntax_Subst.compress
                                                       t
                                                      in
                                                   uu____6446.FStar_Syntax_Syntax.n
                                                    in
                                                 (effect_params, uu____6445)
                                                  in
                                               match uu____6432 with
                                               | ([],uu____6457) -> t
                                               | (uu____6472,FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____6473,c)) ->
                                                   FStar_Syntax_Util.comp_result
                                                     c
                                               | uu____6511 ->
                                                   failwith
                                                     "Impossible : t is an arrow"
                                                in
                                             let close1 n1 ts =
                                               let ts1 =
                                                 let uu____6539 =
                                                   FStar_Syntax_Subst.close_tscheme
                                                     effect_params ts
                                                    in
                                                 FStar_Syntax_Subst.close_univ_vars_tscheme
                                                   univs1 uu____6539
                                                  in
                                               let m =
                                                 FStar_List.length
                                                   (FStar_Pervasives_Native.fst
                                                      ts1)
                                                  in
                                               (let uu____6546 =
                                                  ((n1 >=
                                                      (Prims.parse_int "0"))
                                                     &&
                                                     (let uu____6550 =
                                                        FStar_Syntax_Util.is_unknown
                                                          (FStar_Pervasives_Native.snd
                                                             ts1)
                                                         in
                                                      Prims.op_Negation
                                                        uu____6550))
                                                    && (m <> n1)
                                                   in
                                                if uu____6546
                                                then
                                                  let err_msg uu____6568 =
                                                    let error =
                                                      if m < n1
                                                      then
                                                        "not universe-polymorphic enough"
                                                      else
                                                        "too universe-polymorphic"
                                                       in
                                                    let uu____6583 =
                                                      FStar_Util.string_of_int
                                                        m
                                                       in
                                                    let uu____6591 =
                                                      FStar_Util.string_of_int
                                                        n1
                                                       in
                                                    let uu____6593 =
                                                      FStar_Syntax_Print.tscheme_to_string
                                                        ts1
                                                       in
                                                    FStar_Util.format4
                                                      "The effect combinator is %s (m,n=%s,%s) (%s)"
                                                      error uu____6583
                                                      uu____6591 uu____6593
                                                     in
                                                  let uu____6596 =
                                                    let uu____6602 =
                                                      err_msg ()  in
                                                    (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                      uu____6602)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____6596
                                                    (FStar_Pervasives_Native.snd
                                                       ts1).FStar_Syntax_Syntax.pos
                                                else ());
                                               ts1  in
                                             let close_action act =
                                               let uu____6617 =
                                                 close1
                                                   (~- (Prims.parse_int "1"))
                                                   ((act.FStar_Syntax_Syntax.action_univs),
                                                     (act.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               match uu____6617 with
                                               | (univs2,defn) ->
                                                   let uu____6633 =
                                                     close1
                                                       (~-
                                                          (Prims.parse_int "1"))
                                                       ((act.FStar_Syntax_Syntax.action_univs),
                                                         (act.FStar_Syntax_Syntax.action_typ))
                                                      in
                                                   (match uu____6633 with
                                                    | (univs',typ) ->
                                                        let uu___394_6650 =
                                                          act  in
                                                        {
                                                          FStar_Syntax_Syntax.action_name
                                                            =
                                                            (uu___394_6650.FStar_Syntax_Syntax.action_name);
                                                          FStar_Syntax_Syntax.action_unqualified_name
                                                            =
                                                            (uu___394_6650.FStar_Syntax_Syntax.action_unqualified_name);
                                                          FStar_Syntax_Syntax.action_univs
                                                            = univs2;
                                                          FStar_Syntax_Syntax.action_params
                                                            =
                                                            (uu___394_6650.FStar_Syntax_Syntax.action_params);
                                                          FStar_Syntax_Syntax.action_defn
                                                            = defn;
                                                          FStar_Syntax_Syntax.action_typ
                                                            = typ
                                                        })
                                                in
                                             let ed3 =
                                               let uu___395_6653 = ed2  in
                                               let uu____6654 =
                                                 let uu____6655 =
                                                   close1
                                                     (Prims.parse_int "0")
                                                     return_wp
                                                    in
                                                 let uu____6657 =
                                                   close1
                                                     (Prims.parse_int "1")
                                                     bind_wp
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     =
                                                     FStar_Syntax_Syntax.tun;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____6655;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____6657
                                                 }  in
                                               let uu____6659 =
                                                 close1 (Prims.parse_int "0")
                                                   if_then_else1
                                                  in
                                               let uu____6661 =
                                                 close1 (Prims.parse_int "0")
                                                   ite_wp
                                                  in
                                               let uu____6663 =
                                                 close1 (Prims.parse_int "0")
                                                   stronger
                                                  in
                                               let uu____6665 =
                                                 close1 (Prims.parse_int "1")
                                                   close_wp
                                                  in
                                               let uu____6667 =
                                                 close1 (Prims.parse_int "0")
                                                   assert_p
                                                  in
                                               let uu____6669 =
                                                 close1 (Prims.parse_int "0")
                                                   assume_p
                                                  in
                                               let uu____6671 =
                                                 close1 (Prims.parse_int "0")
                                                   null_wp
                                                  in
                                               let uu____6673 =
                                                 close1 (Prims.parse_int "0")
                                                   trivial_wp
                                                  in
                                               let uu____6675 =
                                                 let uu____6676 =
                                                   let uu____6677 =
                                                     close1
                                                       (Prims.parse_int "0")
                                                       ([], repr)
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____6677
                                                    in
                                                 let uu____6695 =
                                                   close1
                                                     (Prims.parse_int "0")
                                                     return_repr
                                                    in
                                                 let uu____6697 =
                                                   close1
                                                     (Prims.parse_int "1")
                                                     bind_repr
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.monad_m
                                                     = uu____6676;
                                                   FStar_Syntax_Syntax.monad_ret
                                                     = uu____6695;
                                                   FStar_Syntax_Syntax.monad_bind
                                                     = uu____6697
                                                 }  in
                                               let uu____6699 =
                                                 FStar_List.map close_action
                                                   actions
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.cattributes
                                                   =
                                                   (uu___395_6653.FStar_Syntax_Syntax.cattributes);
                                                 FStar_Syntax_Syntax.mname =
                                                   (uu___395_6653.FStar_Syntax_Syntax.mname);
                                                 FStar_Syntax_Syntax.univs =
                                                   univs1;
                                                 FStar_Syntax_Syntax.binders
                                                   = effect_params;
                                                 FStar_Syntax_Syntax.spec =
                                                   uu____6654;
                                                 FStar_Syntax_Syntax.signature
                                                   = signature2;
                                                 FStar_Syntax_Syntax.if_then_else
                                                   = uu____6659;
                                                 FStar_Syntax_Syntax.ite_wp =
                                                   uu____6661;
                                                 FStar_Syntax_Syntax.stronger
                                                   = uu____6663;
                                                 FStar_Syntax_Syntax.close_wp
                                                   = uu____6665;
                                                 FStar_Syntax_Syntax.assert_p
                                                   = uu____6667;
                                                 FStar_Syntax_Syntax.assume_p
                                                   = uu____6669;
                                                 FStar_Syntax_Syntax.null_wp
                                                   = uu____6671;
                                                 FStar_Syntax_Syntax.trivial
                                                   = uu____6673;
                                                 FStar_Syntax_Syntax.repr =
                                                   uu____6675;
                                                 FStar_Syntax_Syntax.elaborated
                                                   =
                                                   (uu___395_6653.FStar_Syntax_Syntax.elaborated);
                                                 FStar_Syntax_Syntax.spec_dm4f
                                                   =
                                                   (uu___395_6653.FStar_Syntax_Syntax.spec_dm4f);
                                                 FStar_Syntax_Syntax.actions
                                                   = uu____6699;
                                                 FStar_Syntax_Syntax.eff_attrs
                                                   =
                                                   (uu___395_6653.FStar_Syntax_Syntax.eff_attrs)
                                               }  in
                                             ed3)))))))))
  
let tc_lex_t :
  'Auu____6713 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____6713 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let err_range =
            let uu____6748 = FStar_List.hd ses  in
            uu____6748.FStar_Syntax_Syntax.sigrng  in
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
           | uu____6753 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t1,uu____6759,[],t,uu____6761,uu____6762);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____6764;
               FStar_Syntax_Syntax.sigattrs = uu____6765;_}::{
                                                               FStar_Syntax_Syntax.sigel
                                                                 =
                                                                 FStar_Syntax_Syntax.Sig_datacon
                                                                 (lex_top1,uu____6767,_t_top,_lex_t_top,_0_1,uu____6770);
                                                               FStar_Syntax_Syntax.sigrng
                                                                 = r1;
                                                               FStar_Syntax_Syntax.sigquals
                                                                 = [];
                                                               FStar_Syntax_Syntax.sigmeta
                                                                 = uu____6772;
                                                               FStar_Syntax_Syntax.sigattrs
                                                                 = uu____6773;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons,uu____6775,_t_cons,_lex_t_cons,_0_2,uu____6778);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____6780;
                 FStar_Syntax_Syntax.sigattrs = uu____6781;_}::[]
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
                 let uu____6832 =
                   let uu____6839 =
                     let uu____6840 =
                       let uu____6847 =
                         let uu____6850 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r1
                            in
                         FStar_Syntax_Syntax.fvar uu____6850
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       (uu____6847, [FStar_Syntax_Syntax.U_name utop])  in
                     FStar_Syntax_Syntax.Tm_uinst uu____6840  in
                   FStar_Syntax_Syntax.mk uu____6839  in
                 uu____6832 FStar_Pervasives_Native.None r1  in
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
                   let uu____6868 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1))
                       FStar_Pervasives_Native.None r2
                      in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6868
                    in
                 let hd1 =
                   let uu____6870 = FStar_Syntax_Syntax.bv_to_name a  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6870
                    in
                 let tl1 =
                   let uu____6872 =
                     let uu____6873 =
                       let uu____6880 =
                         let uu____6881 =
                           let uu____6888 =
                             let uu____6891 =
                               FStar_Ident.set_lid_range
                                 FStar_Parser_Const.lex_t_lid r2
                                in
                             FStar_Syntax_Syntax.fvar uu____6891
                               FStar_Syntax_Syntax.delta_constant
                               FStar_Pervasives_Native.None
                              in
                           (uu____6888, [FStar_Syntax_Syntax.U_name ucons2])
                            in
                         FStar_Syntax_Syntax.Tm_uinst uu____6881  in
                       FStar_Syntax_Syntax.mk uu____6880  in
                     uu____6873 FStar_Pervasives_Native.None r2  in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____6872
                    in
                 let res =
                   let uu____6900 =
                     let uu____6907 =
                       let uu____6908 =
                         let uu____6915 =
                           let uu____6918 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2
                              in
                           FStar_Syntax_Syntax.fvar uu____6918
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____6915,
                           [FStar_Syntax_Syntax.U_max
                              [FStar_Syntax_Syntax.U_name ucons1;
                              FStar_Syntax_Syntax.U_name ucons2]])
                          in
                       FStar_Syntax_Syntax.Tm_uinst uu____6908  in
                     FStar_Syntax_Syntax.mk uu____6907  in
                   uu____6900 FStar_Pervasives_Native.None r2  in
                 let uu____6924 = FStar_Syntax_Syntax.mk_Total res  in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd1, FStar_Pervasives_Native.None);
                   (tl1, FStar_Pervasives_Native.None)] uu____6924
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
               let uu____6963 = FStar_TypeChecker_Env.get_range env  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____6963;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = []
               }
           | uu____6968 ->
               let err_msg =
                 let uu____6973 =
                   let uu____6975 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids))
                      in
                   FStar_Syntax_Print.sigelt_to_string uu____6975  in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____6973
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
    fun uu____7000  ->
      fun expected_typ1  ->
        fun r  ->
          match uu____7000 with
          | (uvs,t) ->
              let uu____7013 = FStar_Syntax_Subst.open_univ_vars uvs t  in
              (match uu____7013 with
               | (uvs1,t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                      in
                   let t2 = tc_check_trivial_guard env1 t1 expected_typ1  in
                   if uvs1 = []
                   then
                     let uu____7025 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2
                        in
                     (match uu____7025 with
                      | (uvs2,t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____7043 =
                        let uu____7046 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1)
                           in
                        FStar_All.pipe_right uu____7046
                          (FStar_Syntax_Subst.close_univ_vars uvs1)
                         in
                      (uvs1, uu____7043)))
  
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7069 =
          let uu____7070 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7070 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7069 r
  
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun ts  ->
      fun r  ->
        let uu____7095 =
          let uu____7096 = FStar_Syntax_Util.type_u ()  in
          FStar_All.pipe_right uu____7096 FStar_Pervasives_Native.fst  in
        tc_type_common env ts uu____7095 r
  
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
          (let uu____7145 = FStar_TypeChecker_Env.debug env FStar_Options.Low
              in
           if uu____7145
           then
             let uu____7148 =
               FStar_Common.string_of_list
                 FStar_Syntax_Print.sigelt_to_string ses
                in
             FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____7148
           else ());
          (let uu____7153 =
             FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
               ses quals lids
              in
           match uu____7153 with
           | (sig_bndle,tcs,datas) ->
               let data_ops_ses =
                 let uu____7184 =
                   FStar_List.map
                     (FStar_TypeChecker_TcInductive.mk_data_operations quals
                        env tcs) datas
                    in
                 FStar_All.pipe_right uu____7184 FStar_List.flatten  in
               ((let uu____7198 =
                   (FStar_Options.no_positivity ()) ||
                     (let uu____7201 =
                        FStar_TypeChecker_Env.should_verify env  in
                      Prims.op_Negation uu____7201)
                    in
                 if uu____7198
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
                           let uu____7217 =
                             match ty.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                 (lid,uu____7227,uu____7228,uu____7229,uu____7230,uu____7231)
                                 -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                             | uu____7240 -> failwith "Impossible!"  in
                           match uu____7217 with
                           | (lid,r) ->
                               FStar_Errors.log_issue r
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.strcat "Inductive type "
                                      (Prims.strcat lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                         else ()) tcs;
                    FStar_List.iter
                      (fun d  ->
                         let uu____7259 =
                           match d.FStar_Syntax_Syntax.sigel with
                           | FStar_Syntax_Syntax.Sig_datacon
                               (data_lid,uu____7269,uu____7270,ty_lid,uu____7272,uu____7273)
                               -> (data_lid, ty_lid)
                           | uu____7280 -> failwith "Impossible"  in
                         match uu____7259 with
                         | (data_lid,ty_lid) ->
                             let uu____7288 =
                               (FStar_Ident.lid_equals ty_lid
                                  FStar_Parser_Const.exn_lid)
                                 &&
                                 (let uu____7291 =
                                    FStar_TypeChecker_TcInductive.check_exn_positivity
                                      data_lid env1
                                     in
                                  Prims.op_Negation uu____7291)
                                in
                             if uu____7288
                             then
                               FStar_Errors.log_issue
                                 d.FStar_Syntax_Syntax.sigrng
                                 (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                   (Prims.strcat "Exception "
                                      (Prims.strcat data_lid.FStar_Ident.str
                                         " does not satisfy the positivity condition")))
                             else ()) datas));
                (let skip_prims_type uu____7305 =
                   let lid =
                     let ty = FStar_List.hd tcs  in
                     match ty.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (lid,uu____7310,uu____7311,uu____7312,uu____7313,uu____7314)
                         -> lid
                     | uu____7323 -> failwith "Impossible"  in
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
                   let uu____7341 =
                     (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                        ((FStar_Ident.lid_equals
                            env.FStar_TypeChecker_Env.curmodule
                            FStar_Parser_Const.prims_lid)
                           && (skip_prims_type ())))
                       || is_noeq
                      in
                   if uu____7341
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
          let pop1 uu____7416 =
            let uu____7417 = FStar_TypeChecker_Env.pop env1 "tc_inductive"
               in
            ()  in
          try
            (fun uu___397_7427  ->
               match () with
               | () ->
                   let uu____7434 = tc_inductive' env1 ses quals lids  in
                   FStar_All.pipe_right uu____7434 (fun r  -> pop1 (); r)) ()
          with | uu___396_7465 -> (pop1 (); FStar_Exn.raise uu___396_7465)
  
let (z3_reset_options :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun en  ->
    let env =
      let uu____7486 = FStar_Options.using_facts_from ()  in
      FStar_TypeChecker_Env.set_proof_ns uu____7486 en  in
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
      | uu____7790 -> FStar_Pervasives_Native.None  in
    FStar_List.fold_right
      (fun at  ->
         fun acc  ->
           let uu____7848 = FStar_ToSyntax_ToSyntax.get_fail_attr true at  in
           comb uu____7848 acc) se.FStar_Syntax_Syntax.sigattrs
      FStar_Pervasives_Native.None
  
let list_of_option :
  'Auu____7873 .
    'Auu____7873 FStar_Pervasives_Native.option -> 'Auu____7873 Prims.list
  =
  fun uu___374_7882  ->
    match uu___374_7882 with
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
            let uu____7962 = collect1 tl1  in
            (match uu____7962 with
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
        | ((e,n1)::uu____8200,[]) ->
            FStar_Pervasives_Native.Some (e, n1, (Prims.parse_int "0"))
        | ([],(e,n1)::uu____8256) ->
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
          let uu____8484 =
            let uu____8486 = FStar_Options.ide ()  in
            Prims.op_Negation uu____8486  in
          if uu____8484
          then
            let uu____8489 =
              let uu____8494 = FStar_TypeChecker_Env.dsenv env  in
              let uu____8495 = FStar_TypeChecker_Env.current_module env  in
              FStar_Syntax_DsEnv.iface_decls uu____8494 uu____8495  in
            (match uu____8489 with
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
                              let uu____8528 =
                                FStar_Syntax_Syntax.range_of_fv lbname  in
                              let uu____8529 =
                                let uu____8535 =
                                  let uu____8537 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  let uu____8539 =
                                    FStar_Syntax_Print.fv_to_string lbname
                                     in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____8537 uu____8539
                                   in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____8535)
                                 in
                              FStar_Errors.log_issue uu____8528 uu____8529
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____8546 =
                                   FStar_Syntax_Syntax.range_of_fv lbname  in
                                 let uu____8547 =
                                   let uu____8553 =
                                     let uu____8555 =
                                       FStar_Syntax_Print.fv_to_string lbname
                                        in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____8555
                                      in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____8553)
                                    in
                                 FStar_Errors.log_issue uu____8546 uu____8547)
                              else ())
                         else ())))
          else ()
      | uu____8565 -> ()
  
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
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____8610 ->
           failwith "Impossible bare data-constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____8638 ->
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
             let uu____8698 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____8698
             then
               let ses1 =
                 let uu____8706 =
                   let uu____8707 =
                     let uu____8708 =
                       tc_inductive
                         (let uu___398_8717 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___398_8717.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___398_8717.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___398_8717.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___398_8717.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___398_8717.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___398_8717.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___398_8717.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___398_8717.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___398_8717.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___398_8717.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___398_8717.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___398_8717.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___398_8717.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___398_8717.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___398_8717.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___398_8717.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___398_8717.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___398_8717.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___398_8717.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___398_8717.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___398_8717.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___398_8717.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___398_8717.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___398_8717.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___398_8717.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___398_8717.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___398_8717.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___398_8717.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___398_8717.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___398_8717.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___398_8717.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___398_8717.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___398_8717.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___398_8717.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___398_8717.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___398_8717.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___398_8717.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___398_8717.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___398_8717.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___398_8717.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___398_8717.FStar_TypeChecker_Env.nbe)
                          }) ses se.FStar_Syntax_Syntax.sigquals lids
                        in
                     FStar_All.pipe_right uu____8708
                       FStar_Pervasives_Native.fst
                      in
                   FStar_All.pipe_right uu____8707
                     (FStar_TypeChecker_Normalize.elim_uvars env1)
                    in
                 FStar_All.pipe_right uu____8706
                   FStar_Syntax_Util.ses_of_sigbundle
                  in
               ((let uu____8731 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "TwoPhases")
                    in
                 if uu____8731
                 then
                   let uu____8736 =
                     FStar_Syntax_Print.sigelt_to_string
                       (let uu___399_8740 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___399_8740.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___399_8740.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___399_8740.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___399_8740.FStar_Syntax_Syntax.sigattrs)
                        })
                      in
                   FStar_Util.print1 "Inductive after phase 1: %s\n"
                     uu____8736
                 else ());
                ses1)
             else ses  in
           let uu____8750 =
             tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids  in
           (match uu____8750 with
            | (sigbndle,projectors_ses) ->
                let sigbndle1 =
                  let uu___400_8774 = sigbndle  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___400_8774.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___400_8774.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___400_8774.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___400_8774.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (se.FStar_Syntax_Syntax.sigattrs)
                  }  in
                ([sigbndle1], projectors_ses, env0))
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p r; ([se], [], env0))
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let forfree =
             let uu____8788 =
               let uu____8789 =
                 FStar_Syntax_Subst.compress
                   (ne.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                  in
               uu____8789.FStar_Syntax_Syntax.n  in
             match uu____8788 with
             | FStar_Syntax_Syntax.Tm_unknown  -> false
             | uu____8794 ->
                 Prims.op_Negation ne.FStar_Syntax_Syntax.elaborated
              in
           if forfree
           then
             ((let uu____8807 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____8807
               then FStar_Util.print_string "Beginning DM4F run\n"
               else ());
              (let uu____8814 = cps_and_elaborate_ed env0 ne  in
               match uu____8814 with
               | (ses,ne1,lift_from_pure_opt) ->
                   let ne2 =
                     let uu___401_8847 = ne1  in
                     {
                       FStar_Syntax_Syntax.cattributes =
                         (uu___401_8847.FStar_Syntax_Syntax.cattributes);
                       FStar_Syntax_Syntax.mname =
                         (uu___401_8847.FStar_Syntax_Syntax.mname);
                       FStar_Syntax_Syntax.univs =
                         (uu___401_8847.FStar_Syntax_Syntax.univs);
                       FStar_Syntax_Syntax.binders =
                         (uu___401_8847.FStar_Syntax_Syntax.binders);
                       FStar_Syntax_Syntax.spec =
                         (uu___401_8847.FStar_Syntax_Syntax.spec);
                       FStar_Syntax_Syntax.signature =
                         (uu___401_8847.FStar_Syntax_Syntax.signature);
                       FStar_Syntax_Syntax.if_then_else =
                         (uu___401_8847.FStar_Syntax_Syntax.if_then_else);
                       FStar_Syntax_Syntax.ite_wp =
                         (uu___401_8847.FStar_Syntax_Syntax.ite_wp);
                       FStar_Syntax_Syntax.stronger =
                         (uu___401_8847.FStar_Syntax_Syntax.stronger);
                       FStar_Syntax_Syntax.close_wp =
                         (uu___401_8847.FStar_Syntax_Syntax.close_wp);
                       FStar_Syntax_Syntax.assert_p =
                         (uu___401_8847.FStar_Syntax_Syntax.assert_p);
                       FStar_Syntax_Syntax.assume_p =
                         (uu___401_8847.FStar_Syntax_Syntax.assume_p);
                       FStar_Syntax_Syntax.null_wp =
                         (uu___401_8847.FStar_Syntax_Syntax.null_wp);
                       FStar_Syntax_Syntax.trivial =
                         (uu___401_8847.FStar_Syntax_Syntax.trivial);
                       FStar_Syntax_Syntax.repr =
                         (uu___401_8847.FStar_Syntax_Syntax.repr);
                       FStar_Syntax_Syntax.elaborated = true;
                       FStar_Syntax_Syntax.spec_dm4f =
                         (uu___401_8847.FStar_Syntax_Syntax.spec_dm4f);
                       FStar_Syntax_Syntax.actions =
                         (uu___401_8847.FStar_Syntax_Syntax.actions);
                       FStar_Syntax_Syntax.eff_attrs =
                         (uu___401_8847.FStar_Syntax_Syntax.eff_attrs)
                     }  in
                   let effect_and_lift_ses =
                     match lift_from_pure_opt with
                     | FStar_Pervasives_Native.Some lift ->
                         [(let uu___402_8856 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne2);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___402_8856.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___402_8856.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___402_8856.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___402_8856.FStar_Syntax_Syntax.sigattrs)
                           });
                         lift]
                     | FStar_Pervasives_Native.None  ->
                         [(let uu___403_8858 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne2);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___403_8858.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___403_8858.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___403_8858.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___403_8858.FStar_Syntax_Syntax.sigattrs)
                           })]
                      in
                   ([], (FStar_List.append ses effect_and_lift_ses), env0)))
           else
             (let ne1 =
                let uu____8866 =
                  (FStar_Options.use_two_phase_tc ()) &&
                    (FStar_TypeChecker_Env.should_verify env)
                   in
                if uu____8866
                then
                  let ne1 =
                    let uu____8870 =
                      let uu____8871 =
                        let uu____8872 =
                          tc_eff_decl
                            (let uu___404_8874 = env  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___404_8874.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___404_8874.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___404_8874.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___404_8874.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___404_8874.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___404_8874.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___404_8874.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___404_8874.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___404_8874.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___404_8874.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___404_8874.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___404_8874.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___404_8874.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___404_8874.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___404_8874.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___404_8874.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___404_8874.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___404_8874.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___404_8874.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___404_8874.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___404_8874.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 = true;
                               FStar_TypeChecker_Env.failhard =
                                 (uu___404_8874.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___404_8874.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___404_8874.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___404_8874.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___404_8874.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___404_8874.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___404_8874.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___404_8874.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___404_8874.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___404_8874.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___404_8874.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___404_8874.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___404_8874.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___404_8874.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___404_8874.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___404_8874.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___404_8874.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___404_8874.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___404_8874.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___404_8874.FStar_TypeChecker_Env.nbe)
                             }) se ne
                           in
                        FStar_All.pipe_right uu____8872
                          (fun ne1  ->
                             let uu___405_8880 = se  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___405_8880.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___405_8880.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___405_8880.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___405_8880.FStar_Syntax_Syntax.sigattrs)
                             })
                         in
                      FStar_All.pipe_right uu____8871
                        (FStar_TypeChecker_Normalize.elim_uvars env)
                       in
                    FStar_All.pipe_right uu____8870
                      FStar_Syntax_Util.eff_decl_of_new_effect
                     in
                  ((let uu____8882 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "TwoPhases")
                       in
                    if uu____8882
                    then
                      let uu____8887 =
                        FStar_Syntax_Print.sigelt_to_string
                          (let uu___406_8891 = se  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_new_effect ne1);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___406_8891.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___406_8891.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___406_8891.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___406_8891.FStar_Syntax_Syntax.sigattrs)
                           })
                         in
                      FStar_Util.print1 "Effect decl after phase 1: %s\n"
                        uu____8887
                    else ());
                   ne1)
                else ne  in
              let ne2 = tc_eff_decl env se ne1  in
              let se1 =
                let uu___407_8899 = se  in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_new_effect ne2);
                  FStar_Syntax_Syntax.sigrng =
                    (uu___407_8899.FStar_Syntax_Syntax.sigrng);
                  FStar_Syntax_Syntax.sigquals =
                    (uu___407_8899.FStar_Syntax_Syntax.sigquals);
                  FStar_Syntax_Syntax.sigmeta =
                    (uu___407_8899.FStar_Syntax_Syntax.sigmeta);
                  FStar_Syntax_Syntax.sigattrs =
                    (uu___407_8899.FStar_Syntax_Syntax.sigattrs)
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
           let uu____8907 =
             let uu____8914 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____8914
              in
           (match uu____8907 with
            | (a,wp_a_src) ->
                let uu____8931 =
                  let uu____8938 =
                    FStar_TypeChecker_Env.lookup_effect_lid env
                      sub1.FStar_Syntax_Syntax.target
                     in
                  monad_signature env sub1.FStar_Syntax_Syntax.target
                    uu____8938
                   in
                (match uu____8931 with
                 | (b,wp_b_tgt) ->
                     let wp_a_tgt =
                       let uu____8956 =
                         let uu____8959 =
                           let uu____8960 =
                             let uu____8967 =
                               FStar_Syntax_Syntax.bv_to_name a  in
                             (b, uu____8967)  in
                           FStar_Syntax_Syntax.NT uu____8960  in
                         [uu____8959]  in
                       FStar_Syntax_Subst.subst uu____8956 wp_b_tgt  in
                     let expected_k =
                       let uu____8975 =
                         let uu____8984 = FStar_Syntax_Syntax.mk_binder a  in
                         let uu____8991 =
                           let uu____9000 =
                             FStar_Syntax_Syntax.null_binder wp_a_src  in
                           [uu____9000]  in
                         uu____8984 :: uu____8991  in
                       let uu____9025 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                          in
                       FStar_Syntax_Util.arrow uu____8975 uu____9025  in
                     let repr_type eff_name a1 wp =
                       (let uu____9047 =
                          let uu____9049 =
                            FStar_TypeChecker_Env.is_reifiable_effect env
                              eff_name
                             in
                          Prims.op_Negation uu____9049  in
                        if uu____9047
                        then
                          let uu____9052 =
                            let uu____9058 =
                              FStar_Util.format1
                                "Effect %s cannot be reified"
                                eff_name.FStar_Ident.str
                               in
                            (FStar_Errors.Fatal_EffectCannotBeReified,
                              uu____9058)
                             in
                          let uu____9062 =
                            FStar_TypeChecker_Env.get_range env  in
                          FStar_Errors.raise_error uu____9052 uu____9062
                        else ());
                       (let uu____9065 =
                          FStar_TypeChecker_Env.effect_decl_opt env eff_name
                           in
                        match uu____9065 with
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
                            let uu____9102 =
                              FStar_TypeChecker_Env.get_range env  in
                            let uu____9103 =
                              let uu____9110 =
                                let uu____9111 =
                                  let uu____9128 =
                                    let uu____9139 =
                                      FStar_Syntax_Syntax.as_arg a1  in
                                    let uu____9148 =
                                      let uu____9159 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____9159]  in
                                    uu____9139 :: uu____9148  in
                                  (repr, uu____9128)  in
                                FStar_Syntax_Syntax.Tm_app uu____9111  in
                              FStar_Syntax_Syntax.mk uu____9110  in
                            uu____9103 FStar_Pervasives_Native.None
                              uu____9102)
                        in
                     let uu____9207 =
                       match ((sub1.FStar_Syntax_Syntax.lift),
                               (sub1.FStar_Syntax_Syntax.lift_wp))
                       with
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.None ) ->
                           failwith "Impossible (parser)"
                       | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                           let uu____9380 =
                             if
                               (FStar_List.length uvs) >
                                 (Prims.parse_int "0")
                             then
                               let uu____9391 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               match uu____9391 with
                               | (usubst,uvs1) ->
                                   let uu____9414 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs1
                                      in
                                   let uu____9415 =
                                     FStar_Syntax_Subst.subst usubst lift_wp
                                      in
                                   (uu____9414, uu____9415)
                             else (env, lift_wp)  in
                           (match uu____9380 with
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
                                     let uu____9465 =
                                       FStar_Syntax_Subst.close_univ_vars uvs
                                         lift_wp2
                                        in
                                     (uvs, uu____9465))
                                   in
                                (lift, lift_wp2))
                       | (FStar_Pervasives_Native.Some
                          (what,lift),FStar_Pervasives_Native.None ) ->
                           let uu____9536 =
                             if
                               (FStar_List.length what) >
                                 (Prims.parse_int "0")
                             then
                               let uu____9551 =
                                 FStar_Syntax_Subst.univ_var_opening what  in
                               match uu____9551 with
                               | (usubst,uvs) ->
                                   let uu____9576 =
                                     FStar_Syntax_Subst.subst usubst lift  in
                                   (uvs, uu____9576)
                             else ([], lift)  in
                           (match uu____9536 with
                            | (uvs,lift1) ->
                                ((let uu____9612 =
                                    FStar_TypeChecker_Env.debug env
                                      (FStar_Options.Other "ED")
                                     in
                                  if uu____9612
                                  then
                                    let uu____9616 =
                                      FStar_Syntax_Print.term_to_string lift1
                                       in
                                    FStar_Util.print1 "Lift for free : %s\n"
                                      uu____9616
                                  else ());
                                 (let dmff_env =
                                    FStar_TypeChecker_DMFF.empty env
                                      (FStar_TypeChecker_TcTerm.tc_constant
                                         env FStar_Range.dummyRange)
                                     in
                                  let uu____9622 =
                                    let uu____9629 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env uvs
                                       in
                                    FStar_TypeChecker_TcTerm.tc_term
                                      uu____9629 lift1
                                     in
                                  match uu____9622 with
                                  | (lift2,comp,uu____9654) ->
                                      let uu____9655 =
                                        FStar_TypeChecker_DMFF.star_expr
                                          dmff_env lift2
                                         in
                                      (match uu____9655 with
                                       | (uu____9684,lift_wp,lift_elab) ->
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
                                             let uu____9716 =
                                               let uu____9727 =
                                                 FStar_TypeChecker_Util.generalize_universes
                                                   env lift_elab1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____9727
                                                in
                                             let uu____9744 =
                                               FStar_TypeChecker_Util.generalize_universes
                                                 env lift_wp1
                                                in
                                             (uu____9716, uu____9744)
                                           else
                                             (let uu____9773 =
                                                let uu____9784 =
                                                  let uu____9793 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs lift_elab1
                                                     in
                                                  (uvs, uu____9793)  in
                                                FStar_Pervasives_Native.Some
                                                  uu____9784
                                                 in
                                              let uu____9808 =
                                                let uu____9817 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    uvs lift_wp1
                                                   in
                                                (uvs, uu____9817)  in
                                              (uu____9773, uu____9808))))))
                        in
                     (match uu____9207 with
                      | (lift,lift_wp) ->
                          let env1 =
                            let uu___408_9891 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___408_9891.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___408_9891.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___408_9891.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___408_9891.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___408_9891.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___408_9891.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___408_9891.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___408_9891.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___408_9891.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___408_9891.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___408_9891.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___408_9891.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___408_9891.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___408_9891.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___408_9891.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___408_9891.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___408_9891.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___408_9891.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___408_9891.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___408_9891.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___408_9891.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___408_9891.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___408_9891.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___408_9891.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___408_9891.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___408_9891.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___408_9891.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___408_9891.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___408_9891.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___408_9891.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___408_9891.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___408_9891.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___408_9891.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___408_9891.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___408_9891.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___408_9891.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___408_9891.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___408_9891.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___408_9891.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___408_9891.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___408_9891.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___408_9891.FStar_TypeChecker_Env.nbe)
                            }  in
                          let lift1 =
                            match lift with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (uvs,lift1) ->
                                let uu____9924 =
                                  let uu____9929 =
                                    FStar_Syntax_Subst.univ_var_opening uvs
                                     in
                                  match uu____9929 with
                                  | (usubst,uvs1) ->
                                      let uu____9952 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1 uvs1
                                         in
                                      let uu____9953 =
                                        FStar_Syntax_Subst.subst usubst lift1
                                         in
                                      (uu____9952, uu____9953)
                                   in
                                (match uu____9924 with
                                 | (env2,lift2) ->
                                     let uu____9958 =
                                       let uu____9965 =
                                         FStar_TypeChecker_Env.lookup_effect_lid
                                           env2
                                           sub1.FStar_Syntax_Syntax.source
                                          in
                                       monad_signature env2
                                         sub1.FStar_Syntax_Syntax.source
                                         uu____9965
                                        in
                                     (match uu____9958 with
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
                                              let uu____9991 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              let uu____9992 =
                                                let uu____9999 =
                                                  let uu____10000 =
                                                    let uu____10017 =
                                                      let uu____10028 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          a_typ
                                                         in
                                                      let uu____10037 =
                                                        let uu____10048 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            wp_a_typ
                                                           in
                                                        [uu____10048]  in
                                                      uu____10028 ::
                                                        uu____10037
                                                       in
                                                    (lift_wp1, uu____10017)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10000
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____9999
                                                 in
                                              uu____9992
                                                FStar_Pervasives_Native.None
                                                uu____9991
                                               in
                                            repr_type
                                              sub1.FStar_Syntax_Syntax.target
                                              a_typ lift_wp_a
                                             in
                                          let expected_k1 =
                                            let uu____10099 =
                                              let uu____10108 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a1
                                                 in
                                              let uu____10115 =
                                                let uu____10124 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    wp_a
                                                   in
                                                let uu____10131 =
                                                  let uu____10140 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      repr_f
                                                     in
                                                  [uu____10140]  in
                                                uu____10124 :: uu____10131
                                                 in
                                              uu____10108 :: uu____10115  in
                                            let uu____10171 =
                                              FStar_Syntax_Syntax.mk_Total
                                                repr_result
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____10099 uu____10171
                                             in
                                          let uu____10174 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env2 expected_k1
                                             in
                                          (match uu____10174 with
                                           | (expected_k2,uu____10184,uu____10185)
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
                                                    let uu____10193 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        uvs lift3
                                                       in
                                                    (uvs, uu____10193))
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 lift3)))
                             in
                          ((let uu____10201 =
                              let uu____10203 =
                                let uu____10205 =
                                  FStar_All.pipe_right lift_wp
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____10205
                                  FStar_List.length
                                 in
                              uu____10203 <> (Prims.parse_int "1")  in
                            if uu____10201
                            then
                              let uu____10227 =
                                let uu____10233 =
                                  let uu____10235 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10237 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10239 =
                                    let uu____10241 =
                                      let uu____10243 =
                                        FStar_All.pipe_right lift_wp
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10243
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10241
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10235 uu____10237 uu____10239
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10233)
                                 in
                              FStar_Errors.raise_error uu____10227 r
                            else ());
                           (let uu____10270 =
                              (FStar_Util.is_some lift1) &&
                                (let uu____10273 =
                                   let uu____10275 =
                                     let uu____10278 =
                                       FStar_All.pipe_right lift1
                                         FStar_Util.must
                                        in
                                     FStar_All.pipe_right uu____10278
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____10275
                                     FStar_List.length
                                    in
                                 uu____10273 <> (Prims.parse_int "1"))
                               in
                            if uu____10270
                            then
                              let uu____10316 =
                                let uu____10322 =
                                  let uu____10324 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.source
                                     in
                                  let uu____10326 =
                                    FStar_Syntax_Print.lid_to_string
                                      sub1.FStar_Syntax_Syntax.target
                                     in
                                  let uu____10328 =
                                    let uu____10330 =
                                      let uu____10332 =
                                        let uu____10335 =
                                          FStar_All.pipe_right lift1
                                            FStar_Util.must
                                           in
                                        FStar_All.pipe_right uu____10335
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____10332
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____10330
                                      FStar_Util.string_of_int
                                     in
                                  FStar_Util.format3
                                    "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                    uu____10324 uu____10326 uu____10328
                                   in
                                (FStar_Errors.Fatal_TooManyUniverse,
                                  uu____10322)
                                 in
                              FStar_Errors.raise_error uu____10316 r
                            else ());
                           (let sub2 =
                              let uu___409_10378 = sub1  in
                              {
                                FStar_Syntax_Syntax.source =
                                  (uu___409_10378.FStar_Syntax_Syntax.source);
                                FStar_Syntax_Syntax.target =
                                  (uu___409_10378.FStar_Syntax_Syntax.target);
                                FStar_Syntax_Syntax.lift_wp =
                                  (FStar_Pervasives_Native.Some lift_wp);
                                FStar_Syntax_Syntax.lift = lift1
                              }  in
                            let se1 =
                              let uu___410_10380 = se  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_sub_effect sub2);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___410_10380.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___410_10380.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___410_10380.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___410_10380.FStar_Syntax_Syntax.sigattrs)
                              }  in
                            ([se1], [], env0))))))
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,flags1) ->
           let uu____10394 =
             if (FStar_List.length uvs) = (Prims.parse_int "0")
             then (env, uvs, tps, c)
             else
               (let uu____10422 = FStar_Syntax_Subst.univ_var_opening uvs  in
                match uu____10422 with
                | (usubst,uvs1) ->
                    let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                       in
                    let c1 =
                      let uu____10453 =
                        FStar_Syntax_Subst.shift_subst
                          (FStar_List.length tps1) usubst
                         in
                      FStar_Syntax_Subst.subst_comp uu____10453 c  in
                    let uu____10462 =
                      FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                    (uu____10462, uvs1, tps1, c1))
              in
           (match uu____10394 with
            | (env1,uvs1,tps1,c1) ->
                let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                let uu____10484 = FStar_Syntax_Subst.open_comp tps1 c1  in
                (match uu____10484 with
                 | (tps2,c2) ->
                     let uu____10501 =
                       FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                     (match uu____10501 with
                      | (tps3,env3,us) ->
                          let uu____10521 =
                            FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                          (match uu____10521 with
                           | (c3,u,g) ->
                               (FStar_TypeChecker_Rel.force_trivial_guard
                                  env3 g;
                                (let expected_result_typ =
                                   match tps3 with
                                   | (x,uu____10549)::uu____10550 ->
                                       FStar_Syntax_Syntax.bv_to_name x
                                   | uu____10569 ->
                                       FStar_Errors.raise_error
                                         (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                           "Effect abbreviations must bind at least the result type")
                                         r
                                    in
                                 let def_result_typ =
                                   FStar_Syntax_Util.comp_result c3  in
                                 let uu____10577 =
                                   let uu____10579 =
                                     FStar_TypeChecker_Rel.teq_nosmt_force
                                       env3 expected_result_typ
                                       def_result_typ
                                      in
                                   Prims.op_Negation uu____10579  in
                                 if uu____10577
                                 then
                                   let uu____10582 =
                                     let uu____10588 =
                                       let uu____10590 =
                                         FStar_Syntax_Print.term_to_string
                                           expected_result_typ
                                          in
                                       let uu____10592 =
                                         FStar_Syntax_Print.term_to_string
                                           def_result_typ
                                          in
                                       FStar_Util.format2
                                         "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                         uu____10590 uu____10592
                                        in
                                     (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                       uu____10588)
                                      in
                                   FStar_Errors.raise_error uu____10582 r
                                 else ());
                                (let tps4 =
                                   FStar_Syntax_Subst.close_binders tps3  in
                                 let c4 =
                                   FStar_Syntax_Subst.close_comp tps4 c3  in
                                 let uu____10600 =
                                   let uu____10601 =
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_arrow
                                          (tps4, c4))
                                       FStar_Pervasives_Native.None r
                                      in
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 uu____10601
                                    in
                                 match uu____10600 with
                                 | (uvs2,t) ->
                                     let uu____10632 =
                                       let uu____10637 =
                                         let uu____10650 =
                                           let uu____10651 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10651.FStar_Syntax_Syntax.n
                                            in
                                         (tps4, uu____10650)  in
                                       match uu____10637 with
                                       | ([],FStar_Syntax_Syntax.Tm_arrow
                                          (uu____10666,c5)) -> ([], c5)
                                       | (uu____10708,FStar_Syntax_Syntax.Tm_arrow
                                          (tps5,c5)) -> (tps5, c5)
                                       | uu____10747 ->
                                           failwith
                                             "Impossible (t is an arrow)"
                                        in
                                     (match uu____10632 with
                                      | (tps5,c5) ->
                                          (if
                                             (FStar_List.length uvs2) <>
                                               (Prims.parse_int "1")
                                           then
                                             (let uu____10781 =
                                                FStar_Syntax_Subst.open_univ_vars
                                                  uvs2 t
                                                 in
                                              match uu____10781 with
                                              | (uu____10786,t1) ->
                                                  let uu____10788 =
                                                    let uu____10794 =
                                                      let uu____10796 =
                                                        FStar_Syntax_Print.lid_to_string
                                                          lid
                                                         in
                                                      let uu____10798 =
                                                        FStar_All.pipe_right
                                                          (FStar_List.length
                                                             uvs2)
                                                          FStar_Util.string_of_int
                                                         in
                                                      let uu____10802 =
                                                        FStar_Syntax_Print.term_to_string
                                                          t1
                                                         in
                                                      FStar_Util.format3
                                                        "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                        uu____10796
                                                        uu____10798
                                                        uu____10802
                                                       in
                                                    (FStar_Errors.Fatal_TooManyUniverse,
                                                      uu____10794)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____10788 r)
                                           else ();
                                           (let se1 =
                                              let uu___411_10809 = se  in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                     (lid, uvs2, tps5, c5,
                                                       flags1));
                                                FStar_Syntax_Syntax.sigrng =
                                                  (uu___411_10809.FStar_Syntax_Syntax.sigrng);
                                                FStar_Syntax_Syntax.sigquals
                                                  =
                                                  (uu___411_10809.FStar_Syntax_Syntax.sigquals);
                                                FStar_Syntax_Syntax.sigmeta =
                                                  (uu___411_10809.FStar_Syntax_Syntax.sigmeta);
                                                FStar_Syntax_Syntax.sigattrs
                                                  =
                                                  (uu___411_10809.FStar_Syntax_Syntax.sigattrs)
                                              }  in
                                            ([se1], [], env0))))))))))
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____10816,uu____10817,uu____10818) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___375_10823  ->
                   match uu___375_10823 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____10826 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_let (uu____10832,uu____10833) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___375_10842  ->
                   match uu___375_10842 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____10845 -> false))
           -> ([], [], env0)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           ((let uu____10856 = FStar_TypeChecker_Env.lid_exists env1 lid  in
             if uu____10856
             then
               let uu____10859 =
                 let uu____10865 =
                   let uu____10867 = FStar_Ident.text_of_lid lid  in
                   FStar_Util.format1
                     "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                     uu____10867
                    in
                 (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                   uu____10865)
                  in
               FStar_Errors.raise_error uu____10859 r
             else ());
            (let uu____10873 =
               let uu____10882 =
                 (FStar_Options.use_two_phase_tc ()) &&
                   (FStar_TypeChecker_Env.should_verify env1)
                  in
               if uu____10882
               then
                 let uu____10893 =
                   tc_declare_typ
                     (let uu___412_10896 = env1  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___412_10896.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___412_10896.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___412_10896.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___412_10896.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___412_10896.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___412_10896.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___412_10896.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___412_10896.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___412_10896.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___412_10896.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___412_10896.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___412_10896.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___412_10896.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___412_10896.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___412_10896.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___412_10896.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___412_10896.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___412_10896.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___412_10896.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___412_10896.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax = true;
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___412_10896.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___412_10896.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___412_10896.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___412_10896.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___412_10896.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___412_10896.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___412_10896.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___412_10896.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___412_10896.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___412_10896.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___412_10896.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___412_10896.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___412_10896.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___412_10896.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___412_10896.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___412_10896.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___412_10896.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___412_10896.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___412_10896.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___412_10896.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv =
                          (uu___412_10896.FStar_TypeChecker_Env.dsenv);
                        FStar_TypeChecker_Env.nbe =
                          (uu___412_10896.FStar_TypeChecker_Env.nbe)
                      }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                    in
                 match uu____10893 with
                 | (uvs1,t1) ->
                     ((let uu____10921 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "TwoPhases")
                          in
                       if uu____10921
                       then
                         let uu____10926 =
                           FStar_Syntax_Print.term_to_string t1  in
                         let uu____10928 =
                           FStar_Syntax_Print.univ_names_to_string uvs1  in
                         FStar_Util.print2
                           "Val declaration after phase 1: %s and uvs: %s\n"
                           uu____10926 uu____10928
                       else ());
                      (uvs1, t1))
               else (uvs, t)  in
             match uu____10873 with
             | (uvs1,t1) ->
                 let uu____10963 =
                   tc_declare_typ env1 (uvs1, t1)
                     se.FStar_Syntax_Syntax.sigrng
                    in
                 (match uu____10963 with
                  | (uvs2,t2) ->
                      ([(let uu___413_10993 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (lid, uvs2, t2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___413_10993.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___413_10993.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___413_10993.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___413_10993.FStar_Syntax_Syntax.sigattrs)
                         })], [], env0))))
       | FStar_Syntax_Syntax.Sig_assume (lid,uvs,t) ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let uu____10998 =
             let uu____11007 =
               (FStar_Options.use_two_phase_tc ()) &&
                 (FStar_TypeChecker_Env.should_verify env1)
                in
             if uu____11007
             then
               let uu____11018 =
                 tc_assume
                   (let uu___414_11021 = env1  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___414_11021.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___414_11021.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___414_11021.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___414_11021.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___414_11021.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___414_11021.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___414_11021.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___414_11021.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___414_11021.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___414_11021.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___414_11021.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___414_11021.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___414_11021.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___414_11021.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___414_11021.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___414_11021.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___414_11021.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___414_11021.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___414_11021.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___414_11021.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax = true;
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___414_11021.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 = true;
                      FStar_TypeChecker_Env.failhard =
                        (uu___414_11021.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___414_11021.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___414_11021.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___414_11021.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___414_11021.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___414_11021.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___414_11021.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___414_11021.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___414_11021.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___414_11021.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___414_11021.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___414_11021.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___414_11021.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___414_11021.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___414_11021.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___414_11021.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___414_11021.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___414_11021.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___414_11021.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___414_11021.FStar_TypeChecker_Env.nbe)
                    }) (uvs, t) se.FStar_Syntax_Syntax.sigrng
                  in
               match uu____11018 with
               | (uvs1,t1) ->
                   ((let uu____11047 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases")
                        in
                     if uu____11047
                     then
                       let uu____11052 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____11054 =
                         FStar_Syntax_Print.univ_names_to_string uvs1  in
                       FStar_Util.print2
                         "Assume after phase 1: %s and uvs: %s\n" uu____11052
                         uu____11054
                     else ());
                    (uvs1, t1))
             else (uvs, t)  in
           (match uu____10998 with
            | (uvs1,t1) ->
                let uu____11089 =
                  tc_assume env1 (uvs1, t1) se.FStar_Syntax_Syntax.sigrng  in
                (match uu____11089 with
                 | (uvs2,t2) ->
                     ([(let uu___415_11119 = se  in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_assume (lid, uvs2, t2));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___415_11119.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___415_11119.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___415_11119.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___415_11119.FStar_Syntax_Syntax.sigattrs)
                        })], [], env0)))
       | FStar_Syntax_Syntax.Sig_main e ->
           let env1 = FStar_TypeChecker_Env.set_range env r  in
           let env2 =
             FStar_TypeChecker_Env.set_expected_typ env1
               FStar_Syntax_Syntax.t_unit
              in
           let uu____11123 = FStar_TypeChecker_TcTerm.tc_term env2 e  in
           (match uu____11123 with
            | (e1,c,g1) ->
                let uu____11143 =
                  let uu____11150 =
                    let uu____11153 =
                      FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r
                       in
                    FStar_Pervasives_Native.Some uu____11153  in
                  let uu____11154 =
                    let uu____11159 = FStar_Syntax_Syntax.lcomp_comp c  in
                    (e1, uu____11159)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env2
                    uu____11150 uu____11154
                   in
                (match uu____11143 with
                 | (e2,uu____11171,g) ->
                     ((let uu____11174 =
                         FStar_TypeChecker_Env.conj_guard g1 g  in
                       FStar_TypeChecker_Rel.force_trivial_guard env2
                         uu____11174);
                      (let se1 =
                         let uu___416_11176 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_main e2);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___416_11176.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___416_11176.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___416_11176.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___416_11176.FStar_Syntax_Syntax.sigattrs)
                         }  in
                       ([se1], [], env0)))))
       | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
           ((let uu____11188 = FStar_Options.debug_any ()  in
             if uu____11188
             then
               let uu____11191 =
                 FStar_Ident.string_of_lid
                   env.FStar_TypeChecker_Env.curmodule
                  in
               let uu____11193 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print2 "%s: Found splice of (%s)\n" uu____11191
                 uu____11193
             else ());
            (let uu____11198 = FStar_TypeChecker_TcTerm.tc_tactic env t  in
             match uu____11198 with
             | (t1,uu____11216,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env g;
                  (let ses = env.FStar_TypeChecker_Env.splice env t1  in
                   let lids' =
                     FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses
                      in
                   FStar_List.iter
                     (fun lid  ->
                        let uu____11230 =
                          FStar_List.tryFind (FStar_Ident.lid_equals lid)
                            lids'
                           in
                        match uu____11230 with
                        | FStar_Pervasives_Native.None  when
                            Prims.op_Negation
                              env.FStar_TypeChecker_Env.nosynth
                            ->
                            let uu____11233 =
                              let uu____11239 =
                                let uu____11241 =
                                  FStar_Ident.string_of_lid lid  in
                                let uu____11243 =
                                  let uu____11245 =
                                    FStar_List.map FStar_Ident.string_of_lid
                                      lids'
                                     in
                                  FStar_All.pipe_left
                                    (FStar_String.concat ", ") uu____11245
                                   in
                                FStar_Util.format2
                                  "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                  uu____11241 uu____11243
                                 in
                              (FStar_Errors.Fatal_SplicedUndef, uu____11239)
                               in
                            FStar_Errors.raise_error uu____11233 r
                        | uu____11257 -> ()) lids;
                   (let dsenv1 =
                      FStar_List.fold_left
                        FStar_Syntax_DsEnv.push_sigelt_force
                        env.FStar_TypeChecker_Env.dsenv ses
                       in
                    let env1 =
                      let uu___417_11262 = env  in
                      {
                        FStar_TypeChecker_Env.solver =
                          (uu___417_11262.FStar_TypeChecker_Env.solver);
                        FStar_TypeChecker_Env.range =
                          (uu___417_11262.FStar_TypeChecker_Env.range);
                        FStar_TypeChecker_Env.curmodule =
                          (uu___417_11262.FStar_TypeChecker_Env.curmodule);
                        FStar_TypeChecker_Env.gamma =
                          (uu___417_11262.FStar_TypeChecker_Env.gamma);
                        FStar_TypeChecker_Env.gamma_sig =
                          (uu___417_11262.FStar_TypeChecker_Env.gamma_sig);
                        FStar_TypeChecker_Env.gamma_cache =
                          (uu___417_11262.FStar_TypeChecker_Env.gamma_cache);
                        FStar_TypeChecker_Env.modules =
                          (uu___417_11262.FStar_TypeChecker_Env.modules);
                        FStar_TypeChecker_Env.expected_typ =
                          (uu___417_11262.FStar_TypeChecker_Env.expected_typ);
                        FStar_TypeChecker_Env.sigtab =
                          (uu___417_11262.FStar_TypeChecker_Env.sigtab);
                        FStar_TypeChecker_Env.attrtab =
                          (uu___417_11262.FStar_TypeChecker_Env.attrtab);
                        FStar_TypeChecker_Env.is_pattern =
                          (uu___417_11262.FStar_TypeChecker_Env.is_pattern);
                        FStar_TypeChecker_Env.instantiate_imp =
                          (uu___417_11262.FStar_TypeChecker_Env.instantiate_imp);
                        FStar_TypeChecker_Env.effects =
                          (uu___417_11262.FStar_TypeChecker_Env.effects);
                        FStar_TypeChecker_Env.generalize =
                          (uu___417_11262.FStar_TypeChecker_Env.generalize);
                        FStar_TypeChecker_Env.letrecs =
                          (uu___417_11262.FStar_TypeChecker_Env.letrecs);
                        FStar_TypeChecker_Env.top_level =
                          (uu___417_11262.FStar_TypeChecker_Env.top_level);
                        FStar_TypeChecker_Env.check_uvars =
                          (uu___417_11262.FStar_TypeChecker_Env.check_uvars);
                        FStar_TypeChecker_Env.use_eq =
                          (uu___417_11262.FStar_TypeChecker_Env.use_eq);
                        FStar_TypeChecker_Env.is_iface =
                          (uu___417_11262.FStar_TypeChecker_Env.is_iface);
                        FStar_TypeChecker_Env.admit =
                          (uu___417_11262.FStar_TypeChecker_Env.admit);
                        FStar_TypeChecker_Env.lax =
                          (uu___417_11262.FStar_TypeChecker_Env.lax);
                        FStar_TypeChecker_Env.lax_universes =
                          (uu___417_11262.FStar_TypeChecker_Env.lax_universes);
                        FStar_TypeChecker_Env.phase1 =
                          (uu___417_11262.FStar_TypeChecker_Env.phase1);
                        FStar_TypeChecker_Env.failhard =
                          (uu___417_11262.FStar_TypeChecker_Env.failhard);
                        FStar_TypeChecker_Env.nosynth =
                          (uu___417_11262.FStar_TypeChecker_Env.nosynth);
                        FStar_TypeChecker_Env.uvar_subtyping =
                          (uu___417_11262.FStar_TypeChecker_Env.uvar_subtyping);
                        FStar_TypeChecker_Env.tc_term =
                          (uu___417_11262.FStar_TypeChecker_Env.tc_term);
                        FStar_TypeChecker_Env.type_of =
                          (uu___417_11262.FStar_TypeChecker_Env.type_of);
                        FStar_TypeChecker_Env.universe_of =
                          (uu___417_11262.FStar_TypeChecker_Env.universe_of);
                        FStar_TypeChecker_Env.check_type_of =
                          (uu___417_11262.FStar_TypeChecker_Env.check_type_of);
                        FStar_TypeChecker_Env.use_bv_sorts =
                          (uu___417_11262.FStar_TypeChecker_Env.use_bv_sorts);
                        FStar_TypeChecker_Env.qtbl_name_and_index =
                          (uu___417_11262.FStar_TypeChecker_Env.qtbl_name_and_index);
                        FStar_TypeChecker_Env.normalized_eff_names =
                          (uu___417_11262.FStar_TypeChecker_Env.normalized_eff_names);
                        FStar_TypeChecker_Env.fv_delta_depths =
                          (uu___417_11262.FStar_TypeChecker_Env.fv_delta_depths);
                        FStar_TypeChecker_Env.proof_ns =
                          (uu___417_11262.FStar_TypeChecker_Env.proof_ns);
                        FStar_TypeChecker_Env.synth_hook =
                          (uu___417_11262.FStar_TypeChecker_Env.synth_hook);
                        FStar_TypeChecker_Env.splice =
                          (uu___417_11262.FStar_TypeChecker_Env.splice);
                        FStar_TypeChecker_Env.postprocess =
                          (uu___417_11262.FStar_TypeChecker_Env.postprocess);
                        FStar_TypeChecker_Env.is_native_tactic =
                          (uu___417_11262.FStar_TypeChecker_Env.is_native_tactic);
                        FStar_TypeChecker_Env.identifier_info =
                          (uu___417_11262.FStar_TypeChecker_Env.identifier_info);
                        FStar_TypeChecker_Env.tc_hooks =
                          (uu___417_11262.FStar_TypeChecker_Env.tc_hooks);
                        FStar_TypeChecker_Env.dsenv = dsenv1;
                        FStar_TypeChecker_Env.nbe =
                          (uu___417_11262.FStar_TypeChecker_Env.nbe)
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
                 let uu____11330 =
                   let uu____11332 =
                     let uu____11341 = drop_logic val_q  in
                     let uu____11344 = drop_logic q'  in
                     (uu____11341, uu____11344)  in
                   match uu____11332 with
                   | (val_q1,q'1) ->
                       ((FStar_List.length val_q1) = (FStar_List.length q'1))
                         &&
                         (FStar_List.forall2
                            FStar_Syntax_Util.qualifier_equal val_q1 q'1)
                    in
                 if uu____11330
                 then FStar_Pervasives_Native.Some q'
                 else
                   (let uu____11371 =
                      let uu____11377 =
                        let uu____11379 = FStar_Syntax_Print.lid_to_string l
                           in
                        let uu____11381 =
                          FStar_Syntax_Print.quals_to_string val_q  in
                        let uu____11383 =
                          FStar_Syntax_Print.quals_to_string q'  in
                        FStar_Util.format3
                          "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                          uu____11379 uu____11381 uu____11383
                         in
                      (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                        uu____11377)
                       in
                    FStar_Errors.raise_error uu____11371 r)
              in
           let rename_parameters lb =
             let rename_in_typ def typ =
               let typ1 = FStar_Syntax_Subst.compress typ  in
               let def_bs =
                 let uu____11420 =
                   let uu____11421 = FStar_Syntax_Subst.compress def  in
                   uu____11421.FStar_Syntax_Syntax.n  in
                 match uu____11420 with
                 | FStar_Syntax_Syntax.Tm_abs
                     (binders,uu____11433,uu____11434) -> binders
                 | uu____11459 -> []  in
               match typ1 with
               | {
                   FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                     (val_bs,c);
                   FStar_Syntax_Syntax.pos = r1;
                   FStar_Syntax_Syntax.vars = uu____11471;_} ->
                   let has_auto_name bv =
                     FStar_Util.starts_with
                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                       FStar_Ident.reserved_prefix
                      in
                   let rec rename_binders1 def_bs1 val_bs1 =
                     match (def_bs1, val_bs1) with
                     | ([],uu____11576) -> val_bs1
                     | (uu____11607,[]) -> val_bs1
                     | ((body_bv,uu____11639)::bt,(val_bv,aqual)::vt) ->
                         let uu____11696 = rename_binders1 bt vt  in
                         ((match ((has_auto_name body_bv),
                                   (has_auto_name val_bv))
                           with
                           | (true ,uu____11720) -> (val_bv, aqual)
                           | (false ,true ) ->
                               ((let uu___418_11734 = val_bv  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (let uu___419_11737 =
                                        val_bv.FStar_Syntax_Syntax.ppname  in
                                      {
                                        FStar_Ident.idText =
                                          ((body_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText);
                                        FStar_Ident.idRange =
                                          (uu___419_11737.FStar_Ident.idRange)
                                      });
                                   FStar_Syntax_Syntax.index =
                                     (uu___418_11734.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort =
                                     (uu___418_11734.FStar_Syntax_Syntax.sort)
                                 }), aqual)
                           | (false ,false ) -> (val_bv, aqual))) ::
                           uu____11696
                      in
                   let uu____11744 =
                     let uu____11751 =
                       let uu____11752 =
                         let uu____11767 = rename_binders1 def_bs val_bs  in
                         (uu____11767, c)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____11752  in
                     FStar_Syntax_Syntax.mk uu____11751  in
                   uu____11744 FStar_Pervasives_Native.None r1
               | uu____11789 -> typ1  in
             let uu___420_11790 = lb  in
             let uu____11791 =
               rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                 lb.FStar_Syntax_Syntax.lbtyp
                in
             {
               FStar_Syntax_Syntax.lbname =
                 (uu___420_11790.FStar_Syntax_Syntax.lbname);
               FStar_Syntax_Syntax.lbunivs =
                 (uu___420_11790.FStar_Syntax_Syntax.lbunivs);
               FStar_Syntax_Syntax.lbtyp = uu____11791;
               FStar_Syntax_Syntax.lbeff =
                 (uu___420_11790.FStar_Syntax_Syntax.lbeff);
               FStar_Syntax_Syntax.lbdef =
                 (uu___420_11790.FStar_Syntax_Syntax.lbdef);
               FStar_Syntax_Syntax.lbattrs =
                 (uu___420_11790.FStar_Syntax_Syntax.lbattrs);
               FStar_Syntax_Syntax.lbpos =
                 (uu___420_11790.FStar_Syntax_Syntax.lbpos)
             }  in
           let uu____11794 =
             FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
               (FStar_List.fold_left
                  (fun uu____11849  ->
                     fun lb  ->
                       match uu____11849 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____11895 =
                             let uu____11907 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env1
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____11907 with
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
                                   | uu____11987 ->
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
                                  (let uu____12034 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Parser_Const.effect_ALL_lid,
                                         tval, def, [],
                                         (lb.FStar_Syntax_Syntax.lbpos))
                                      in
                                   (false, uu____12034, quals_opt1)))
                              in
                           (match uu____11895 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [],
                    (if se.FStar_Syntax_Syntax.sigquals = []
                     then FStar_Pervasives_Native.None
                     else
                       FStar_Pervasives_Native.Some
                         (se.FStar_Syntax_Syntax.sigquals))))
              in
           (match uu____11794 with
            | (should_generalize,lbs',quals_opt) ->
                let quals =
                  match quals_opt with
                  | FStar_Pervasives_Native.None  ->
                      [FStar_Syntax_Syntax.Visible_default]
                  | FStar_Pervasives_Native.Some q ->
                      let uu____12138 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___376_12144  ->
                                match uu___376_12144 with
                                | FStar_Syntax_Syntax.Irreducible  -> true
                                | FStar_Syntax_Syntax.Visible_default  ->
                                    true
                                | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                     -> true
                                | uu____12149 -> false))
                         in
                      if uu____12138
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____12162 =
                    let uu____12169 =
                      let uu____12170 =
                        let uu____12184 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                            FStar_Pervasives_Native.None r
                           in
                        (((FStar_Pervasives_Native.fst lbs), lbs'1),
                          uu____12184)
                         in
                      FStar_Syntax_Syntax.Tm_let uu____12170  in
                    FStar_Syntax_Syntax.mk uu____12169  in
                  uu____12162 FStar_Pervasives_Native.None r  in
                let env' =
                  let uu___421_12206 = env1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___421_12206.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___421_12206.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___421_12206.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___421_12206.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___421_12206.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___421_12206.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___421_12206.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___421_12206.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___421_12206.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___421_12206.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___421_12206.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___421_12206.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___421_12206.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize = should_generalize;
                    FStar_TypeChecker_Env.letrecs =
                      (uu___421_12206.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level = true;
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___421_12206.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___421_12206.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___421_12206.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___421_12206.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___421_12206.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___421_12206.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___421_12206.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___421_12206.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___421_12206.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___421_12206.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___421_12206.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___421_12206.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___421_12206.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___421_12206.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___421_12206.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___421_12206.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___421_12206.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___421_12206.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___421_12206.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___421_12206.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___421_12206.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___421_12206.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___421_12206.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___421_12206.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___421_12206.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___421_12206.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___421_12206.FStar_TypeChecker_Env.nbe)
                  }  in
                let e1 =
                  let uu____12209 =
                    (FStar_Options.use_two_phase_tc ()) &&
                      (FStar_TypeChecker_Env.should_verify env')
                     in
                  if uu____12209
                  then
                    let drop_lbtyp e_lax =
                      let uu____12218 =
                        let uu____12219 = FStar_Syntax_Subst.compress e_lax
                           in
                        uu____12219.FStar_Syntax_Syntax.n  in
                      match uu____12218 with
                      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
                          let lb_unannotated =
                            let uu____12241 =
                              let uu____12242 = FStar_Syntax_Subst.compress e
                                 in
                              uu____12242.FStar_Syntax_Syntax.n  in
                            match uu____12241 with
                            | FStar_Syntax_Syntax.Tm_let
                                ((uu____12246,lb1::[]),uu____12248) ->
                                let uu____12264 =
                                  let uu____12265 =
                                    FStar_Syntax_Subst.compress
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                     in
                                  uu____12265.FStar_Syntax_Syntax.n  in
                                (match uu____12264 with
                                 | FStar_Syntax_Syntax.Tm_unknown  -> true
                                 | uu____12270 -> false)
                            | uu____12272 ->
                                failwith
                                  "Impossible: first phase lb and second phase lb differ in structure!"
                             in
                          if lb_unannotated
                          then
                            let uu___422_12276 = e_lax  in
                            {
                              FStar_Syntax_Syntax.n =
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false,
                                      [(let uu___423_12291 = lb  in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            (uu___423_12291.FStar_Syntax_Syntax.lbname);
                                          FStar_Syntax_Syntax.lbunivs =
                                            (uu___423_12291.FStar_Syntax_Syntax.lbunivs);
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            (uu___423_12291.FStar_Syntax_Syntax.lbeff);
                                          FStar_Syntax_Syntax.lbdef =
                                            (uu___423_12291.FStar_Syntax_Syntax.lbdef);
                                          FStar_Syntax_Syntax.lbattrs =
                                            (uu___423_12291.FStar_Syntax_Syntax.lbattrs);
                                          FStar_Syntax_Syntax.lbpos =
                                            (uu___423_12291.FStar_Syntax_Syntax.lbpos)
                                        })]), e2));
                              FStar_Syntax_Syntax.pos =
                                (uu___422_12276.FStar_Syntax_Syntax.pos);
                              FStar_Syntax_Syntax.vars =
                                (uu___422_12276.FStar_Syntax_Syntax.vars)
                            }
                          else e_lax
                      | uu____12294 -> e_lax  in
                    let e1 =
                      let uu____12296 =
                        let uu____12297 =
                          let uu____12298 =
                            FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                              (let uu___424_12307 = env'  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___424_12307.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___424_12307.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___424_12307.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___424_12307.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___424_12307.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___424_12307.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___424_12307.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___424_12307.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___424_12307.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___424_12307.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___424_12307.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___424_12307.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___424_12307.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___424_12307.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___424_12307.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___424_12307.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___424_12307.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___424_12307.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___424_12307.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___424_12307.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___424_12307.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 = true;
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___424_12307.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___424_12307.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___424_12307.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___424_12307.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___424_12307.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___424_12307.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___424_12307.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___424_12307.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___424_12307.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___424_12307.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___424_12307.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___424_12307.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___424_12307.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___424_12307.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___424_12307.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___424_12307.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___424_12307.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___424_12307.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___424_12307.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___424_12307.FStar_TypeChecker_Env.nbe)
                               }) e
                             in
                          FStar_All.pipe_right uu____12298
                            (fun uu____12320  ->
                               match uu____12320 with
                               | (e1,uu____12328,uu____12329) -> e1)
                           in
                        FStar_All.pipe_right uu____12297
                          (FStar_TypeChecker_Normalize.remove_uvar_solutions
                             env')
                         in
                      FStar_All.pipe_right uu____12296 drop_lbtyp  in
                    ((let uu____12331 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "TwoPhases")
                         in
                      if uu____12331
                      then
                        let uu____12336 =
                          FStar_Syntax_Print.term_to_string e1  in
                        FStar_Util.print1 "Let binding after phase 1: %s\n"
                          uu____12336
                      else ());
                     e1)
                  else e  in
                let uu____12343 =
                  let uu____12352 =
                    FStar_Syntax_Util.extract_attr'
                      FStar_Parser_Const.postprocess_with
                      se.FStar_Syntax_Syntax.sigattrs
                     in
                  match uu____12352 with
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
                (match uu____12343 with
                 | (attrs,post_tau) ->
                     let se1 =
                       let uu___425_12457 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (uu___425_12457.FStar_Syntax_Syntax.sigel);
                         FStar_Syntax_Syntax.sigrng =
                           (uu___425_12457.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___425_12457.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___425_12457.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs = attrs
                       }  in
                     let postprocess_lb tau lb =
                       let lbdef =
                         env1.FStar_TypeChecker_Env.postprocess env1 tau
                           lb.FStar_Syntax_Syntax.lbtyp
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       let uu___426_12470 = lb  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___426_12470.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___426_12470.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp =
                           (uu___426_12470.FStar_Syntax_Syntax.lbtyp);
                         FStar_Syntax_Syntax.lbeff =
                           (uu___426_12470.FStar_Syntax_Syntax.lbeff);
                         FStar_Syntax_Syntax.lbdef = lbdef;
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___426_12470.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___426_12470.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let uu____12471 =
                       let uu____12483 =
                         FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env'
                           e1
                          in
                       match uu____12483 with
                       | ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_let (lbs1,e2);
                            FStar_Syntax_Syntax.pos = uu____12503;
                            FStar_Syntax_Syntax.vars = uu____12504;_},uu____12505,g)
                           when FStar_TypeChecker_Env.is_trivial g ->
                           let lbs2 =
                             let uu____12535 =
                               FStar_All.pipe_right
                                 (FStar_Pervasives_Native.snd lbs1)
                                 (FStar_List.map rename_parameters)
                                in
                             ((FStar_Pervasives_Native.fst lbs1),
                               uu____12535)
                              in
                           let lbs3 =
                             let uu____12559 =
                               match post_tau with
                               | FStar_Pervasives_Native.Some tau ->
                                   FStar_List.map (postprocess_lb tau)
                                     (FStar_Pervasives_Native.snd lbs2)
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.snd lbs2
                                in
                             ((FStar_Pervasives_Native.fst lbs2),
                               uu____12559)
                              in
                           let quals1 =
                             match e2.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_meta
                                 (uu____12582,FStar_Syntax_Syntax.Meta_desugared
                                  (FStar_Syntax_Syntax.Masked_effect ))
                                 -> FStar_Syntax_Syntax.HasMaskedEffect ::
                                 quals
                             | uu____12587 -> quals  in
                           ((let uu___427_12596 = se1  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_let (lbs3, lids));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___427_12596.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals = quals1;
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___427_12596.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___427_12596.FStar_Syntax_Syntax.sigattrs)
                             }), lbs3)
                       | uu____12599 ->
                           failwith
                             "impossible (typechecking should preserve Tm_let)"
                        in
                     (match uu____12471 with
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
                           (let uu____12655 = log env1  in
                            if uu____12655
                            then
                              let uu____12658 =
                                let uu____12660 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs1)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let should_log =
                                            let uu____12680 =
                                              let uu____12689 =
                                                let uu____12690 =
                                                  let uu____12693 =
                                                    FStar_Util.right
                                                      lb.FStar_Syntax_Syntax.lbname
                                                     in
                                                  uu____12693.FStar_Syntax_Syntax.fv_name
                                                   in
                                                uu____12690.FStar_Syntax_Syntax.v
                                                 in
                                              FStar_TypeChecker_Env.try_lookup_val_decl
                                                env1 uu____12689
                                               in
                                            match uu____12680 with
                                            | FStar_Pervasives_Native.None 
                                                -> true
                                            | uu____12702 -> false  in
                                          if should_log
                                          then
                                            let uu____12714 =
                                              FStar_Syntax_Print.lbname_to_string
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            let uu____12716 =
                                              FStar_Syntax_Print.term_to_string
                                                lb.FStar_Syntax_Syntax.lbtyp
                                               in
                                            FStar_Util.format2 "let %s : %s"
                                              uu____12714 uu____12716
                                          else ""))
                                   in
                                FStar_All.pipe_right uu____12660
                                  (FStar_String.concat "\n")
                                 in
                              FStar_Util.print1 "%s\n" uu____12658
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
      (let uu____12768 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low
          in
       if uu____12768
       then
         let uu____12771 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____12771
       else ());
      (let uu____12776 = get_fail_se se  in
       match uu____12776 with
       | FStar_Pervasives_Native.Some (uu____12797,false ) when
           let uu____12814 = FStar_TypeChecker_Env.should_verify env1  in
           Prims.op_Negation uu____12814 -> ([], [], env1)
       | FStar_Pervasives_Native.Some (errnos,lax1) ->
           let env' =
             if lax1
             then
               let uu___428_12840 = env1  in
               {
                 FStar_TypeChecker_Env.solver =
                   (uu___428_12840.FStar_TypeChecker_Env.solver);
                 FStar_TypeChecker_Env.range =
                   (uu___428_12840.FStar_TypeChecker_Env.range);
                 FStar_TypeChecker_Env.curmodule =
                   (uu___428_12840.FStar_TypeChecker_Env.curmodule);
                 FStar_TypeChecker_Env.gamma =
                   (uu___428_12840.FStar_TypeChecker_Env.gamma);
                 FStar_TypeChecker_Env.gamma_sig =
                   (uu___428_12840.FStar_TypeChecker_Env.gamma_sig);
                 FStar_TypeChecker_Env.gamma_cache =
                   (uu___428_12840.FStar_TypeChecker_Env.gamma_cache);
                 FStar_TypeChecker_Env.modules =
                   (uu___428_12840.FStar_TypeChecker_Env.modules);
                 FStar_TypeChecker_Env.expected_typ =
                   (uu___428_12840.FStar_TypeChecker_Env.expected_typ);
                 FStar_TypeChecker_Env.sigtab =
                   (uu___428_12840.FStar_TypeChecker_Env.sigtab);
                 FStar_TypeChecker_Env.attrtab =
                   (uu___428_12840.FStar_TypeChecker_Env.attrtab);
                 FStar_TypeChecker_Env.is_pattern =
                   (uu___428_12840.FStar_TypeChecker_Env.is_pattern);
                 FStar_TypeChecker_Env.instantiate_imp =
                   (uu___428_12840.FStar_TypeChecker_Env.instantiate_imp);
                 FStar_TypeChecker_Env.effects =
                   (uu___428_12840.FStar_TypeChecker_Env.effects);
                 FStar_TypeChecker_Env.generalize =
                   (uu___428_12840.FStar_TypeChecker_Env.generalize);
                 FStar_TypeChecker_Env.letrecs =
                   (uu___428_12840.FStar_TypeChecker_Env.letrecs);
                 FStar_TypeChecker_Env.top_level =
                   (uu___428_12840.FStar_TypeChecker_Env.top_level);
                 FStar_TypeChecker_Env.check_uvars =
                   (uu___428_12840.FStar_TypeChecker_Env.check_uvars);
                 FStar_TypeChecker_Env.use_eq =
                   (uu___428_12840.FStar_TypeChecker_Env.use_eq);
                 FStar_TypeChecker_Env.is_iface =
                   (uu___428_12840.FStar_TypeChecker_Env.is_iface);
                 FStar_TypeChecker_Env.admit =
                   (uu___428_12840.FStar_TypeChecker_Env.admit);
                 FStar_TypeChecker_Env.lax = true;
                 FStar_TypeChecker_Env.lax_universes =
                   (uu___428_12840.FStar_TypeChecker_Env.lax_universes);
                 FStar_TypeChecker_Env.phase1 =
                   (uu___428_12840.FStar_TypeChecker_Env.phase1);
                 FStar_TypeChecker_Env.failhard =
                   (uu___428_12840.FStar_TypeChecker_Env.failhard);
                 FStar_TypeChecker_Env.nosynth =
                   (uu___428_12840.FStar_TypeChecker_Env.nosynth);
                 FStar_TypeChecker_Env.uvar_subtyping =
                   (uu___428_12840.FStar_TypeChecker_Env.uvar_subtyping);
                 FStar_TypeChecker_Env.tc_term =
                   (uu___428_12840.FStar_TypeChecker_Env.tc_term);
                 FStar_TypeChecker_Env.type_of =
                   (uu___428_12840.FStar_TypeChecker_Env.type_of);
                 FStar_TypeChecker_Env.universe_of =
                   (uu___428_12840.FStar_TypeChecker_Env.universe_of);
                 FStar_TypeChecker_Env.check_type_of =
                   (uu___428_12840.FStar_TypeChecker_Env.check_type_of);
                 FStar_TypeChecker_Env.use_bv_sorts =
                   (uu___428_12840.FStar_TypeChecker_Env.use_bv_sorts);
                 FStar_TypeChecker_Env.qtbl_name_and_index =
                   (uu___428_12840.FStar_TypeChecker_Env.qtbl_name_and_index);
                 FStar_TypeChecker_Env.normalized_eff_names =
                   (uu___428_12840.FStar_TypeChecker_Env.normalized_eff_names);
                 FStar_TypeChecker_Env.fv_delta_depths =
                   (uu___428_12840.FStar_TypeChecker_Env.fv_delta_depths);
                 FStar_TypeChecker_Env.proof_ns =
                   (uu___428_12840.FStar_TypeChecker_Env.proof_ns);
                 FStar_TypeChecker_Env.synth_hook =
                   (uu___428_12840.FStar_TypeChecker_Env.synth_hook);
                 FStar_TypeChecker_Env.splice =
                   (uu___428_12840.FStar_TypeChecker_Env.splice);
                 FStar_TypeChecker_Env.postprocess =
                   (uu___428_12840.FStar_TypeChecker_Env.postprocess);
                 FStar_TypeChecker_Env.is_native_tactic =
                   (uu___428_12840.FStar_TypeChecker_Env.is_native_tactic);
                 FStar_TypeChecker_Env.identifier_info =
                   (uu___428_12840.FStar_TypeChecker_Env.identifier_info);
                 FStar_TypeChecker_Env.tc_hooks =
                   (uu___428_12840.FStar_TypeChecker_Env.tc_hooks);
                 FStar_TypeChecker_Env.dsenv =
                   (uu___428_12840.FStar_TypeChecker_Env.dsenv);
                 FStar_TypeChecker_Env.nbe =
                   (uu___428_12840.FStar_TypeChecker_Env.nbe)
               }
             else env1  in
           ((let uu____12845 =
               FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
             if uu____12845
             then
               let uu____12848 =
                 let uu____12850 =
                   FStar_List.map FStar_Util.string_of_int errnos  in
                 FStar_All.pipe_left (FStar_String.concat "; ") uu____12850
                  in
               FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____12848
             else ());
            (let uu____12864 =
               FStar_Errors.catch_errors
                 (fun uu____12894  ->
                    FStar_Options.with_saved_options
                      (fun uu____12906  -> tc_decl' env' se))
                in
             match uu____12864 with
             | (errs,uu____12918) ->
                 ((let uu____12948 =
                     FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
                   if uu____12948
                   then
                     (FStar_Util.print_string ">> Got issues: [\n";
                      FStar_List.iter FStar_Errors.print_issue errs;
                      FStar_Util.print_string ">>]\n")
                   else ());
                  (let sort = FStar_List.sortWith (fun x  -> fun y  -> x - y)
                      in
                   let errnos1 = sort errnos  in
                   let actual =
                     let uu____12983 =
                       FStar_List.concatMap
                         (fun i  ->
                            list_of_option i.FStar_Errors.issue_number) errs
                        in
                     sort uu____12983  in
                   (match errs with
                    | [] ->
                        (FStar_List.iter FStar_Errors.print_issue errs;
                         FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                           (FStar_Errors.Error_DidNotFail,
                             "This top-level definition was expected to fail, but it succeeded"))
                    | uu____12995 ->
                        if (errnos1 <> []) && (errnos1 <> actual)
                        then
                          let uu____13006 =
                            let uu____13016 =
                              check_multi_contained errnos1 actual  in
                            match uu____13016 with
                            | FStar_Pervasives_Native.Some r -> r
                            | FStar_Pervasives_Native.None  ->
                                ((~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")),
                                  (~- (Prims.parse_int "1")))
                             in
                          (match uu____13006 with
                           | (e,n1,n2) ->
                               (FStar_List.iter FStar_Errors.print_issue errs;
                                (let uu____13081 =
                                   let uu____13087 =
                                     let uu____13089 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int errnos1
                                        in
                                     let uu____13092 =
                                       FStar_Common.string_of_list
                                         FStar_Util.string_of_int actual
                                        in
                                     let uu____13095 =
                                       FStar_Util.string_of_int e  in
                                     let uu____13097 =
                                       FStar_Util.string_of_int n2  in
                                     let uu____13099 =
                                       FStar_Util.string_of_int n1  in
                                     FStar_Util.format5
                                       "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                       uu____13089 uu____13092 uu____13095
                                       uu____13097 uu____13099
                                      in
                                   (FStar_Errors.Error_DidNotFail,
                                     uu____13087)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____13081)))
                        else ());
                   ([], [], env1)))))
       | FStar_Pervasives_Native.None  -> tc_decl' env1 se)
  
let for_export :
  'Auu____13126 .
    'Auu____13126 ->
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
               (fun uu___377_13169  ->
                  match uu___377_13169 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | uu____13172 -> false))
           in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l,uu____13183) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____13191 -> false  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____13201 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_splice uu____13206 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____13222 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____13248 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13274) ->
            let uu____13283 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13283
            then
              let for_export_bundle se1 uu____13320 =
                match uu____13320 with
                | (out,hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,us,bs,t,uu____13359,uu____13360) ->
                         let dec =
                           let uu___429_13370 = se1  in
                           let uu____13371 =
                             let uu____13372 =
                               let uu____13379 =
                                 let uu____13380 =
                                   FStar_Syntax_Syntax.mk_Total t  in
                                 FStar_Syntax_Util.arrow bs uu____13380  in
                               (l, us, uu____13379)  in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____13372
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____13371;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___429_13370.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___429_13370.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___429_13370.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l,us,t,uu____13390,uu____13391,uu____13392) ->
                         let dec =
                           let uu___430_13400 = se1  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___430_13400.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___430_13400.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___430_13400.FStar_Syntax_Syntax.sigattrs)
                           }  in
                         ((dec :: out), (l :: hidden1))
                     | uu____13405 -> (out, hidden1))
                 in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume
            (uu____13428,uu____13429,uu____13430) ->
            let uu____13431 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13431 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t) ->
            let uu____13455 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc)
               in
            if uu____13455
            then
              ([(let uu___431_13474 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___431_13474.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___431_13474.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___431_13474.FStar_Syntax_Syntax.sigattrs)
                 })], (l :: hidden))
            else
              (let uu____13477 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___378_13483  ->
                         match uu___378_13483 with
                         | FStar_Syntax_Syntax.Assumption  -> true
                         | FStar_Syntax_Syntax.Projector uu____13486 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____13492 ->
                             true
                         | uu____13494 -> false))
                  in
               if uu____13477 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_main uu____13515 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_new_effect uu____13520 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____13525 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13530 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13548) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____13562 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
               in
            if uu____13562
            then ([], hidden)
            else
              (let dec =
                 let uu____13583 = FStar_Ident.range_of_lid lid  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____13583;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs,l) ->
            let uu____13594 = is_abstract se.FStar_Syntax_Syntax.sigquals  in
            if uu____13594
            then
              let uu____13605 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb  ->
                        let uu___432_13619 = se  in
                        let uu____13620 =
                          let uu____13621 =
                            let uu____13628 =
                              let uu____13629 =
                                let uu____13632 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                uu____13632.FStar_Syntax_Syntax.fv_name  in
                              uu____13629.FStar_Syntax_Syntax.v  in
                            (uu____13628, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp))
                             in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____13621  in
                        {
                          FStar_Syntax_Syntax.sigel = uu____13620;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___432_13619.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___432_13619.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___432_13619.FStar_Syntax_Syntax.sigattrs)
                        }))
                 in
              (uu____13605, hidden)
            else ([se], hidden)
  
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun se  ->
      (let uu____13655 = FStar_TypeChecker_Env.debug env FStar_Options.Low
          in
       if uu____13655
       then
         let uu____13658 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1
           ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n"
           uu____13658
       else ());
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____13663 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_datacon uu____13681 ->
           failwith "add_sigelt_to_env: Impossible, bare data constructor"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           uu____13698) -> z3_reset_options env
       | FStar_Syntax_Syntax.Sig_pragma uu____13702 -> env
       | FStar_Syntax_Syntax.Sig_new_effect ne ->
           let env1 = FStar_TypeChecker_Env.push_sigelt env se  in
           FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
             (FStar_List.fold_left
                (fun env2  ->
                   fun a  ->
                     let uu____13712 =
                       FStar_Syntax_Util.action_as_lb
                         ne.FStar_Syntax_Syntax.mname a
                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                        in
                     FStar_TypeChecker_Env.push_sigelt env2 uu____13712) env1)
       | FStar_Syntax_Syntax.Sig_declare_typ
           (uu____13713,uu____13714,uu____13715) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_13720  ->
                   match uu___379_13720 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13723 -> false))
           -> env
       | FStar_Syntax_Syntax.Sig_let (uu____13725,uu____13726) when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_Util.for_some
                (fun uu___379_13735  ->
                   match uu___379_13735 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____13738 -> false))
           -> env
       | uu____13740 -> FStar_TypeChecker_Env.push_sigelt env se)
  
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____13809 se =
        match uu____13809 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____13862 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____13862
              then
                let uu____13865 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____13865
              else ());
             (let uu____13870 = tc_decl env1 se  in
              match uu____13870 with
              | (ses',ses_elaborated,env2) ->
                  let ses'1 =
                    FStar_All.pipe_right ses'
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____13923 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____13923
                             then
                               let uu____13927 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from %s\n" uu____13927
                             else ());
                            FStar_TypeChecker_Normalize.elim_uvars env2 se1))
                     in
                  let ses_elaborated1 =
                    FStar_All.pipe_right ses_elaborated
                      (FStar_List.map
                         (fun se1  ->
                            (let uu____13943 =
                               FStar_TypeChecker_Env.debug env2
                                 (FStar_Options.Other "UF")
                                in
                             if uu____13943
                             then
                               let uu____13947 =
                                 FStar_Syntax_Print.sigelt_to_string se1  in
                               FStar_Util.print1
                                 "About to elim vars from (elaborated) %s\\m"
                                 uu____13947
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
                    (let uu____13964 =
                       (FStar_Options.log_types ()) ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env3)
                            (FStar_Options.Other "LogTypes"))
                        in
                     if uu____13964
                     then
                       let uu____13969 =
                         FStar_List.fold_left
                           (fun s  ->
                              fun se1  ->
                                let uu____13978 =
                                  let uu____13980 =
                                    FStar_Syntax_Print.sigelt_to_string se1
                                     in
                                  Prims.strcat uu____13980 "\n"  in
                                Prims.strcat s uu____13978) "" ses'1
                          in
                       FStar_Util.print1 "Checked: %s\n" uu____13969
                     else ());
                    FStar_List.iter
                      (fun se1  ->
                         (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                           env3 se1) ses'1;
                    (let uu____13990 =
                       let uu____13999 =
                         FStar_Options.use_extracted_interfaces ()  in
                       if uu____13999
                       then ((FStar_List.rev_append ses'1 exports), [])
                       else
                         (let accum_exports_hidden uu____14041 se1 =
                            match uu____14041 with
                            | (exports1,hidden1) ->
                                let uu____14069 = for_export env3 hidden1 se1
                                   in
                                (match uu____14069 with
                                 | (se_exported,hidden2) ->
                                     ((FStar_List.rev_append se_exported
                                         exports1), hidden2))
                             in
                          FStar_List.fold_left accum_exports_hidden
                            (exports, hidden) ses'1)
                        in
                     match uu____13990 with
                     | (exports1,hidden1) ->
                         (((FStar_List.rev_append ses'1 ses1), exports1,
                            env3, hidden1), ses_elaborated1))))))
         in
      let process_one_decl_timed acc se =
        let uu____14223 = acc  in
        match uu____14223 with
        | (uu____14258,uu____14259,env1,uu____14261) ->
            let uu____14274 =
              FStar_Util.record_time
                (fun uu____14321  -> process_one_decl acc se)
               in
            (match uu____14274 with
             | (r,ms_elapsed) ->
                 ((let uu____14387 =
                     ((FStar_TypeChecker_Env.debug env1
                         (FStar_Options.Other "TCDeclTime"))
                        ||
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.attr_eq
                              FStar_Syntax_Util.tcdecltime_attr)
                           se.FStar_Syntax_Syntax.sigattrs))
                       || (FStar_Options.timing ())
                      in
                   if uu____14387
                   then
                     let uu____14391 =
                       FStar_Syntax_Print.sigelt_to_string_short se  in
                     let uu____14393 = FStar_Util.string_of_int ms_elapsed
                        in
                     FStar_Util.print2 "Checked %s in %s milliseconds\n"
                       uu____14391 uu____14393
                   else ());
                  r))
         in
      let uu____14398 =
        FStar_Util.fold_flatten process_one_decl_timed ([], [], env, []) ses
         in
      match uu____14398 with
      | (ses1,exports,env1,uu____14446) ->
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
          let uu___433_14484 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___433_14484.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___433_14484.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___433_14484.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___433_14484.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___433_14484.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___433_14484.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___433_14484.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___433_14484.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___433_14484.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___433_14484.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___433_14484.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___433_14484.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___433_14484.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___433_14484.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___433_14484.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___433_14484.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___433_14484.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___433_14484.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___433_14484.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___433_14484.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___433_14484.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___433_14484.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___433_14484.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___433_14484.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___433_14484.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___433_14484.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___433_14484.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___433_14484.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___433_14484.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___433_14484.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___433_14484.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___433_14484.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___433_14484.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.splice =
              (uu___433_14484.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.postprocess =
              (uu___433_14484.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.is_native_tactic =
              (uu___433_14484.FStar_TypeChecker_Env.is_native_tactic);
            FStar_TypeChecker_Env.identifier_info =
              (uu___433_14484.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___433_14484.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___433_14484.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___433_14484.FStar_TypeChecker_Env.nbe)
          }  in
        let check_term lid univs1 t =
          let uu____14504 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____14504 with
          | (univs2,t1) ->
              ((let uu____14512 =
                  let uu____14514 =
                    let uu____14520 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____14520  in
                  FStar_All.pipe_left uu____14514
                    (FStar_Options.Other "Exports")
                   in
                if uu____14512
                then
                  let uu____14524 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____14526 =
                    let uu____14528 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____14528
                      (FStar_String.concat ", ")
                     in
                  let uu____14545 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____14524 uu____14526 uu____14545
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____14551 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____14551 (fun a1  -> ())))
           in
        let check_term1 lid univs1 t =
          (let uu____14577 =
             let uu____14579 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____14581 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____14579 uu____14581
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____14577);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14592) ->
              let uu____14601 =
                let uu____14603 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14603  in
              if uu____14601
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____14617,uu____14618) ->
              let t =
                let uu____14630 =
                  let uu____14637 =
                    let uu____14638 =
                      let uu____14653 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____14653)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____14638  in
                  FStar_Syntax_Syntax.mk uu____14637  in
                uu____14630 FStar_Pervasives_Native.None
                  se.FStar_Syntax_Syntax.sigrng
                 in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____14672,uu____14673,uu____14674) ->
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t) ->
              let uu____14684 =
                let uu____14686 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14686  in
              if uu____14684 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____14694,lbs),uu____14696) ->
              let uu____14707 =
                let uu____14709 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14709  in
              if uu____14707
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
              let uu____14732 =
                let uu____14734 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____14734  in
              if uu____14732
              then
                let arrow1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    FStar_Pervasives_Native.None
                    se.FStar_Syntax_Syntax.sigrng
                   in
                check_term1 l univs1 arrow1
              else ()
          | FStar_Syntax_Syntax.Sig_main uu____14755 -> ()
          | FStar_Syntax_Syntax.Sig_assume uu____14756 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____14763 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____14764 -> ()
          | FStar_Syntax_Syntax.Sig_splice uu____14765 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____14772 -> ()  in
        let uu____14773 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____14773 then () else FStar_List.iter check_sigelt exports
  
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
             | FStar_Syntax_Syntax.Projector (l,uu____14879) -> true
             | uu____14881 -> false) quals
         in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____14911 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs',c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c))
                     FStar_Pervasives_Native.None r
               | uu____14950 ->
                   let uu____14951 =
                     let uu____14958 =
                       let uu____14959 =
                         let uu____14974 = FStar_Syntax_Syntax.mk_Total t  in
                         (bs, uu____14974)  in
                       FStar_Syntax_Syntax.Tm_arrow uu____14959  in
                     FStar_Syntax_Syntax.mk uu____14958  in
                   uu____14951 FStar_Pervasives_Native.None r)
           in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,uvs,bs,t,uu____14994,uu____14995) ->
            let s1 =
              let uu___434_15005 = s  in
              let uu____15006 =
                let uu____15007 =
                  let uu____15014 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng
                     in
                  (lid, uvs, uu____15014)  in
                FStar_Syntax_Syntax.Sig_declare_typ uu____15007  in
              let uu____15015 =
                let uu____15018 =
                  let uu____15021 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Syntax_Syntax.New :: uu____15021  in
                FStar_Syntax_Syntax.Assumption :: uu____15018  in
              {
                FStar_Syntax_Syntax.sigel = uu____15006;
                FStar_Syntax_Syntax.sigrng =
                  (uu___434_15005.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____15015;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___434_15005.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___434_15005.FStar_Syntax_Syntax.sigattrs)
              }  in
            [s1]
        | uu____15024 -> failwith "Impossible!"  in
      let val_of_lb s lid uu____15049 lbdef =
        match uu____15049 with
        | (uvs,t) ->
            let attrs =
              let uu____15060 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef  in
              if uu____15060
              then
                let uu____15065 =
                  let uu____15066 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None
                     in
                  FStar_All.pipe_right uu____15066
                    FStar_Syntax_Syntax.fv_to_tm
                   in
                uu____15065 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs  in
            let uu___435_15069 = s  in
            let uu____15070 =
              let uu____15073 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals
                 in
              FStar_Syntax_Syntax.Assumption :: uu____15073  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___435_15069.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____15070;
              FStar_Syntax_Syntax.sigmeta =
                (uu___435_15069.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs
            }
         in
      let should_keep_lbdef t =
        let comp_effect_name1 c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____15091 -> failwith "Impossible!"  in
        let c_opt =
          let uu____15098 = FStar_Syntax_Util.is_unit t  in
          if uu____15098
          then
            let uu____15105 = FStar_Syntax_Syntax.mk_Total t  in
            FStar_Pervasives_Native.Some uu____15105
          else
            (let uu____15112 =
               let uu____15113 = FStar_Syntax_Subst.compress t  in
               uu____15113.FStar_Syntax_Syntax.n  in
             match uu____15112 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____15120,c) ->
                 FStar_Pervasives_Native.Some c
             | uu____15144 -> FStar_Pervasives_Native.None)
           in
        match c_opt with
        | FStar_Pervasives_Native.None  -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____15156 = FStar_Syntax_Util.is_lemma_comp c  in
            if uu____15156
            then false
            else
              (let uu____15163 = FStar_Syntax_Util.is_pure_or_ghost_comp c
                  in
               if uu____15163
               then true
               else
                 (let uu____15170 = comp_effect_name1 c  in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____15170))
         in
      let extract_sigelt s =
        (let uu____15182 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme  in
         if uu____15182
         then
           let uu____15185 = FStar_Syntax_Print.sigelt_to_string s  in
           FStar_Util.print1 "Extracting interface for %s\n" uu____15185
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____15192 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____15212 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____15231 ->
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
                             (lid,uu____15277,uu____15278,uu____15279,uu____15280,uu____15281)
                             ->
                             ((let uu____15291 =
                                 let uu____15294 =
                                   FStar_ST.op_Bang abstract_inductive_tycons
                                    in
                                 lid :: uu____15294  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____15291);
                              (let uu____15387 =
                                 vals_of_abstract_inductive s1  in
                               FStar_List.append uu____15387 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid,uu____15391,uu____15392,uu____15393,uu____15394,uu____15395)
                             ->
                             ((let uu____15403 =
                                 let uu____15406 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons
                                    in
                                 lid :: uu____15406  in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____15403);
                              sigelts1)
                         | uu____15499 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t) ->
             let uu____15508 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15508
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____15518 =
                    let uu___436_15519 = s  in
                    let uu____15520 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___436_15519.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___436_15519.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15520;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___436_15519.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___436_15519.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15518])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs,lids) ->
             let uu____15531 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals
                in
             if uu____15531
             then []
             else
               (let uu____15538 = lbs  in
                match uu____15538 with
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
                        (fun uu____15600  ->
                           match uu____15600 with
                           | (uu____15608,t,uu____15610) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs
                       in
                    let vals =
                      FStar_List.map2
                        (fun lid  ->
                           fun uu____15627  ->
                             match uu____15627 with
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
                           (fun uu____15654  ->
                              match uu____15654 with
                              | (uu____15662,t,uu____15664) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs
                          in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_main t ->
             failwith
               "Did not anticipate main would arise when extracting interfaces!"
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____15676,uu____15677) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid
                in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____15685 = FStar_ST.op_Bang abstract_inductive_tycons
                    in
                 FStar_List.existsML
                   (fun l  ->
                      let uu____15736 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l
                         in
                      FStar_Ident.lid_equals lid uu____15736) uu____15685
                  in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____15740 =
                    let uu___437_15741 = s  in
                    let uu____15742 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___437_15741.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___437_15741.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____15742;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___437_15741.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___437_15741.FStar_Syntax_Syntax.sigattrs)
                    }  in
                  [uu____15740]
                else [])
             else
               (let uu____15749 =
                  let uu___438_15750 = s  in
                  let uu____15751 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___438_15750.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___438_15750.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____15751;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___438_15750.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___438_15750.FStar_Syntax_Syntax.sigattrs)
                  }  in
                [uu____15749])
         | FStar_Syntax_Syntax.Sig_new_effect uu____15754 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____15755 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15756 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____15769 -> [s])
         in
      let uu___439_15770 = m  in
      let uu____15771 =
        let uu____15772 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt)
           in
        FStar_All.pipe_right uu____15772 FStar_List.flatten  in
      {
        FStar_Syntax_Syntax.name = (uu___439_15770.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____15771;
        FStar_Syntax_Syntax.exports =
          (uu___439_15770.FStar_Syntax_Syntax.exports);
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
        (fun uu____15823  -> FStar_TypeChecker_Env.snapshot env msg)
  
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
          (fun uu____15871  ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth  in
             solver.FStar_TypeChecker_Env.refresh (); env)
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let uu____15887 = snapshot_context env msg  in
      FStar_Pervasives_Native.snd uu____15887
  
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
      (let uu____15976 = FStar_Options.debug_any ()  in
       if uu____15976
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
         let uu___440_15992 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___440_15992.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___440_15992.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___440_15992.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___440_15992.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___440_15992.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___440_15992.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___440_15992.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___440_15992.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___440_15992.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___440_15992.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___440_15992.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___440_15992.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___440_15992.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___440_15992.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___440_15992.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___440_15992.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___440_15992.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___440_15992.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___440_15992.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___440_15992.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___440_15992.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___440_15992.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___440_15992.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___440_15992.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___440_15992.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___440_15992.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___440_15992.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___440_15992.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___440_15992.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___440_15992.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___440_15992.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___440_15992.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___440_15992.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___440_15992.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___440_15992.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___440_15992.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___440_15992.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___440_15992.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___440_15992.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___440_15992.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___440_15992.FStar_TypeChecker_Env.nbe)
         }  in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name
          in
       let uu____15994 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
          in
       match uu____15994 with
       | (ses,exports,env3) ->
           ((let uu___441_16027 = modul  in
             {
               FStar_Syntax_Syntax.name =
                 (uu___441_16027.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___441_16027.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___441_16027.FStar_Syntax_Syntax.is_interface)
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
        let uu____16056 = tc_decls env decls  in
        match uu____16056 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___442_16087 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___442_16087.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___442_16087.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___442_16087.FStar_Syntax_Syntax.is_interface)
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
        let uu____16148 = tc_partial_modul env01 m  in
        match uu____16148 with
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
                (let uu____16185 = FStar_Errors.get_err_count ()  in
                 uu____16185 = (Prims.parse_int "0"))
               in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m  in
              ((let uu____16196 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low
                   in
                if uu____16196
                then
                  let uu____16200 =
                    let uu____16202 =
                      FStar_Options.should_verify
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16202 then "" else " (in lax mode) "  in
                  let uu____16210 =
                    let uu____16212 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16212
                    then
                      let uu____16216 =
                        let uu____16218 =
                          FStar_Syntax_Print.modul_to_string m  in
                        Prims.strcat uu____16218 "\n"  in
                      Prims.strcat "\nfrom: " uu____16216
                    else ""  in
                  let uu____16225 =
                    let uu____16227 =
                      FStar_Options.dump_module
                        (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    if uu____16227
                    then
                      let uu____16231 =
                        let uu____16233 =
                          FStar_Syntax_Print.modul_to_string modul_iface  in
                        Prims.strcat uu____16233 "\n"  in
                      Prims.strcat "\nto: " uu____16231
                    else ""  in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    (m.FStar_Syntax_Syntax.name).FStar_Ident.str uu____16200
                    uu____16210 uu____16225
                else ());
               (let en0 =
                  let en0 =
                    pop_context en
                      (Prims.strcat "Ending modul "
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     in
                  let en01 =
                    let uu___443_16247 = en0  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___443_16247.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___443_16247.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___443_16247.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___443_16247.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___443_16247.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___443_16247.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___443_16247.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___443_16247.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___443_16247.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___443_16247.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___443_16247.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___443_16247.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___443_16247.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___443_16247.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___443_16247.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___443_16247.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___443_16247.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___443_16247.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___443_16247.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___443_16247.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___443_16247.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___443_16247.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___443_16247.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___443_16247.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___443_16247.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___443_16247.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___443_16247.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___443_16247.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___443_16247.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___443_16247.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___443_16247.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___443_16247.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___443_16247.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___443_16247.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___443_16247.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___443_16247.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___443_16247.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___443_16247.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___443_16247.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___443_16247.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___443_16247.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___443_16247.FStar_TypeChecker_Env.nbe)
                    }  in
                  let en02 =
                    let uu___444_16249 = en01  in
                    let uu____16250 =
                      let uu____16265 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst
                         in
                      (uu____16265, FStar_Pervasives_Native.None)  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___444_16249.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___444_16249.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___444_16249.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___444_16249.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___444_16249.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___444_16249.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___444_16249.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___444_16249.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___444_16249.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___444_16249.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.is_pattern =
                        (uu___444_16249.FStar_TypeChecker_Env.is_pattern);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___444_16249.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___444_16249.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___444_16249.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___444_16249.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___444_16249.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___444_16249.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___444_16249.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___444_16249.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___444_16249.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___444_16249.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___444_16249.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___444_16249.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___444_16249.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___444_16249.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___444_16249.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___444_16249.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___444_16249.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___444_16249.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___444_16249.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___444_16249.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____16250;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___444_16249.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___444_16249.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___444_16249.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___444_16249.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___444_16249.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___444_16249.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___444_16249.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___444_16249.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___444_16249.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___444_16249.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___444_16249.FStar_TypeChecker_Env.nbe)
                    }  in
                  let uu____16311 =
                    let uu____16313 = FStar_Options.interactive ()  in
                    Prims.op_Negation uu____16313  in
                  if uu____16311
                  then
                    ((let uu____16317 =
                        FStar_Options.restore_cmd_line_options true  in
                      FStar_All.pipe_right uu____16317 (fun a2  -> ()));
                     z3_reset_options en02)
                  else en02  in
                let uu____16321 = tc_modul en0 modul_iface true  in
                match uu____16321 with
                | (modul_iface1,env) ->
                    ((let uu___445_16334 = m  in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___445_16334.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___445_16334.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___445_16334.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___446_16338 = m  in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___446_16338.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___446_16338.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___446_16338.FStar_Syntax_Syntax.is_interface)
                 }  in
               let env = FStar_TypeChecker_Env.finish_module en modul  in
               (let uu____16341 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst
                   in
                FStar_All.pipe_right uu____16341 FStar_Util.smap_clear);
               (let uu____16377 =
                  ((let uu____16381 = FStar_Options.lax ()  in
                    Prims.op_Negation uu____16381) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____16384 =
                       FStar_Options.use_extracted_interfaces ()  in
                     Prims.op_Negation uu____16384)
                   in
                if uu____16377 then check_exports env modul exports else ());
               (let uu____16390 =
                  pop_context env
                    (Prims.strcat "Ending modul "
                       (modul.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   in
                FStar_All.pipe_right uu____16390 (fun a3  -> ()));
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
                 env modul;
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ();
               (let uu____16395 =
                  let uu____16397 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____16397  in
                if uu____16395
                then
                  let uu____16400 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____16400 (fun a4  -> ())
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
        let uu____16417 =
          let uu____16419 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
          Prims.strcat "Internals for " uu____16419  in
        push_context env uu____16417  in
      let env2 =
        FStar_List.fold_left
          (fun env2  ->
             fun se  ->
               let env3 = FStar_TypeChecker_Env.push_sigelt env2 se  in
               let lids = FStar_Syntax_Util.lids_of_sigelt se  in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid  ->
                       let uu____16440 =
                         FStar_TypeChecker_Env.try_lookup_lid env3 lid  in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations
         in
      let uu____16451 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports
         in
      match uu____16451 with | (uu____16458,env3) -> env3
  
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env  ->
    fun m  ->
      fun b  ->
        (let uu____16483 = FStar_Options.debug_any ()  in
         if uu____16483
         then
           let uu____16486 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____16486
         else ());
        (let uu____16498 =
           FStar_Options.dump_module
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         if uu____16498
         then
           let uu____16501 = FStar_Syntax_Print.modul_to_string m  in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____16501
         else ());
        (let env1 =
           let uu___447_16507 = env  in
           let uu____16508 =
             let uu____16510 =
               FStar_Options.should_verify
                 (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             Prims.op_Negation uu____16510  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___447_16507.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___447_16507.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___447_16507.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___447_16507.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___447_16507.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___447_16507.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___447_16507.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___447_16507.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___447_16507.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___447_16507.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___447_16507.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___447_16507.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___447_16507.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___447_16507.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___447_16507.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___447_16507.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___447_16507.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___447_16507.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___447_16507.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___447_16507.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____16508;
             FStar_TypeChecker_Env.lax_universes =
               (uu___447_16507.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___447_16507.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___447_16507.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___447_16507.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___447_16507.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___447_16507.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___447_16507.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___447_16507.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___447_16507.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___447_16507.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___447_16507.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___447_16507.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___447_16507.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___447_16507.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___447_16507.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___447_16507.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___447_16507.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___447_16507.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___447_16507.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___447_16507.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___447_16507.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___447_16507.FStar_TypeChecker_Env.nbe)
           }  in
         let uu____16512 = tc_modul env1 m b  in
         match uu____16512 with
         | (m1,env2) ->
             ((let uu____16524 =
                 FStar_Options.dump_module
                   (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____16524
               then
                 let uu____16527 = FStar_Syntax_Print.modul_to_string m1  in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____16527
               else ());
              (let uu____16533 =
                 (FStar_Options.dump_module
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                   &&
                   (FStar_Options.debug_at_level
                      (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                      (FStar_Options.Other "Normalize"))
                  in
               if uu____16533
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
                         let uu____16571 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         match uu____16571 with
                         | (univnames1,e) ->
                             let uu___448_16578 = lb  in
                             let uu____16579 =
                               let uu____16582 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames1
                                  in
                               n1 uu____16582 e  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___448_16578.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___448_16578.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___448_16578.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___448_16578.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16579;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___448_16578.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___448_16578.FStar_Syntax_Syntax.lbpos)
                             }
                          in
                       let uu___449_16583 = se  in
                       let uu____16584 =
                         let uu____16585 =
                           let uu____16592 =
                             let uu____16593 = FStar_List.map update lbs  in
                             (b1, uu____16593)  in
                           (uu____16592, ids)  in
                         FStar_Syntax_Syntax.Sig_let uu____16585  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____16584;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___449_16583.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___449_16583.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___449_16583.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___449_16583.FStar_Syntax_Syntax.sigattrs)
                       }
                   | uu____16601 -> se  in
                 let normalized_module =
                   let uu___450_16603 = m1  in
                   let uu____16604 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations
                      in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___450_16603.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____16604;
                     FStar_Syntax_Syntax.exports =
                       (uu___450_16603.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___450_16603.FStar_Syntax_Syntax.is_interface)
                   }  in
                 let uu____16605 =
                   FStar_Syntax_Print.modul_to_string normalized_module  in
                 FStar_Util.print1 "%s\n" uu____16605
               else ());
              (m1, env2)))
  
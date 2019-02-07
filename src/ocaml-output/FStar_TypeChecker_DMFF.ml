open Prims
type env =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }
let (__proj__Mkenv__item__tcenv : env -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with | { tcenv; subst = subst1; tc_const;_} -> tcenv
  
let (__proj__Mkenv__item__subst :
  env -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun projectee  ->
    match projectee with | { tcenv; subst = subst1; tc_const;_} -> subst1
  
let (__proj__Mkenv__item__tc_const :
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with | { tcenv; subst = subst1; tc_const;_} -> tc_const
  
let (empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env)
  = fun env  -> fun tc_const  -> { tcenv = env; subst = []; tc_const } 
let (gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl))
  =
  fun env  ->
    fun binders  ->
      fun a  ->
        fun wp_a  ->
          fun ed  ->
            let wp_a1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.EraseUniverses] env wp_a
               in
            let a1 =
              let uu___363_127 = a  in
              let uu____128 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___363_127.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___363_127.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____128
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____141 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____141
             then
               (d "Elaborating extra WP combinators";
                (let uu____147 = FStar_Syntax_Print.term_to_string wp_a1  in
                 FStar_Util.print1 "wp_a is: %s\n" uu____147))
             else ());
            (let rec collect_binders t =
               let uu____166 =
                 let uu____167 =
                   let uu____170 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____170
                    in
                 uu____167.FStar_Syntax_Syntax.n  in
               match uu____166 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____205) -> t1
                     | FStar_Syntax_Syntax.GTotal (t1,uu____215) -> t1
                     | uu____224 ->
                         let uu____225 =
                           let uu____227 =
                             FStar_Syntax_Print.comp_to_string comp  in
                           Prims.strcat "wp_a contains non-Tot arrow: "
                             uu____227
                            in
                         failwith uu____225
                      in
                   let uu____230 = collect_binders rest  in
                   FStar_List.append bs uu____230
               | FStar_Syntax_Syntax.Tm_type uu____245 -> []
               | uu____252 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____279 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____279 FStar_Syntax_Util.name_binders
                in
             (let uu____305 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____305
              then
                let uu____309 =
                  let uu____311 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____311  in
                d uu____309
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____349 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____349 with
                | (sigelt,fv) ->
                    ((let uu____357 =
                        let uu____360 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____360
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____357);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____484  ->
                     match uu____484 with
                     | (t,b) ->
                         let uu____498 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____498))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____537 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____537))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____571 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____571)
                 in
              let uu____574 =
                let uu____591 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____616 =
                        let uu____619 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____619  in
                      FStar_Syntax_Util.arrow gamma uu____616  in
                    let uu____620 =
                      let uu____621 =
                        let uu____630 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____637 =
                          let uu____646 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____646]  in
                        uu____630 :: uu____637  in
                      FStar_List.append binders uu____621  in
                    FStar_Syntax_Util.abs uu____620 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____677 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____678 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____677, uu____678)  in
                match uu____591 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____720 =
                        let uu____721 =
                          let uu____738 =
                            let uu____749 =
                              FStar_List.map
                                (fun uu____771  ->
                                   match uu____771 with
                                   | (bv,uu____783) ->
                                       let uu____788 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____789 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____788, uu____789)) binders
                               in
                            let uu____791 =
                              let uu____798 =
                                let uu____803 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____804 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____803, uu____804)  in
                              let uu____806 =
                                let uu____813 =
                                  let uu____818 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____818)  in
                                [uu____813]  in
                              uu____798 :: uu____806  in
                            FStar_List.append uu____749 uu____791  in
                          (fv, uu____738)  in
                        FStar_Syntax_Syntax.Tm_app uu____721  in
                      mk1 uu____720  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____574 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____891 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____891
                       in
                    let ret1 =
                      let uu____896 =
                        let uu____897 =
                          let uu____900 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____900  in
                        FStar_Syntax_Util.residual_tot uu____897  in
                      FStar_Pervasives_Native.Some uu____896  in
                    let body =
                      let uu____904 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____904 ret1  in
                    let uu____907 =
                      let uu____908 = mk_all_implicit binders  in
                      let uu____915 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____908 uu____915  in
                    FStar_Syntax_Util.abs uu____907 body ret1  in
                  let c_pure1 =
                    let uu____953 = mk_lid "pure"  in
                    register env1 uu____953 c_pure  in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let l =
                      let uu____963 =
                        let uu____964 =
                          let uu____965 =
                            let uu____974 =
                              let uu____981 =
                                let uu____982 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____982
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____981  in
                            [uu____974]  in
                          let uu____995 =
                            let uu____998 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____998  in
                          FStar_Syntax_Util.arrow uu____965 uu____995  in
                        mk_gctx uu____964  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____963
                       in
                    let r =
                      let uu____1001 =
                        let uu____1002 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1002  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____1001
                       in
                    let ret1 =
                      let uu____1007 =
                        let uu____1008 =
                          let uu____1011 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1011  in
                        FStar_Syntax_Util.residual_tot uu____1008  in
                      FStar_Pervasives_Native.Some uu____1007  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____1021 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____1024 =
                          let uu____1035 =
                            let uu____1038 =
                              let uu____1039 =
                                let uu____1040 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____1040
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____1039  in
                            [uu____1038]  in
                          FStar_List.append gamma_as_args uu____1035  in
                        FStar_Syntax_Util.mk_app uu____1021 uu____1024  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____1043 =
                      let uu____1044 = mk_all_implicit binders  in
                      let uu____1051 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____1044 uu____1051  in
                    FStar_Syntax_Util.abs uu____1043 outer_body ret1  in
                  let c_app1 =
                    let uu____1103 = mk_lid "app"  in
                    register env1 uu____1103 c_app  in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1115 =
                        let uu____1124 =
                          let uu____1131 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1131  in
                        [uu____1124]  in
                      let uu____1144 =
                        let uu____1147 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1147  in
                      FStar_Syntax_Util.arrow uu____1115 uu____1144  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1151 =
                        let uu____1152 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1152  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1151
                       in
                    let ret1 =
                      let uu____1157 =
                        let uu____1158 =
                          let uu____1161 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1161  in
                        FStar_Syntax_Util.residual_tot uu____1158  in
                      FStar_Pervasives_Native.Some uu____1157  in
                    let uu____1162 =
                      let uu____1163 = mk_all_implicit binders  in
                      let uu____1170 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____1163 uu____1170  in
                    let uu____1221 =
                      let uu____1224 =
                        let uu____1235 =
                          let uu____1238 =
                            let uu____1239 =
                              let uu____1250 =
                                let uu____1253 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1253]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1250
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1239  in
                          let uu____1262 =
                            let uu____1265 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1265]  in
                          uu____1238 :: uu____1262  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1235
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1224  in
                    FStar_Syntax_Util.abs uu____1162 uu____1221 ret1  in
                  let c_lift11 =
                    let uu____1275 = mk_lid "lift1"  in
                    register env1 uu____1275 c_lift1  in
                  let c_lift2 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t3 =
                      FStar_Syntax_Syntax.gen_bv "t3"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1289 =
                        let uu____1298 =
                          let uu____1305 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1305  in
                        let uu____1306 =
                          let uu____1315 =
                            let uu____1322 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1322  in
                          [uu____1315]  in
                        uu____1298 :: uu____1306  in
                      let uu____1341 =
                        let uu____1344 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1344  in
                      FStar_Syntax_Util.arrow uu____1289 uu____1341  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1348 =
                        let uu____1349 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1349  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1348
                       in
                    let a2 =
                      let uu____1352 =
                        let uu____1353 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1353  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1352
                       in
                    let ret1 =
                      let uu____1358 =
                        let uu____1359 =
                          let uu____1362 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1362  in
                        FStar_Syntax_Util.residual_tot uu____1359  in
                      FStar_Pervasives_Native.Some uu____1358  in
                    let uu____1363 =
                      let uu____1364 = mk_all_implicit binders  in
                      let uu____1371 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1364 uu____1371  in
                    let uu____1436 =
                      let uu____1439 =
                        let uu____1450 =
                          let uu____1453 =
                            let uu____1454 =
                              let uu____1465 =
                                let uu____1468 =
                                  let uu____1469 =
                                    let uu____1480 =
                                      let uu____1483 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1483]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1480
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1469
                                   in
                                let uu____1492 =
                                  let uu____1495 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1495]  in
                                uu____1468 :: uu____1492  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1465
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1454  in
                          let uu____1504 =
                            let uu____1507 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1507]  in
                          uu____1453 :: uu____1504  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1450
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1439  in
                    FStar_Syntax_Util.abs uu____1363 uu____1436 ret1  in
                  let c_lift21 =
                    let uu____1517 = mk_lid "lift2"  in
                    register env1 uu____1517 c_lift2  in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1529 =
                        let uu____1538 =
                          let uu____1545 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1545  in
                        [uu____1538]  in
                      let uu____1558 =
                        let uu____1561 =
                          let uu____1562 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1562  in
                        FStar_Syntax_Syntax.mk_Total uu____1561  in
                      FStar_Syntax_Util.arrow uu____1529 uu____1558  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1568 =
                        let uu____1569 =
                          let uu____1572 =
                            let uu____1573 =
                              let uu____1582 =
                                let uu____1589 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1589
                                 in
                              [uu____1582]  in
                            let uu____1602 =
                              let uu____1605 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1605  in
                            FStar_Syntax_Util.arrow uu____1573 uu____1602  in
                          mk_ctx uu____1572  in
                        FStar_Syntax_Util.residual_tot uu____1569  in
                      FStar_Pervasives_Native.Some uu____1568  in
                    let e1 =
                      let uu____1607 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1607
                       in
                    let body =
                      let uu____1612 =
                        let uu____1613 =
                          let uu____1622 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1622]  in
                        FStar_List.append gamma uu____1613  in
                      let uu____1647 =
                        let uu____1650 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1653 =
                          let uu____1664 =
                            let uu____1665 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1665  in
                          let uu____1666 = args_of_binders1 gamma  in
                          uu____1664 :: uu____1666  in
                        FStar_Syntax_Util.mk_app uu____1650 uu____1653  in
                      FStar_Syntax_Util.abs uu____1612 uu____1647 ret1  in
                    let uu____1669 =
                      let uu____1670 = mk_all_implicit binders  in
                      let uu____1677 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1670 uu____1677  in
                    FStar_Syntax_Util.abs uu____1669 body ret1  in
                  let c_push1 =
                    let uu____1722 = mk_lid "push"  in
                    register env1 uu____1722 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1749 =
                        let uu____1750 =
                          let uu____1767 = args_of_binders1 binders  in
                          (c, uu____1767)  in
                        FStar_Syntax_Syntax.Tm_app uu____1750  in
                      mk1 uu____1749
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1796 =
                        let uu____1797 =
                          let uu____1806 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1813 =
                            let uu____1822 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1822]  in
                          uu____1806 :: uu____1813  in
                        let uu____1847 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1797 uu____1847  in
                      FStar_Syntax_Syntax.mk_Total uu____1796  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1852 =
                      let uu____1853 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1853  in
                    let uu____1868 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1873 =
                        let uu____1876 =
                          let uu____1887 =
                            let uu____1890 =
                              let uu____1891 =
                                let uu____1902 =
                                  let uu____1911 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1911  in
                                [uu____1902]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1891  in
                            [uu____1890]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1887
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1876  in
                      FStar_Syntax_Util.ascribe uu____1873
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1852 uu____1868
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1955 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1955 wp_if_then_else  in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1  in
                  let wp_assert =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let l_and =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.and_lid
                        (FStar_Syntax_Syntax.Delta_constant_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____1972 =
                        let uu____1983 =
                          let uu____1986 =
                            let uu____1987 =
                              let uu____1998 =
                                let uu____2001 =
                                  let uu____2002 =
                                    let uu____2013 =
                                      let uu____2022 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____2022
                                       in
                                    [uu____2013]  in
                                  FStar_Syntax_Util.mk_app l_and uu____2002
                                   in
                                [uu____2001]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1998
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1987  in
                          let uu____2047 =
                            let uu____2050 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____2050]  in
                          uu____1986 :: uu____2047  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1983
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1972  in
                    let uu____2059 =
                      let uu____2060 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____2060  in
                    FStar_Syntax_Util.abs uu____2059 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____2076 = mk_lid "wp_assert"  in
                    register env1 uu____2076 wp_assert  in
                  let wp_assert2 = mk_generic_app wp_assert1  in
                  let wp_assume =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let l_imp =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
                        (FStar_Syntax_Syntax.Delta_constant_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____2093 =
                        let uu____2104 =
                          let uu____2107 =
                            let uu____2108 =
                              let uu____2119 =
                                let uu____2122 =
                                  let uu____2123 =
                                    let uu____2134 =
                                      let uu____2143 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____2143
                                       in
                                    [uu____2134]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____2123
                                   in
                                [uu____2122]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____2119
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2108  in
                          let uu____2168 =
                            let uu____2171 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____2171]  in
                          uu____2107 :: uu____2168  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2104
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2093  in
                    let uu____2180 =
                      let uu____2181 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____2181  in
                    FStar_Syntax_Util.abs uu____2180 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____2197 = mk_lid "wp_assume"  in
                    register env1 uu____2197 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____2210 =
                        let uu____2219 =
                          let uu____2226 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____2226  in
                        [uu____2219]  in
                      let uu____2239 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____2210 uu____2239  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____2247 =
                        let uu____2258 =
                          let uu____2261 =
                            let uu____2262 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2262  in
                          let uu____2281 =
                            let uu____2284 =
                              let uu____2285 =
                                let uu____2296 =
                                  let uu____2299 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____2299]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____2296
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____2285  in
                            [uu____2284]  in
                          uu____2261 :: uu____2281  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2258
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2247  in
                    let uu____2316 =
                      let uu____2317 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____2317  in
                    FStar_Syntax_Util.abs uu____2316 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____2333 = mk_lid "wp_close"  in
                    register env1 uu____2333 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____2344 =
                      let uu____2345 =
                        let uu____2346 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____2346
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____2345  in
                    FStar_Pervasives_Native.Some uu____2344  in
                  let mk_forall1 x body =
                    let uu____2358 =
                      let uu____2365 =
                        let uu____2366 =
                          let uu____2383 =
                            let uu____2394 =
                              let uu____2403 =
                                let uu____2404 =
                                  let uu____2405 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____2405]  in
                                FStar_Syntax_Util.abs uu____2404 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____2403  in
                            [uu____2394]  in
                          (FStar_Syntax_Util.tforall, uu____2383)  in
                        FStar_Syntax_Syntax.Tm_app uu____2366  in
                      FStar_Syntax_Syntax.mk uu____2365  in
                    uu____2358 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2466 =
                      let uu____2467 = FStar_Syntax_Subst.compress t  in
                      uu____2467.FStar_Syntax_Syntax.n  in
                    match uu____2466 with
                    | FStar_Syntax_Syntax.Tm_type uu____2471 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2504  ->
                              match uu____2504 with
                              | (b,uu____2513) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2518 -> true  in
                  let rec is_monotonic t =
                    let uu____2531 =
                      let uu____2532 = FStar_Syntax_Subst.compress t  in
                      uu____2532.FStar_Syntax_Syntax.n  in
                    match uu____2531 with
                    | FStar_Syntax_Syntax.Tm_type uu____2536 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2569  ->
                              match uu____2569 with
                              | (b,uu____2578) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2583 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____2657 =
                      let uu____2658 = FStar_Syntax_Subst.compress t1  in
                      uu____2658.FStar_Syntax_Syntax.n  in
                    match uu____2657 with
                    | FStar_Syntax_Syntax.Tm_type uu____2663 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2666);
                                      FStar_Syntax_Syntax.pos = uu____2667;
                                      FStar_Syntax_Syntax.vars = uu____2668;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2712 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2712
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2722 =
                              let uu____2725 =
                                let uu____2736 =
                                  let uu____2745 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2745  in
                                [uu____2736]  in
                              FStar_Syntax_Util.mk_app x uu____2725  in
                            let uu____2762 =
                              let uu____2765 =
                                let uu____2776 =
                                  let uu____2785 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2785  in
                                [uu____2776]  in
                              FStar_Syntax_Util.mk_app y uu____2765  in
                            mk_rel1 b uu____2722 uu____2762  in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2
                              in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2
                              in
                           let body =
                             let uu____2809 =
                               let uu____2812 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2815 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2812 uu____2815  in
                             let uu____2818 =
                               let uu____2821 =
                                 let uu____2824 =
                                   let uu____2835 =
                                     let uu____2844 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2844
                                      in
                                   [uu____2835]  in
                                 FStar_Syntax_Util.mk_app x uu____2824  in
                               let uu____2861 =
                                 let uu____2864 =
                                   let uu____2875 =
                                     let uu____2884 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2884
                                      in
                                   [uu____2875]  in
                                 FStar_Syntax_Util.mk_app y uu____2864  in
                               mk_rel1 b uu____2821 uu____2861  in
                             FStar_Syntax_Util.mk_imp uu____2809 uu____2818
                              in
                           let uu____2901 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2901)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2904);
                                      FStar_Syntax_Syntax.pos = uu____2905;
                                      FStar_Syntax_Syntax.vars = uu____2906;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2950 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2950
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2960 =
                              let uu____2963 =
                                let uu____2974 =
                                  let uu____2983 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2983  in
                                [uu____2974]  in
                              FStar_Syntax_Util.mk_app x uu____2963  in
                            let uu____3000 =
                              let uu____3003 =
                                let uu____3014 =
                                  let uu____3023 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____3023  in
                                [uu____3014]  in
                              FStar_Syntax_Util.mk_app y uu____3003  in
                            mk_rel1 b uu____2960 uu____3000  in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2
                              in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2
                              in
                           let body =
                             let uu____3047 =
                               let uu____3050 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____3053 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____3050 uu____3053  in
                             let uu____3056 =
                               let uu____3059 =
                                 let uu____3062 =
                                   let uu____3073 =
                                     let uu____3082 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____3082
                                      in
                                   [uu____3073]  in
                                 FStar_Syntax_Util.mk_app x uu____3062  in
                               let uu____3099 =
                                 let uu____3102 =
                                   let uu____3113 =
                                     let uu____3122 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____3122
                                      in
                                   [uu____3113]  in
                                 FStar_Syntax_Util.mk_app y uu____3102  in
                               mk_rel1 b uu____3059 uu____3099  in
                             FStar_Syntax_Util.mk_imp uu____3047 uu____3056
                              in
                           let uu____3139 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____3139)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___364_3178 = t1  in
                          let uu____3179 =
                            let uu____3180 =
                              let uu____3195 =
                                let uu____3198 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____3198  in
                              ([binder], uu____3195)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____3180  in
                          {
                            FStar_Syntax_Syntax.n = uu____3179;
                            FStar_Syntax_Syntax.pos =
                              (uu___364_3178.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___364_3178.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____3221 ->
                        failwith "unhandled arrow"
                    | uu____3239 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
                  let stronger =
                    let wp1 =
                      FStar_Syntax_Syntax.gen_bv "wp1"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let wp2 =
                      FStar_Syntax_Syntax.gen_bv "wp2"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let rec mk_stronger t x y =
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.UnfoldUntil
                            FStar_Syntax_Syntax.delta_constant] env1 t
                         in
                      let uu____3276 =
                        let uu____3277 = FStar_Syntax_Subst.compress t1  in
                        uu____3277.FStar_Syntax_Syntax.n  in
                      match uu____3276 with
                      | FStar_Syntax_Syntax.Tm_type uu____3280 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____3307 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____3307
                          ->
                          let project i tuple =
                            let projector =
                              let uu____3328 =
                                let uu____3329 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____3329 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____3328
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____3359 =
                            let uu____3370 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____3388  ->
                                     match uu____3388 with
                                     | (t2,q) ->
                                         let uu____3408 = project i x  in
                                         let uu____3411 = project i y  in
                                         mk_stronger t2 uu____3408 uu____3411)
                                args
                               in
                            match uu____3370 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____3359 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____3465);
                                      FStar_Syntax_Syntax.pos = uu____3466;
                                      FStar_Syntax_Syntax.vars = uu____3467;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3511  ->
                                   match uu____3511 with
                                   | (bv,q) ->
                                       let uu____3525 =
                                         let uu____3527 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____3527  in
                                       FStar_Syntax_Syntax.gen_bv uu____3525
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3536 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3536) bvs
                             in
                          let body =
                            let uu____3538 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3541 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3538 uu____3541  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____3550);
                                      FStar_Syntax_Syntax.pos = uu____3551;
                                      FStar_Syntax_Syntax.vars = uu____3552;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3596  ->
                                   match uu____3596 with
                                   | (bv,q) ->
                                       let uu____3610 =
                                         let uu____3612 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____3612  in
                                       FStar_Syntax_Syntax.gen_bv uu____3610
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3621 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3621) bvs
                             in
                          let body =
                            let uu____3623 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3626 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3623 uu____3626  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____3633 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____3636 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____3639 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3642 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____3636 uu____3639 uu____3642  in
                    let uu____3645 =
                      let uu____3646 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3646  in
                    FStar_Syntax_Util.abs uu____3645 body ret_tot_type  in
                  let stronger1 =
                    let uu____3688 = mk_lid "stronger"  in
                    register env1 uu____3688 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3696 = FStar_Util.prefix gamma  in
                    match uu____3696 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3762 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3762
                             in
                          let uu____3767 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3767 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3777 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3777  in
                              let guard_free1 =
                                let uu____3789 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3789  in
                              let pat =
                                let uu____3793 =
                                  let uu____3804 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3804]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3793
                                 in
                              let pattern_guarded_body =
                                let uu____3832 =
                                  let uu____3833 =
                                    let uu____3840 =
                                      let uu____3841 =
                                        let uu____3854 =
                                          let uu____3865 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____3865]  in
                                        [uu____3854]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3841
                                       in
                                    (body, uu____3840)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3833  in
                                mk1 uu____3832  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3912 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3921 =
                            let uu____3924 =
                              let uu____3925 =
                                let uu____3928 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3931 =
                                  let uu____3942 = args_of_binders1 wp_args
                                     in
                                  let uu____3945 =
                                    let uu____3948 =
                                      let uu____3949 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3949
                                       in
                                    [uu____3948]  in
                                  FStar_List.append uu____3942 uu____3945  in
                                FStar_Syntax_Util.mk_app uu____3928
                                  uu____3931
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____3925  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3924
                             in
                          FStar_Syntax_Util.abs gamma uu____3921
                            ret_gtot_type
                           in
                        let uu____3950 =
                          let uu____3951 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3951  in
                        FStar_Syntax_Util.abs uu____3950 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____3967 = mk_lid "ite_wp"  in
                    register env1 uu____3967 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3975 = FStar_Util.prefix gamma  in
                    match uu____3975 with
                    | (wp_args,post) ->
                        let uu____4030 =
                          FStar_Syntax_Util.arrow_formals_comp
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        (match uu____4030 with
                         | (bs,uu____4046) ->
                             let bs1 =
                               FStar_List.map
                                 FStar_Syntax_Syntax.freshen_binder bs
                                in
                             let args =
                               FStar_List.map
                                 (fun uu____4109  ->
                                    match uu____4109 with
                                    | (bv,q) ->
                                        let uu____4128 =
                                          FStar_Syntax_Syntax.bv_to_name bv
                                           in
                                        (uu____4128, q)) bs1
                                in
                             let body =
                               let uu____4132 =
                                 let uu____4133 =
                                   FStar_All.pipe_left
                                     FStar_Syntax_Syntax.bv_to_name
                                     (FStar_Pervasives_Native.fst post)
                                    in
                                 FStar_Syntax_Util.mk_app uu____4133 args  in
                               FStar_Syntax_Util.close_forall_no_univs bs1
                                 uu____4132
                                in
                             let uu____4140 =
                               let uu____4141 =
                                 let uu____4150 =
                                   FStar_Syntax_Syntax.binders_of_list [a1]
                                    in
                                 FStar_List.append uu____4150 gamma  in
                               FStar_List.append binders uu____4141  in
                             FStar_Syntax_Util.abs uu____4140 body
                               ret_gtot_type)
                     in
                  let null_wp1 =
                    let uu____4172 = mk_lid "null_wp"  in
                    register env1 uu____4172 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____4185 =
                        let uu____4196 =
                          let uu____4199 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____4200 =
                            let uu____4203 =
                              let uu____4204 =
                                let uu____4215 =
                                  let uu____4224 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____4224  in
                                [uu____4215]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____4204
                               in
                            let uu____4241 =
                              let uu____4244 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____4244]  in
                            uu____4203 :: uu____4241  in
                          uu____4199 :: uu____4200  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____4196
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____4185  in
                    let uu____4253 =
                      let uu____4254 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____4254  in
                    FStar_Syntax_Util.abs uu____4253 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____4270 = mk_lid "wp_trivial"  in
                    register env1 uu____4270 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____4276 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____4276
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____4288 =
                      let uu____4289 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____4289  in
                    let uu____4337 =
                      let uu___365_4338 = ed  in
                      let uu____4339 =
                        let uu____4340 = c wp_if_then_else2  in
                        ([], uu____4340)  in
                      let uu____4347 =
                        let uu____4348 = c ite_wp2  in ([], uu____4348)  in
                      let uu____4355 =
                        let uu____4356 = c stronger2  in ([], uu____4356)  in
                      let uu____4363 =
                        let uu____4364 = c wp_close2  in ([], uu____4364)  in
                      let uu____4371 =
                        let uu____4372 = c wp_assert2  in ([], uu____4372)
                         in
                      let uu____4379 =
                        let uu____4380 = c wp_assume2  in ([], uu____4380)
                         in
                      let uu____4387 =
                        let uu____4388 = c null_wp2  in ([], uu____4388)  in
                      let uu____4395 =
                        let uu____4396 = c wp_trivial2  in ([], uu____4396)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___365_4338.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___365_4338.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___365_4338.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___365_4338.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.spec =
                          (uu___365_4338.FStar_Syntax_Syntax.spec);
                        FStar_Syntax_Syntax.signature =
                          (uu___365_4338.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.if_then_else = uu____4339;
                        FStar_Syntax_Syntax.ite_wp = uu____4347;
                        FStar_Syntax_Syntax.stronger = uu____4355;
                        FStar_Syntax_Syntax.close_wp = uu____4363;
                        FStar_Syntax_Syntax.assert_p = uu____4371;
                        FStar_Syntax_Syntax.assume_p = uu____4379;
                        FStar_Syntax_Syntax.null_wp = uu____4387;
                        FStar_Syntax_Syntax.trivial = uu____4395;
                        FStar_Syntax_Syntax.repr =
                          (uu___365_4338.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.elaborated =
                          (uu___365_4338.FStar_Syntax_Syntax.elaborated);
                        FStar_Syntax_Syntax.spec_dm4f =
                          (uu___365_4338.FStar_Syntax_Syntax.spec_dm4f);
                        FStar_Syntax_Syntax.actions =
                          (uu___365_4338.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___365_4338.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____4288, uu____4337)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___366_4420 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___366_4420.subst);
        tc_const = (uu___366_4420.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4441 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4461 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____4482) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___352_4496  ->
                match uu___352_4496 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4499 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____4501 ->
        let uu____4502 =
          let uu____4508 =
            let uu____4510 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____4510
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____4508)  in
        FStar_Errors.raise_error uu____4502 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___353_4520  ->
    match uu___353_4520 with
    | N t ->
        let uu____4523 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4523
    | M t ->
        let uu____4527 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4527
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____4536,c) -> nm_of_comp c
    | uu____4558 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4571 = nm_of_comp c  in
    match uu____4571 with | M uu____4573 -> true | N uu____4575 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4586 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4602 =
        let uu____4611 =
          let uu____4618 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4618  in
        [uu____4611]  in
      let uu____4637 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4602 uu____4637  in
    let uu____4640 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____4640
  
let rec (mk_star_to_type :
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun mk1  ->
    fun env  ->
      fun a  ->
        let uu____4682 =
          let uu____4683 =
            let uu____4698 =
              let uu____4707 =
                let uu____4714 =
                  let uu____4715 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____4715  in
                let uu____4716 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____4714, uu____4716)  in
              [uu____4707]  in
            let uu____4734 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____4698, uu____4734)  in
          FStar_Syntax_Syntax.Tm_arrow uu____4683  in
        mk1 uu____4682

and (star_type' :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
         in
      let mk_star_to_type1 = mk_star_to_type mk1  in
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4774) ->
          let binders1 =
            FStar_List.map
              (fun uu____4820  ->
                 match uu____4820 with
                 | (bv,aqual) ->
                     let uu____4839 =
                       let uu___367_4840 = bv  in
                       let uu____4841 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___367_4840.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___367_4840.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____4841
                       }  in
                     (uu____4839, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____4846,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____4848);
                             FStar_Syntax_Syntax.pos = uu____4849;
                             FStar_Syntax_Syntax.vars = uu____4850;_})
               ->
               let uu____4879 =
                 let uu____4880 =
                   let uu____4895 =
                     let uu____4898 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____4898  in
                   (binders1, uu____4895)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____4880  in
               mk1 uu____4879
           | uu____4909 ->
               let uu____4910 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____4910 with
                | N hn ->
                    let uu____4912 =
                      let uu____4913 =
                        let uu____4928 =
                          let uu____4931 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____4931  in
                        (binders1, uu____4928)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4913  in
                    mk1 uu____4912
                | M a ->
                    let uu____4943 =
                      let uu____4944 =
                        let uu____4959 =
                          let uu____4968 =
                            let uu____4977 =
                              let uu____4984 =
                                let uu____4985 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4985  in
                              let uu____4986 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4984, uu____4986)  in
                            [uu____4977]  in
                          FStar_List.append binders1 uu____4968  in
                        let uu____5010 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4959, uu____5010)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4944  in
                    mk1 uu____4943))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____5104 = f x  in
                    FStar_Util.string_builder_append strb uu____5104);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____5113 = f x1  in
                         FStar_Util.string_builder_append strb uu____5113))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____5117 =
              let uu____5123 =
                let uu____5125 = FStar_Syntax_Print.term_to_string t2  in
                let uu____5127 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____5125 uu____5127
                 in
              (FStar_Errors.Warning_DependencyFound, uu____5123)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____5117  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____5149 =
              let uu____5150 = FStar_Syntax_Subst.compress ty  in
              uu____5150.FStar_Syntax_Syntax.n  in
            match uu____5149 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5176 =
                  let uu____5178 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____5178  in
                if uu____5176
                then false
                else
                  (try
                     (fun uu___369_5195  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____5219 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____5219 s  in
                              let uu____5222 =
                                let uu____5224 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____5224  in
                              if uu____5222
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____5230 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____5230 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____5255  ->
                                          match uu____5255 with
                                          | (bv,uu____5267) ->
                                              (non_dependent_or_raise s
                                                 bv.FStar_Syntax_Syntax.sort;
                                               FStar_Util.set_add bv s))
                                     FStar_Syntax_Syntax.no_names binders1
                                    in
                                 let ct = FStar_Syntax_Util.comp_result c1
                                    in
                                 (non_dependent_or_raise s ct;
                                  (let k = n1 - (FStar_List.length binders1)
                                      in
                                   if k > (Prims.parse_int "0")
                                   then is_non_dependent_arrow ct k
                                   else true)))) ()
                   with | Not_found  -> false)
            | uu____5295 ->
                ((let uu____5297 =
                    let uu____5303 =
                      let uu____5305 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____5305
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____5303)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____5297);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____5321 =
              let uu____5322 = FStar_Syntax_Subst.compress head2  in
              uu____5322.FStar_Syntax_Syntax.n  in
            match uu____5321 with
            | FStar_Syntax_Syntax.Tm_fvar fv when
                (((FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.option_lid)
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.either_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.eq2_lid))
                  ||
                  (let uu____5328 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____5328)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____5331 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____5331 with
                 | ((uu____5341,ty),uu____5343) ->
                     let uu____5348 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____5348
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____5361 =
                         let uu____5362 = FStar_Syntax_Subst.compress res  in
                         uu____5362.FStar_Syntax_Syntax.n  in
                       (match uu____5361 with
                        | FStar_Syntax_Syntax.Tm_app uu____5366 -> true
                        | uu____5384 ->
                            ((let uu____5386 =
                                let uu____5392 =
                                  let uu____5394 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____5394
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____5392)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____5386);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____5402 -> true
            | FStar_Syntax_Syntax.Tm_name uu____5404 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5407) ->
                is_valid_application t2
            | uu____5412 -> false  in
          let uu____5414 = is_valid_application head1  in
          if uu____5414
          then
            let uu____5417 =
              let uu____5418 =
                let uu____5435 =
                  FStar_List.map
                    (fun uu____5464  ->
                       match uu____5464 with
                       | (t2,qual) ->
                           let uu____5489 = star_type' env t2  in
                           (uu____5489, qual)) args
                   in
                (head1, uu____5435)  in
              FStar_Syntax_Syntax.Tm_app uu____5418  in
            mk1 uu____5417
          else
            (let uu____5506 =
               let uu____5512 =
                 let uu____5514 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5514
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5512)  in
             FStar_Errors.raise_err uu____5506)
      | FStar_Syntax_Syntax.Tm_bvar uu____5518 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5519 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5520 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5521 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5549 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5549 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___370_5557 = env  in
                 let uu____5558 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____5558;
                   subst = (uu___370_5557.subst);
                   tc_const = (uu___370_5557.tc_const)
                 }  in
               let repr2 = star_type' env1 repr1  in
               FStar_Syntax_Util.abs binders1 repr2 something)
      | FStar_Syntax_Syntax.Tm_refine (x,t2) when false ->
          let x1 = FStar_Syntax_Syntax.freshen_bv x  in
          let sort = star_type' env x1.FStar_Syntax_Syntax.sort  in
          let subst1 = [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x1)]
             in
          let t3 = FStar_Syntax_Subst.subst subst1 t2  in
          let t4 = star_type' env t3  in
          let subst2 = [FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))]
             in
          let t5 = FStar_Syntax_Subst.subst subst2 t4  in
          mk1
            (FStar_Syntax_Syntax.Tm_refine
               ((let uu___371_5585 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___371_5585.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___371_5585.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5592 =
            let uu____5593 =
              let uu____5600 = star_type' env t2  in (uu____5600, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5593  in
          mk1 uu____5592
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____5652 =
            let uu____5653 =
              let uu____5680 = star_type' env e  in
              let uu____5683 =
                let uu____5700 =
                  let uu____5709 = star_type' env t2  in
                  FStar_Util.Inl uu____5709  in
                (uu____5700, FStar_Pervasives_Native.None)  in
              (uu____5680, uu____5683, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5653  in
          mk1 uu____5652
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____5797 =
            let uu____5798 =
              let uu____5825 = star_type' env e  in
              let uu____5828 =
                let uu____5845 =
                  let uu____5854 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____5854  in
                (uu____5845, FStar_Pervasives_Native.None)  in
              (uu____5825, uu____5828, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5798  in
          mk1 uu____5797
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____5895,(uu____5896,FStar_Pervasives_Native.Some uu____5897),uu____5898)
          ->
          let uu____5947 =
            let uu____5953 =
              let uu____5955 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____5955
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5953)  in
          FStar_Errors.raise_err uu____5947
      | FStar_Syntax_Syntax.Tm_refine uu____5959 ->
          let uu____5966 =
            let uu____5972 =
              let uu____5974 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____5974
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5972)  in
          FStar_Errors.raise_err uu____5966
      | FStar_Syntax_Syntax.Tm_uinst uu____5978 ->
          let uu____5985 =
            let uu____5991 =
              let uu____5993 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____5993
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5991)  in
          FStar_Errors.raise_err uu____5985
      | FStar_Syntax_Syntax.Tm_quoted uu____5997 ->
          let uu____6004 =
            let uu____6010 =
              let uu____6012 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____6012
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6010)  in
          FStar_Errors.raise_err uu____6004
      | FStar_Syntax_Syntax.Tm_constant uu____6016 ->
          let uu____6017 =
            let uu____6023 =
              let uu____6025 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____6025
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6023)  in
          FStar_Errors.raise_err uu____6017
      | FStar_Syntax_Syntax.Tm_match uu____6029 ->
          let uu____6052 =
            let uu____6058 =
              let uu____6060 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____6060
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6058)  in
          FStar_Errors.raise_err uu____6052
      | FStar_Syntax_Syntax.Tm_let uu____6064 ->
          let uu____6078 =
            let uu____6084 =
              let uu____6086 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____6086
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6084)  in
          FStar_Errors.raise_err uu____6078
      | FStar_Syntax_Syntax.Tm_uvar uu____6090 ->
          let uu____6103 =
            let uu____6109 =
              let uu____6111 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____6111
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6109)  in
          FStar_Errors.raise_err uu____6103
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____6115 =
            let uu____6121 =
              let uu____6123 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____6123
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6121)  in
          FStar_Errors.raise_err uu____6115
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6128 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____6128
      | FStar_Syntax_Syntax.Tm_delayed uu____6131 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___355_6163  ->
    match uu___355_6163 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___354_6174  ->
                match uu___354_6174 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____6177 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____6187 =
      let uu____6188 = FStar_Syntax_Subst.compress t  in
      uu____6188.FStar_Syntax_Syntax.n  in
    match uu____6187 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____6220 =
            let uu____6221 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____6221  in
          is_C uu____6220  in
        if r
        then
          ((let uu____6245 =
              let uu____6247 =
                FStar_List.for_all
                  (fun uu____6258  ->
                     match uu____6258 with | (h,uu____6267) -> is_C h) args
                 in
              Prims.op_Negation uu____6247  in
            if uu____6245 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____6280 =
              let uu____6282 =
                FStar_List.for_all
                  (fun uu____6294  ->
                     match uu____6294 with
                     | (h,uu____6303) ->
                         let uu____6308 = is_C h  in
                         Prims.op_Negation uu____6308) args
                 in
              Prims.op_Negation uu____6282  in
            if uu____6280 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____6337 = nm_of_comp comp  in
        (match uu____6337 with
         | M t1 ->
             ((let uu____6341 = is_C t1  in
               if uu____6341 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____6350) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6356) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____6362,uu____6363) -> is_C t1
    | uu____6404 -> false
  
let (mk_return :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun t  ->
      fun e  ->
        let mk1 x =
          FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos
           in
        let p_type = mk_star_to_type mk1 env t  in
        let p =
          FStar_Syntax_Syntax.gen_bv "p'" FStar_Pervasives_Native.None p_type
           in
        let body =
          let uu____6440 =
            let uu____6441 =
              let uu____6458 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____6461 =
                let uu____6472 =
                  let uu____6481 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____6481)  in
                [uu____6472]  in
              (uu____6458, uu____6461)  in
            FStar_Syntax_Syntax.Tm_app uu____6441  in
          mk1 uu____6440  in
        let uu____6517 =
          let uu____6518 = FStar_Syntax_Syntax.mk_binder p  in [uu____6518]
           in
        FStar_Syntax_Util.abs uu____6517 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___356_6543  ->
    match uu___356_6543 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6546 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____6784 =
          match uu____6784 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____6821 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____6824 =
                       let uu____6826 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____6826  in
                     Prims.op_Negation uu____6824)
                   in
                if uu____6821
                then
                  let uu____6828 =
                    let uu____6834 =
                      let uu____6836 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____6838 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____6840 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____6836 uu____6838 uu____6840
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____6834)  in
                  FStar_Errors.raise_err uu____6828
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____6865 = mk_return env t1 s_e  in
                     ((M t1), uu____6865, u_e)))
               | (M t1,N t2) ->
                   let uu____6872 =
                     let uu____6878 =
                       let uu____6880 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6882 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____6884 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____6880 uu____6882 uu____6884
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____6878)
                      in
                   FStar_Errors.raise_err uu____6872)
           in
        let ensure_m env1 e2 =
          let strip_m uu___357_6936 =
            match uu___357_6936 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____6952 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____6973 =
                let uu____6979 =
                  let uu____6981 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____6981
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____6979)  in
              FStar_Errors.raise_error uu____6973 e2.FStar_Syntax_Syntax.pos
          | M uu____6991 ->
              let uu____6992 = check env1 e2 context_nm  in
              strip_m uu____6992
           in
        let uu____6999 =
          let uu____7000 = FStar_Syntax_Subst.compress e  in
          uu____7000.FStar_Syntax_Syntax.n  in
        match uu____6999 with
        | FStar_Syntax_Syntax.Tm_bvar uu____7009 ->
            let uu____7010 = infer env e  in return_if uu____7010
        | FStar_Syntax_Syntax.Tm_name uu____7017 ->
            let uu____7018 = infer env e  in return_if uu____7018
        | FStar_Syntax_Syntax.Tm_fvar uu____7025 ->
            let uu____7026 = infer env e  in return_if uu____7026
        | FStar_Syntax_Syntax.Tm_abs uu____7033 ->
            let uu____7052 = infer env e  in return_if uu____7052
        | FStar_Syntax_Syntax.Tm_constant uu____7059 ->
            let uu____7060 = infer env e  in return_if uu____7060
        | FStar_Syntax_Syntax.Tm_quoted uu____7067 ->
            let uu____7074 = infer env e  in return_if uu____7074
        | FStar_Syntax_Syntax.Tm_app uu____7081 ->
            let uu____7098 = infer env e  in return_if uu____7098
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____7106 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____7106 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____7171) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7177) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7183,uu____7184) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____7225 ->
            let uu____7239 =
              let uu____7241 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____7241  in
            failwith uu____7239
        | FStar_Syntax_Syntax.Tm_type uu____7250 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____7258 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____7280 ->
            let uu____7287 =
              let uu____7289 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____7289  in
            failwith uu____7287
        | FStar_Syntax_Syntax.Tm_uvar uu____7298 ->
            let uu____7311 =
              let uu____7313 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____7313  in
            failwith uu____7311
        | FStar_Syntax_Syntax.Tm_delayed uu____7322 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____7352 =
              let uu____7354 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____7354  in
            failwith uu____7352

and (infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          e.FStar_Syntax_Syntax.pos
         in
      let normalize1 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses] env.tcenv
         in
      let uu____7384 =
        let uu____7385 = FStar_Syntax_Subst.compress e  in
        uu____7385.FStar_Syntax_Syntax.n  in
      match uu____7384 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7404 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____7404
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____7455;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____7456;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____7462 =
                  let uu___372_7463 = rc  in
                  let uu____7464 =
                    let uu____7469 =
                      let uu____7472 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____7472  in
                    FStar_Pervasives_Native.Some uu____7469  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___372_7463.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____7464;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___372_7463.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____7462
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___373_7484 = env  in
            let uu____7485 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____7485;
              subst = (uu___373_7484.subst);
              tc_const = (uu___373_7484.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____7511  ->
                 match uu____7511 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___374_7534 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___374_7534.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___374_7534.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____7535 =
            FStar_List.fold_left
              (fun uu____7566  ->
                 fun uu____7567  ->
                   match (uu____7566, uu____7567) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7625 = is_C c  in
                       if uu____7625
                       then
                         let xw =
                           let uu____7635 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____7635
                            in
                         let x =
                           let uu___375_7638 = bv  in
                           let uu____7639 =
                             let uu____7642 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____7642  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___375_7638.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___375_7638.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7639
                           }  in
                         let env3 =
                           let uu___376_7644 = env2  in
                           let uu____7645 =
                             let uu____7648 =
                               let uu____7649 =
                                 let uu____7656 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____7656)  in
                               FStar_Syntax_Syntax.NT uu____7649  in
                             uu____7648 :: (env2.subst)  in
                           {
                             tcenv = (uu___376_7644.tcenv);
                             subst = uu____7645;
                             tc_const = (uu___376_7644.tc_const)
                           }  in
                         let uu____7661 =
                           let uu____7664 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____7665 =
                             let uu____7668 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____7668 :: acc  in
                           uu____7664 :: uu____7665  in
                         (env3, uu____7661)
                       else
                         (let x =
                            let uu___377_7674 = bv  in
                            let uu____7675 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___377_7674.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___377_7674.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____7675
                            }  in
                          let uu____7678 =
                            let uu____7681 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____7681 :: acc  in
                          (env2, uu____7678))) (env1, []) binders1
             in
          (match uu____7535 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____7701 =
                 let check_what =
                   let uu____7727 = is_monadic rc_opt1  in
                   if uu____7727 then check_m else check_n  in
                 let uu____7744 = check_what env2 body1  in
                 match uu____7744 with
                 | (t,s_body,u_body) ->
                     let uu____7764 =
                       let uu____7767 =
                         let uu____7768 = is_monadic rc_opt1  in
                         if uu____7768 then M t else N t  in
                       comp_of_nm uu____7767  in
                     (uu____7764, s_body, u_body)
                  in
               (match uu____7701 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp  in
                    let s_rc_opt =
                      match rc_opt1 with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some rc ->
                          (match rc.FStar_Syntax_Syntax.residual_typ with
                           | FStar_Pervasives_Native.None  ->
                               let rc1 =
                                 let uu____7808 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___358_7814  ->
                                           match uu___358_7814 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____7817 -> false))
                                    in
                                 if uu____7808
                                 then
                                   let uu____7820 =
                                     FStar_List.filter
                                       (fun uu___359_7824  ->
                                          match uu___359_7824 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____7827 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____7820
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____7838 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___360_7844  ->
                                         match uu___360_7844 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____7847 -> false))
                                  in
                               if uu____7838
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___361_7856  ->
                                        match uu___361_7856 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____7859 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____7861 =
                                   let uu____7862 =
                                     let uu____7867 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____7867
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____7862 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____7861
                               else
                                 (let uu____7874 =
                                    let uu___378_7875 = rc  in
                                    let uu____7876 =
                                      let uu____7881 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____7881
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___378_7875.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____7876;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___378_7875.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____7874))
                       in
                    let uu____7886 =
                      let comp1 =
                        let uu____7894 = is_monadic rc_opt1  in
                        let uu____7896 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____7894 uu____7896
                         in
                      let uu____7897 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____7897,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____7886 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____7935 =
                             let uu____7936 =
                               let uu____7955 =
                                 let uu____7958 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____7958 s_rc_opt  in
                               (s_binders1, s_body1, uu____7955)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7936  in
                           mk1 uu____7935  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____7978 =
                             let uu____7979 =
                               let uu____7998 =
                                 let uu____8001 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____8001 u_rc_opt  in
                               (u_binders2, u_body2, uu____7998)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7979  in
                           mk1 uu____7978  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____8017;_};
            FStar_Syntax_Syntax.fv_delta = uu____8018;
            FStar_Syntax_Syntax.fv_qual = uu____8019;_}
          ->
          let uu____8022 =
            let uu____8027 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8027  in
          (match uu____8022 with
           | (uu____8058,t) ->
               let uu____8060 =
                 let uu____8061 = normalize1 t  in N uu____8061  in
               (uu____8060, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8062;
             FStar_Syntax_Syntax.vars = uu____8063;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____8142 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8142 with
           | (unary_op1,uu____8166) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8237;
             FStar_Syntax_Syntax.vars = uu____8238;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____8334 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8334 with
           | (unary_op1,uu____8358) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8437;
             FStar_Syntax_Syntax.vars = uu____8438;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____8476 = infer env a  in
          (match uu____8476 with
           | (t,s,u) ->
               let uu____8492 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8492 with
                | (head1,uu____8516) ->
                    let uu____8541 =
                      let uu____8542 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____8542  in
                    let uu____8543 =
                      let uu____8544 =
                        let uu____8545 =
                          let uu____8562 =
                            let uu____8573 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8573]  in
                          (head1, uu____8562)  in
                        FStar_Syntax_Syntax.Tm_app uu____8545  in
                      mk1 uu____8544  in
                    let uu____8610 =
                      let uu____8611 =
                        let uu____8612 =
                          let uu____8629 =
                            let uu____8640 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8640]  in
                          (head1, uu____8629)  in
                        FStar_Syntax_Syntax.Tm_app uu____8612  in
                      mk1 uu____8611  in
                    (uu____8541, uu____8543, uu____8610)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8677;
             FStar_Syntax_Syntax.vars = uu____8678;_},(a1,uu____8680)::a2::[])
          ->
          let uu____8736 = infer env a1  in
          (match uu____8736 with
           | (t,s,u) ->
               let uu____8752 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8752 with
                | (head1,uu____8776) ->
                    let uu____8801 =
                      let uu____8802 =
                        let uu____8803 =
                          let uu____8820 =
                            let uu____8831 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8831; a2]  in
                          (head1, uu____8820)  in
                        FStar_Syntax_Syntax.Tm_app uu____8803  in
                      mk1 uu____8802  in
                    let uu____8876 =
                      let uu____8877 =
                        let uu____8878 =
                          let uu____8895 =
                            let uu____8906 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8906; a2]  in
                          (head1, uu____8895)  in
                        FStar_Syntax_Syntax.Tm_app uu____8878  in
                      mk1 uu____8877  in
                    (t, uu____8801, uu____8876)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8951;
             FStar_Syntax_Syntax.vars = uu____8952;_},uu____8953)
          ->
          let uu____8978 =
            let uu____8984 =
              let uu____8986 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8986
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8984)  in
          FStar_Errors.raise_error uu____8978 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8996;
             FStar_Syntax_Syntax.vars = uu____8997;_},uu____8998)
          ->
          let uu____9023 =
            let uu____9029 =
              let uu____9031 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____9031
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____9029)  in
          FStar_Errors.raise_error uu____9023 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____9067 = check_n env head1  in
          (match uu____9067 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____9090 =
                   let uu____9091 = FStar_Syntax_Subst.compress t  in
                   uu____9091.FStar_Syntax_Syntax.n  in
                 match uu____9090 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____9095 -> true
                 | uu____9111 -> false  in
               let rec flatten1 t =
                 let uu____9133 =
                   let uu____9134 = FStar_Syntax_Subst.compress t  in
                   uu____9134.FStar_Syntax_Syntax.n  in
                 match uu____9133 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____9153);
                                FStar_Syntax_Syntax.pos = uu____9154;
                                FStar_Syntax_Syntax.vars = uu____9155;_})
                     when is_arrow t1 ->
                     let uu____9184 = flatten1 t1  in
                     (match uu____9184 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____9284,uu____9285)
                     -> flatten1 e1
                 | uu____9326 ->
                     let uu____9327 =
                       let uu____9333 =
                         let uu____9335 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____9335
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____9333)  in
                     FStar_Errors.raise_err uu____9327
                  in
               let uu____9353 = flatten1 t_head  in
               (match uu____9353 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____9428 =
                          let uu____9434 =
                            let uu____9436 = FStar_Util.string_of_int n1  in
                            let uu____9444 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____9456 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____9436 uu____9444 uu____9456
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____9434)
                           in
                        FStar_Errors.raise_err uu____9428)
                     else ();
                     (let uu____9468 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____9468 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____9521 args1 =
                            match uu____9521 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9621 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____9621
                                 | (binders3,[]) ->
                                     let uu____9659 =
                                       let uu____9660 =
                                         let uu____9663 =
                                           let uu____9664 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____9664
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____9663
                                          in
                                       uu____9660.FStar_Syntax_Syntax.n  in
                                     (match uu____9659 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____9697 =
                                            let uu____9698 =
                                              let uu____9699 =
                                                let uu____9714 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____9714)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9699
                                               in
                                            mk1 uu____9698  in
                                          N uu____9697
                                      | uu____9727 -> failwith "wat?")
                                 | ([],uu____9729::uu____9730) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____9783)::binders3,(arg,uu____9786)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____9873 = FStar_List.splitAt n' binders1  in
                          (match uu____9873 with
                           | (binders2,uu____9911) ->
                               let uu____9944 =
                                 let uu____9967 =
                                   FStar_List.map2
                                     (fun uu____10029  ->
                                        fun uu____10030  ->
                                          match (uu____10029, uu____10030)
                                          with
                                          | ((bv,uu____10078),(arg,q)) ->
                                              let uu____10107 =
                                                let uu____10108 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____10108.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____10107 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____10129 ->
                                                   let uu____10130 =
                                                     let uu____10137 =
                                                       star_type' env arg  in
                                                     (uu____10137, q)  in
                                                   (uu____10130, [(arg, q)])
                                               | uu____10174 ->
                                                   let uu____10175 =
                                                     check_n env arg  in
                                                   (match uu____10175 with
                                                    | (uu____10200,s_arg,u_arg)
                                                        ->
                                                        let uu____10203 =
                                                          let uu____10212 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____10212
                                                          then
                                                            let uu____10223 =
                                                              let uu____10230
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____10230,
                                                                q)
                                                               in
                                                            [uu____10223;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____10203))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____9967  in
                               (match uu____9944 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____10358 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____10371 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____10358, uu____10371)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____10440) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____10446) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____10452,uu____10453) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10495 =
            let uu____10496 = env.tc_const c  in N uu____10496  in
          (uu____10495, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____10503 ->
          let uu____10517 =
            let uu____10519 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____10519  in
          failwith uu____10517
      | FStar_Syntax_Syntax.Tm_type uu____10528 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____10536 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____10558 ->
          let uu____10565 =
            let uu____10567 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____10567  in
          failwith uu____10565
      | FStar_Syntax_Syntax.Tm_uvar uu____10576 ->
          let uu____10589 =
            let uu____10591 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____10591  in
          failwith uu____10589
      | FStar_Syntax_Syntax.Tm_delayed uu____10600 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____10630 =
            let uu____10632 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10632  in
          failwith uu____10630

and (mk_match :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
        FStar_Syntax_Syntax.syntax) Prims.list ->
        (env ->
           FStar_Syntax_Syntax.term ->
             (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
          -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
              e0.FStar_Syntax_Syntax.pos
             in
          let uu____10681 = check_n env e0  in
          match uu____10681 with
          | (uu____10694,s_e0,u_e0) ->
              let uu____10697 =
                let uu____10726 =
                  FStar_List.map
                    (fun b  ->
                       let uu____10787 = FStar_Syntax_Subst.open_branch b  in
                       match uu____10787 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___379_10829 = env  in
                             let uu____10830 =
                               let uu____10831 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____10831
                                in
                             {
                               tcenv = uu____10830;
                               subst = (uu___379_10829.subst);
                               tc_const = (uu___379_10829.tc_const)
                             }  in
                           let uu____10834 = f env1 body  in
                           (match uu____10834 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____10906 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____10726  in
              (match uu____10697 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____11012 = FStar_List.hd nms  in
                     match uu____11012 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___362_11021  ->
                          match uu___362_11021 with
                          | M uu____11023 -> true
                          | uu____11025 -> false) nms
                      in
                   let uu____11027 =
                     let uu____11064 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____11154  ->
                              match uu____11154 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____11338 =
                                         check env original_body (M t2)  in
                                       (match uu____11338 with
                                        | (uu____11375,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____11414,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____11064  in
                   (match uu____11027 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____11603  ->
                                 match uu____11603 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____11654 =
                                         let uu____11655 =
                                           let uu____11672 =
                                             let uu____11683 =
                                               let uu____11692 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____11695 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____11692, uu____11695)  in
                                             [uu____11683]  in
                                           (s_body, uu____11672)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____11655
                                          in
                                       mk1 uu____11654  in
                                     (pat, guard, s_body1)) s_branches
                             in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1
                             in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches
                             in
                          let s_e =
                            let uu____11830 =
                              let uu____11831 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11831]  in
                            let uu____11850 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____11830 uu____11850
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____11874 =
                              let uu____11883 =
                                let uu____11890 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____11890
                                 in
                              [uu____11883]  in
                            let uu____11909 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____11874 uu____11909
                             in
                          let uu____11912 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____11951 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____11912, uu____11951)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches
                              in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches
                              in
                           let t1_star = t1  in
                           let uu____12061 =
                             let uu____12062 =
                               let uu____12063 =
                                 let uu____12090 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____12090,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12063
                                in
                             mk1 uu____12062  in
                           let uu____12149 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____12061, uu____12149))))

and (mk_let :
  env_ ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.term ->
        (env_ ->
           FStar_Syntax_Syntax.term ->
             (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
          ->
          (env_ ->
             FStar_Syntax_Syntax.term ->
               (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
                 FStar_Syntax_Syntax.term))
            -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun binding  ->
      fun e2  ->
        fun proceed  ->
          fun ensure_m  ->
            let mk1 x =
              FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                e2.FStar_Syntax_Syntax.pos
               in
            let e1 = binding.FStar_Syntax_Syntax.lbdef  in
            let x = FStar_Util.left binding.FStar_Syntax_Syntax.lbname  in
            let x_binders =
              let uu____12214 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____12214]  in
            let uu____12233 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____12233 with
            | (x_binders1,e21) ->
                let uu____12246 = infer env e1  in
                (match uu____12246 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____12263 = is_C t1  in
                       if uu____12263
                       then
                         let uu___380_12266 = binding  in
                         let uu____12267 =
                           let uu____12270 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____12270  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___380_12266.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___380_12266.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____12267;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___380_12266.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___380_12266.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___380_12266.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___380_12266.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___381_12274 = env  in
                       let uu____12275 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___382_12277 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___382_12277.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___382_12277.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12275;
                         subst = (uu___381_12274.subst);
                         tc_const = (uu___381_12274.tc_const)
                       }  in
                     let uu____12278 = proceed env1 e21  in
                     (match uu____12278 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___383_12295 = binding  in
                            let uu____12296 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___383_12295.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___383_12295.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____12296;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___383_12295.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___383_12295.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___383_12295.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___383_12295.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____12299 =
                            let uu____12300 =
                              let uu____12301 =
                                let uu____12315 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___384_12332 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___384_12332.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___384_12332.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___384_12332.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___384_12332.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___384_12332.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___384_12332.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12315)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12301  in
                            mk1 uu____12300  in
                          let uu____12333 =
                            let uu____12334 =
                              let uu____12335 =
                                let uu____12349 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___385_12366 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___385_12366.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___385_12366.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___385_12366.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___385_12366.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___385_12366.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___385_12366.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12349)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12335  in
                            mk1 uu____12334  in
                          (nm_rec, uu____12299, uu____12333))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___386_12371 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___386_12371.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___386_12371.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___386_12371.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___386_12371.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___386_12371.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___387_12373 = env  in
                       let uu____12374 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___388_12376 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___388_12376.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___388_12376.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12374;
                         subst = (uu___387_12373.subst);
                         tc_const = (uu___387_12373.tc_const)
                       }  in
                     let uu____12377 = ensure_m env1 e21  in
                     (match uu____12377 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____12401 =
                              let uu____12402 =
                                let uu____12419 =
                                  let uu____12430 =
                                    let uu____12439 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____12442 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12439, uu____12442)  in
                                  [uu____12430]  in
                                (s_e2, uu____12419)  in
                              FStar_Syntax_Syntax.Tm_app uu____12402  in
                            mk1 uu____12401  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____12484 =
                              let uu____12485 =
                                let uu____12502 =
                                  let uu____12513 =
                                    let uu____12522 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____12522)  in
                                  [uu____12513]  in
                                (s_e1, uu____12502)  in
                              FStar_Syntax_Syntax.Tm_app uu____12485  in
                            mk1 uu____12484  in
                          let uu____12558 =
                            let uu____12559 =
                              let uu____12560 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12560]  in
                            FStar_Syntax_Util.abs uu____12559 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____12579 =
                            let uu____12580 =
                              let uu____12581 =
                                let uu____12595 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___389_12612 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___389_12612.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___389_12612.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___389_12612.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___389_12612.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___389_12612.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___389_12612.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12595)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12581  in
                            mk1 uu____12580  in
                          ((M t2), uu____12558, uu____12579)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12622 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____12622  in
      let uu____12623 = check env e mn  in
      match uu____12623 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12639 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12662 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____12662  in
      let uu____12663 = check env e mn  in
      match uu____12663 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12679 -> failwith "[check_m]: impossible"

and (comp_of_nm : nm_ -> FStar_Syntax_Syntax.comp) =
  fun nm  ->
    match nm with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t

and (mk_M : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp) =
  fun t  ->
    FStar_Syntax_Syntax.mk_Comp
      {
        FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_unknown];
        FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.monadic_lid;
        FStar_Syntax_Syntax.result_typ = t;
        FStar_Syntax_Syntax.effect_args = [];
        FStar_Syntax_Syntax.flags =
          [FStar_Syntax_Syntax.CPS; FStar_Syntax_Syntax.TOTAL]
      }

and (type_of_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun t  -> FStar_Syntax_Util.comp_result t

and (trans_F_ :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        (let uu____12712 =
           let uu____12714 = is_C c  in Prims.op_Negation uu____12714  in
         if uu____12712 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____12728 =
           let uu____12729 = FStar_Syntax_Subst.compress c  in
           uu____12729.FStar_Syntax_Syntax.n  in
         match uu____12728 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____12758 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____12758 with
              | (wp_head,wp_args) ->
                  ((let uu____12802 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____12821 =
                           let uu____12823 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____12823
                            in
                         Prims.op_Negation uu____12821)
                       in
                    if uu____12802 then failwith "mismatch" else ());
                   (let uu____12836 =
                      let uu____12837 =
                        let uu____12854 =
                          FStar_List.map2
                            (fun uu____12892  ->
                               fun uu____12893  ->
                                 match (uu____12892, uu____12893) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____12955 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____12955
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____12964 =
                                         let uu____12966 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____12966 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____12964
                                       then
                                         let uu____12968 =
                                           let uu____12974 =
                                             let uu____12976 =
                                               print_implicit q  in
                                             let uu____12978 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____12976 uu____12978
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____12974)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____12968
                                       else ());
                                      (let uu____12984 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____12984, q)))) args wp_args
                           in
                        (head1, uu____12854)  in
                      FStar_Syntax_Syntax.Tm_app uu____12837  in
                    mk1 uu____12836)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____13030 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____13030 with
              | (binders_orig,comp1) ->
                  let uu____13037 =
                    let uu____13054 =
                      FStar_List.map
                        (fun uu____13094  ->
                           match uu____13094 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____13122 = is_C h  in
                               if uu____13122
                               then
                                 let w' =
                                   let uu____13138 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____13138
                                    in
                                 let uu____13140 =
                                   let uu____13149 =
                                     let uu____13158 =
                                       let uu____13165 =
                                         let uu____13166 =
                                           let uu____13167 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____13167  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____13166
                                          in
                                       (uu____13165, q)  in
                                     [uu____13158]  in
                                   (w', q) :: uu____13149  in
                                 (w', uu____13140)
                               else
                                 (let x =
                                    let uu____13201 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____13201
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____13054  in
                  (match uu____13037 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____13275 =
                           let uu____13278 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____13278
                            in
                         FStar_Syntax_Subst.subst_comp uu____13275 comp1  in
                       let app =
                         let uu____13282 =
                           let uu____13283 =
                             let uu____13300 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____13319 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____13320 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____13319, uu____13320)) bvs
                                in
                             (wp, uu____13300)  in
                           FStar_Syntax_Syntax.Tm_app uu____13283  in
                         mk1 uu____13282  in
                       let comp3 =
                         let uu____13335 = type_of_comp comp2  in
                         let uu____13336 = is_monadic_comp comp2  in
                         trans_G env uu____13335 uu____13336 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____13339,uu____13340) ->
             trans_F_ env e wp
         | uu____13381 -> failwith "impossible trans_F_")

and (trans_G :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      Prims.bool -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun h  ->
      fun is_monadic1  ->
        fun wp  ->
          if is_monadic1
          then
            let uu____13389 =
              let uu____13390 = star_type' env h  in
              let uu____13393 =
                let uu____13404 =
                  let uu____13413 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____13413)  in
                [uu____13404]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____13390;
                FStar_Syntax_Syntax.effect_args = uu____13393;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____13389
          else
            (let uu____13439 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____13439)

let (n :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Env.Beta;
    FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
    FStar_TypeChecker_Env.DoNotUnfoldPureLets;
    FStar_TypeChecker_Env.Eager_unfolding;
    FStar_TypeChecker_Env.EraseUniverses]
  
let (star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun env  ->
    fun t  -> let uu____13460 = n env.tcenv t  in star_type' env uu____13460
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____13480 = n env.tcenv t  in check_n env uu____13480
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____13497 = n env.tcenv c  in
        let uu____13498 = n env.tcenv wp  in
        trans_F_ env uu____13497 uu____13498
  
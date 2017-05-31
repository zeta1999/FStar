open Prims
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let bnorm:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun e  -> fun t  -> FStar_TypeChecker_Normalize.normalize [] e t
type goal =
  {
  context: env;
  witness: FStar_Syntax_Syntax.term;
  goal_ty: FStar_Syntax_Syntax.typ;}
type proofstate =
  {
  main_context: env;
  main_goal: goal;
  all_implicits: implicits;
  goals: goal Prims.list;
  smt_goals: goal Prims.list;}
type 'a result =
  | Success of ('a* proofstate)
  | Failed of (Prims.string* proofstate)
let uu___is_Success projectee =
  match projectee with | Success _0 -> true | uu____96 -> false
let __proj__Success__item___0 projectee =
  match projectee with | Success _0 -> _0
let uu___is_Failed projectee =
  match projectee with | Failed _0 -> true | uu____127 -> false
let __proj__Failed__item___0 projectee =
  match projectee with | Failed _0 -> _0
exception Failure of Prims.string
let uu___is_Failure: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Failure uu____151 -> true | uu____152 -> false
let __proj__Failure__item__uu___: Prims.exn -> Prims.string =
  fun projectee  -> match projectee with | Failure uu____159 -> uu____159
type 'a tac = {
  tac_f: proofstate -> 'a result;}
let mk_tac f = { tac_f = f }
let run t p = t.tac_f p
let ret x = mk_tac (fun p  -> Success (x, p))
let bind t1 t2 =
  mk_tac
    (fun p  ->
       let uu____252 = run t1 p in
       match uu____252 with
       | Success (a,q) -> let uu____257 = t2 a in run uu____257 q
       | Failed (msg,q) -> Failed (msg, q))
let idtac: Prims.unit tac = ret ()
let goal_to_string: goal -> Prims.string =
  fun g  ->
    let g_binders =
      let uu____266 = FStar_TypeChecker_Env.all_binders g.context in
      FStar_All.pipe_right uu____266
        (FStar_Syntax_Print.binders_to_string ", ") in
    let uu____267 = FStar_Syntax_Print.term_to_string g.witness in
    let uu____268 = FStar_Syntax_Print.term_to_string g.goal_ty in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____267 uu____268
let tacprint: Prims.string -> Prims.unit =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s
let tacprint1: Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      let uu____278 = FStar_Util.format1 s x in
      FStar_Util.print1 "TAC>> %s\n" uu____278
let tacprint2: Prims.string -> Prims.string -> Prims.string -> Prims.unit =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____288 = FStar_Util.format2 s x y in
        FStar_Util.print1 "TAC>> %s\n" uu____288
let tacprint3:
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> Prims.unit
  =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____301 = FStar_Util.format3 s x y z in
          FStar_Util.print1 "TAC>> %s\n" uu____301
let comp_to_typ:
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____306) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____314) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let is_irrelevant: goal -> Prims.bool =
  fun g  ->
    let uu____325 = FStar_Syntax_Util.un_squash g.goal_ty in
    match uu____325 with | Some t -> true | uu____334 -> false
let mk_irrelevant: env -> FStar_Syntax_Syntax.typ -> goal =
  fun env  ->
    fun phi  ->
      let typ = FStar_Syntax_Util.mk_squash phi in
      let uu____347 =
        FStar_TypeChecker_Util.new_implicit_var "mk_irrelevant"
          phi.FStar_Syntax_Syntax.pos env typ in
      match uu____347 with
      | (u,uu____355,g_u) -> { context = env; witness = u; goal_ty = typ }
let dump_goal ps goal =
  let uu____376 = goal_to_string goal in tacprint uu____376
let dump_proofstate: proofstate -> Prims.string -> Prims.unit =
  fun ps  ->
    fun msg  ->
      tacprint "";
      tacprint1 "State dump (%s):" msg;
      (let uu____386 = FStar_Util.string_of_int (FStar_List.length ps.goals) in
       tacprint1 "ACTIVE goals (%s):" uu____386);
      FStar_List.iter (dump_goal ps) ps.goals;
      (let uu____392 =
         FStar_Util.string_of_int (FStar_List.length ps.smt_goals) in
       tacprint1 "SMT goals (%s):" uu____392);
      FStar_List.iter (dump_goal ps) ps.smt_goals
let print_proof_state: Prims.string -> Prims.unit tac =
  fun msg  -> mk_tac (fun p  -> dump_proofstate p msg; Success ((), p))
let get: proofstate tac = mk_tac (fun p  -> Success (p, p))
let tac_verb_dbg: Prims.bool option FStar_ST.ref = FStar_Util.mk_ref None
let rec log: proofstate -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun ps  ->
    fun f  ->
      let uu____422 = FStar_ST.read tac_verb_dbg in
      match uu____422 with
      | None  ->
          ((let uu____428 =
              let uu____430 =
                FStar_TypeChecker_Env.debug ps.main_context
                  (FStar_Options.Other "TacVerbose") in
              Some uu____430 in
            FStar_ST.write tac_verb_dbg uu____428);
           log ps f)
      | Some (true ) -> f ()
      | Some (false ) -> ()
let mlog: (Prims.unit -> Prims.unit) -> Prims.unit tac =
  fun f  -> bind get (fun ps  -> log ps f; ret ())
let fail msg =
  mk_tac
    (fun ps  ->
       (let uu____456 =
          FStar_TypeChecker_Env.debug ps.main_context
            (FStar_Options.Other "TacFail") in
        if uu____456 then dump_proofstate ps "TACTING FAILING" else ());
       Failed (msg, ps))
let set: proofstate -> Prims.unit tac =
  fun p  -> mk_tac (fun uu____463  -> Success ((), p))
let solve: goal -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun goal  ->
    fun solution  ->
      let uu____470 =
        FStar_TypeChecker_Rel.teq_nosmt goal.context goal.witness solution in
      if uu____470
      then ()
      else
        (let uu____472 =
           let uu____473 =
             let uu____474 = FStar_Syntax_Print.term_to_string solution in
             let uu____475 = FStar_Syntax_Print.term_to_string goal.witness in
             let uu____476 = FStar_Syntax_Print.term_to_string goal.goal_ty in
             FStar_Util.format3 "%s does not solve %s : %s" uu____474
               uu____475 uu____476 in
           Failure uu____473 in
         raise uu____472)
let dismiss: Prims.unit tac =
  bind get
    (fun p  ->
       let uu____479 =
         let uu___78_480 = p in
         let uu____481 = FStar_List.tl p.goals in
         {
           main_context = (uu___78_480.main_context);
           main_goal = (uu___78_480.main_goal);
           all_implicits = (uu___78_480.all_implicits);
           goals = uu____481;
           smt_goals = (uu___78_480.smt_goals)
         } in
       set uu____479)
let dismiss_all: Prims.unit tac =
  bind get
    (fun p  ->
       set
         (let uu___79_485 = p in
          {
            main_context = (uu___79_485.main_context);
            main_goal = (uu___79_485.main_goal);
            all_implicits = (uu___79_485.all_implicits);
            goals = [];
            smt_goals = (uu___79_485.smt_goals)
          }))
let add_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___80_494 = p in
            {
              main_context = (uu___80_494.main_context);
              main_goal = (uu___80_494.main_goal);
              all_implicits = (uu___80_494.all_implicits);
              goals = (FStar_List.append gs p.goals);
              smt_goals = (uu___80_494.smt_goals)
            }))
let add_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___81_503 = p in
            {
              main_context = (uu___81_503.main_context);
              main_goal = (uu___81_503.main_goal);
              all_implicits = (uu___81_503.all_implicits);
              goals = (uu___81_503.goals);
              smt_goals = (FStar_List.append gs p.smt_goals)
            }))
let push_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___82_512 = p in
            {
              main_context = (uu___82_512.main_context);
              main_goal = (uu___82_512.main_goal);
              all_implicits = (uu___82_512.all_implicits);
              goals = (FStar_List.append p.goals gs);
              smt_goals = (uu___82_512.smt_goals)
            }))
let push_smt_goals: goal Prims.list -> Prims.unit tac =
  fun gs  ->
    bind get
      (fun p  ->
         set
           (let uu___83_521 = p in
            {
              main_context = (uu___83_521.main_context);
              main_goal = (uu___83_521.main_goal);
              all_implicits = (uu___83_521.all_implicits);
              goals = (uu___83_521.goals);
              smt_goals = (FStar_List.append p.smt_goals gs)
            }))
let replace_cur: goal -> Prims.unit tac =
  fun g  -> bind dismiss (fun uu____527  -> add_goals [g])
let add_implicits: implicits -> Prims.unit tac =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___84_534 = p in
            {
              main_context = (uu___84_534.main_context);
              main_goal = (uu___84_534.main_goal);
              all_implicits = (FStar_List.append i p.all_implicits);
              goals = (uu___84_534.goals);
              smt_goals = (uu___84_534.smt_goals)
            }))
let is_true: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____544 = FStar_Syntax_Util.un_squash t in
    match uu____544 with
    | Some t' ->
        let uu____553 =
          let uu____554 = FStar_Syntax_Subst.compress t' in
          uu____554.FStar_Syntax_Syntax.n in
        (match uu____553 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid
         | uu____558 -> false)
    | uu____559 -> false
let is_false: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____566 = FStar_Syntax_Util.un_squash t in
    match uu____566 with
    | Some t' ->
        let uu____575 =
          let uu____576 = FStar_Syntax_Subst.compress t' in
          uu____576.FStar_Syntax_Syntax.n in
        (match uu____575 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid
         | uu____580 -> false)
    | uu____581 -> false
let cur_goal: goal tac =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> fail "No more goals (1)"
       | hd1::tl1 -> ret hd1)
let smt: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____593 = is_irrelevant g in
       if uu____593
       then bind dismiss (fun uu____595  -> add_smt_goals [g])
       else
         (let uu____597 =
            let uu____598 = FStar_Syntax_Print.term_to_string g.goal_ty in
            FStar_Util.format1
              "goal is not irrelevant: cannot dispatch to smt (%s)" uu____598 in
          fail uu____597))
let divide n1 l r =
  bind get
    (fun p  ->
       let uu____628 =
         try let uu____645 = FStar_List.splitAt n1 p.goals in ret uu____645
         with | uu____660 -> fail "divide: not enough goals" in
       bind uu____628
         (fun uu____671  ->
            match uu____671 with
            | (lgs,rgs) ->
                let lp =
                  let uu___85_686 = p in
                  {
                    main_context = (uu___85_686.main_context);
                    main_goal = (uu___85_686.main_goal);
                    all_implicits = (uu___85_686.all_implicits);
                    goals = lgs;
                    smt_goals = []
                  } in
                let rp =
                  let uu___86_688 = p in
                  {
                    main_context = (uu___86_688.main_context);
                    main_goal = (uu___86_688.main_goal);
                    all_implicits = (uu___86_688.all_implicits);
                    goals = rgs;
                    smt_goals = []
                  } in
                let uu____689 = set lp in
                bind uu____689
                  (fun uu____693  ->
                     bind l
                       (fun a  ->
                          bind get
                            (fun lp'  ->
                               let uu____700 = set rp in
                               bind uu____700
                                 (fun uu____704  ->
                                    bind r
                                      (fun b  ->
                                         bind get
                                           (fun rp'  ->
                                              let p' =
                                                let uu___87_712 = p in
                                                {
                                                  main_context =
                                                    (uu___87_712.main_context);
                                                  main_goal =
                                                    (uu___87_712.main_goal);
                                                  all_implicits =
                                                    (uu___87_712.all_implicits);
                                                  goals =
                                                    (FStar_List.append
                                                       lp'.goals rp'.goals);
                                                  smt_goals =
                                                    (FStar_List.append
                                                       lp'.smt_goals
                                                       (FStar_List.append
                                                          rp'.smt_goals
                                                          p.smt_goals))
                                                } in
                                              let uu____713 = set p' in
                                              bind uu____713
                                                (fun uu____717  -> ret (a, b))))))))))
let focus_cur_goal f =
  let uu____730 = divide (Prims.parse_int "1") f idtac in
  bind uu____730 (fun uu____736  -> match uu____736 with | (a,()) -> ret a)
let or_else t1 t2 =
  mk_tac
    (fun p  ->
       let uu____759 = t1.tac_f p in
       match uu____759 with | Failed uu____762 -> t2.tac_f p | q -> q)
let rec map tau =
  bind get
    (fun p  ->
       match p.goals with
       | [] -> ret []
       | uu____783::uu____784 ->
           let uu____786 =
             let uu____791 = map tau in
             divide (Prims.parse_int "1") tau uu____791 in
           bind uu____786
             (fun uu____799  -> match uu____799 with | (h,t) -> ret (h :: t)))
let seq: Prims.unit tac -> Prims.unit tac -> Prims.unit tac =
  fun t1  ->
    fun t2  ->
      let uu____822 =
        bind t1
          (fun uu____824  ->
             let uu____825 = map t2 in
             bind uu____825 (fun uu____829  -> ret ())) in
      focus_cur_goal uu____822
let arrow_one:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.comp) option
  =
  fun t  ->
    let uu____840 =
      let uu____841 = FStar_Syntax_Subst.compress t in
      uu____841.FStar_Syntax_Syntax.n in
    match uu____840 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) -> Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____902 =
          let uu____907 =
            let uu____908 = FStar_Syntax_Util.arrow bs c in
            FStar_Syntax_Syntax.mk_Total uu____908 in
          (b, uu____907) in
        Some uu____902
    | uu____915 -> None
let __intro:
  Prims.bool -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) tac =
  fun irrel  ->
    bind cur_goal
      (fun goal  ->
         let uu____926 = arrow_one goal.goal_ty in
         match uu____926 with
         | Some (b,c) ->
             let uu____937 = FStar_Syntax_Subst.open_comp [b] c in
             (match uu____937 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____957 ->
                        failwith
                          "impossible: open_comp returned different amount of binders" in
                  let uu____960 =
                    let uu____961 = FStar_Syntax_Util.is_total_comp c1 in
                    Prims.op_Negation uu____961 in
                  if uu____960
                  then fail "Codomain is effectful"
                  else
                    (let env = goal.context in
                     let env' = FStar_TypeChecker_Env.push_binders env [b1] in
                     let typ' = comp_to_typ c1 in
                     let uu____975 =
                       FStar_TypeChecker_Util.new_implicit_var "intro"
                         typ'.FStar_Syntax_Syntax.pos
                         (if irrel then env else env') typ' in
                     match uu____975 with
                     | (u,uu____987,g) ->
                         let uu____995 =
                           let uu____996 = FStar_Syntax_Util.abs [b1] u None in
                           FStar_TypeChecker_Rel.teq_nosmt goal.context
                             goal.witness uu____996 in
                         if uu____995
                         then
                           let uu____1009 =
                             let uu____1011 =
                               let uu___90_1012 = goal in
                               let uu____1013 = bnorm env' u in
                               let uu____1014 = bnorm env' typ' in
                               {
                                 context = env';
                                 witness = uu____1013;
                                 goal_ty = uu____1014
                               } in
                             replace_cur uu____1011 in
                           bind uu____1009 (fun uu____1017  -> ret b1)
                         else fail "intro: unification failed"))
         | None  -> fail "intro: goal is not an arrow")
let intro: FStar_Syntax_Syntax.binder tac = __intro false
let intro_irrel: FStar_Syntax_Syntax.binder tac = __intro true
let norm: FStar_Reflection_Data.norm_step Prims.list -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun goal  ->
         let tr s1 =
           match s1 with
           | FStar_Reflection_Data.Simpl  ->
               [FStar_TypeChecker_Normalize.Simplify]
           | FStar_Reflection_Data.WHNF  ->
               [FStar_TypeChecker_Normalize.WHNF]
           | FStar_Reflection_Data.Primops  ->
               [FStar_TypeChecker_Normalize.Primops]
           | FStar_Reflection_Data.Delta  ->
               [FStar_TypeChecker_Normalize.UnfoldUntil
                  FStar_Syntax_Syntax.Delta_constant] in
         let steps =
           let uu____1045 =
             let uu____1047 = FStar_List.map tr s in
             FStar_List.flatten uu____1047 in
           FStar_List.append
             [FStar_TypeChecker_Normalize.Reify;
             FStar_TypeChecker_Normalize.UnfoldTac] uu____1045 in
         let w =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.witness in
         let t =
           FStar_TypeChecker_Normalize.normalize steps goal.context
             goal.goal_ty in
         replace_cur
           (let uu___91_1053 = goal in
            { context = (uu___91_1053.context); witness = w; goal_ty = t }))
let istrivial: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.UnfoldTac] in
      let t1 = FStar_TypeChecker_Normalize.normalize steps e t in is_true t1
let trivial: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____1065 = istrivial goal.context goal.goal_ty in
       if uu____1065
       then
         let t_unit1 = FStar_TypeChecker_Common.t_unit in
         (solve goal t_unit1; dismiss)
       else
         (let uu____1072 =
            let uu____1073 = FStar_Syntax_Print.term_to_string goal.goal_ty in
            FStar_Util.format1 "Not a trivial goal: %s" uu____1073 in
          fail uu____1072))
let apply: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1080 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1080 with
         | (tm1,t,guard) ->
             let uu____1088 = FStar_Syntax_Util.arrow_formals_comp t in
             (match uu____1088 with
              | (bs,comp) ->
                  let uu____1103 =
                    FStar_List.fold_left
                      (fun uu____1120  ->
                         fun uu____1121  ->
                           match (uu____1120, uu____1121) with
                           | ((uvs,guard1,subst1),(b,aq)) ->
                               let b_t =
                                 FStar_Syntax_Subst.subst subst1
                                   b.FStar_Syntax_Syntax.sort in
                               let uu____1170 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "apply"
                                   (goal.goal_ty).FStar_Syntax_Syntax.pos
                                   goal.context b_t in
                               (match uu____1170 with
                                | (u,uu____1185,g_u) ->
                                    let uu____1193 =
                                      FStar_TypeChecker_Rel.conj_guard guard1
                                        g_u in
                                    (((u, aq) :: uvs), uu____1193,
                                      ((FStar_Syntax_Syntax.NT (b, u)) ::
                                      subst1)))) ([], guard, []) bs in
                  (match uu____1103 with
                   | (uvs,implicits,subst1) ->
                       let uvs1 = FStar_List.rev uvs in
                       let comp1 = FStar_Syntax_Subst.subst_comp subst1 comp in
                       let ret_typ = comp_to_typ comp1 in
                       let uu____1226 =
                         FStar_TypeChecker_Rel.try_teq false goal.context
                           ret_typ goal.goal_ty in
                       (match uu____1226 with
                        | None  ->
                            let uu____1229 =
                              let uu____1230 =
                                FStar_Syntax_Print.term_to_string tm1 in
                              let uu____1231 =
                                FStar_Syntax_Print.term_to_string ret_typ in
                              let uu____1232 =
                                FStar_Syntax_Print.term_to_string
                                  goal.goal_ty in
                              FStar_Util.format3
                                "apply: does not unify with goal: %s : %s vs %s"
                                uu____1230 uu____1231 uu____1232 in
                            fail uu____1229
                        | Some g ->
                            let g1 =
                              let uu____1235 =
                                FStar_TypeChecker_Rel.solve_deferred_constraints
                                  goal.context g in
                              FStar_All.pipe_right uu____1235
                                FStar_TypeChecker_Rel.resolve_implicits in
                            let solution =
                              FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1 None
                                (goal.context).FStar_TypeChecker_Env.range in
                            let implicits1 =
                              FStar_All.pipe_right
                                implicits.FStar_TypeChecker_Env.implicits
                                (FStar_List.filter
                                   (fun uu____1269  ->
                                      match uu____1269 with
                                      | (uu____1276,uu____1277,uu____1278,tm2,uu____1280,uu____1281)
                                          ->
                                          let uu____1282 =
                                            FStar_Syntax_Util.head_and_args
                                              tm2 in
                                          (match uu____1282 with
                                           | (hd1,uu____1293) ->
                                               let uu____1308 =
                                                 let uu____1309 =
                                                   FStar_Syntax_Subst.compress
                                                     hd1 in
                                                 uu____1309.FStar_Syntax_Syntax.n in
                                               (match uu____1308 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    uu____1312 -> true
                                                | uu____1321 -> false)))) in
                            (solve goal solution;
                             (let is_free_uvar uv t1 =
                                let free_uvars =
                                  let uu____1340 =
                                    let uu____1344 =
                                      FStar_Syntax_Free.uvars t1 in
                                    FStar_Util.set_elements uu____1344 in
                                  FStar_List.map FStar_Pervasives.fst
                                    uu____1340 in
                                FStar_List.existsML
                                  (fun u  -> FStar_Unionfind.equivalent u uv)
                                  free_uvars in
                              let appears uv goals =
                                FStar_List.existsML
                                  (fun g'  -> is_free_uvar uv g'.goal_ty)
                                  goals in
                              let checkone t1 goals =
                                let uu____1391 =
                                  FStar_Syntax_Util.head_and_args t1 in
                                match uu____1391 with
                                | (hd1,uu____1402) ->
                                    (match hd1.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (uv,uu____1418) -> appears uv goals
                                     | uu____1431 -> false) in
                              let sub_goals =
                                FStar_All.pipe_right implicits1
                                  (FStar_List.map
                                     (fun uu____1448  ->
                                        match uu____1448 with
                                        | (_msg,_env,_uvar,term,typ,uu____1460)
                                            ->
                                            let uu____1461 =
                                              bnorm goal.context term in
                                            let uu____1462 =
                                              bnorm goal.context typ in
                                            {
                                              context = (goal.context);
                                              witness = uu____1461;
                                              goal_ty = uu____1462
                                            })) in
                              let rec filter' f xs =
                                match xs with
                                | [] -> []
                                | x::xs1 ->
                                    let uu____1494 = f x xs1 in
                                    if uu____1494
                                    then
                                      let uu____1496 = filter' f xs1 in x ::
                                        uu____1496
                                    else filter' f xs1 in
                              let sub_goals1 =
                                filter'
                                  (fun g2  ->
                                     fun goals  ->
                                       let uu____1504 =
                                         checkone g2.witness goals in
                                       Prims.op_Negation uu____1504)
                                  sub_goals in
                              let uu____1505 =
                                add_implicits
                                  g1.FStar_TypeChecker_Env.implicits in
                              bind uu____1505
                                (fun uu____1507  ->
                                   bind dismiss
                                     (fun uu____1508  -> add_goals sub_goals1))))))))
let apply_lemma: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun tm  ->
    bind cur_goal
      (fun goal  ->
         let uu____1515 =
           (goal.context).FStar_TypeChecker_Env.type_of goal.context tm in
         match uu____1515 with
         | (tm1,t,guard) ->
             let uu____1523 = FStar_Syntax_Util.arrow_formals_comp t in
             (match uu____1523 with
              | (bs,comp) ->
                  let uu____1538 =
                    FStar_List.fold_left
                      (fun uu____1555  ->
                         fun uu____1556  ->
                           match (uu____1555, uu____1556) with
                           | ((uvs,guard1,subst1),(b,aq)) ->
                               let b_t =
                                 FStar_Syntax_Subst.subst subst1
                                   b.FStar_Syntax_Syntax.sort in
                               let uu____1605 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "apply"
                                   (goal.goal_ty).FStar_Syntax_Syntax.pos
                                   goal.context b_t in
                               (match uu____1605 with
                                | (u,uu____1620,g_u) ->
                                    let uu____1628 =
                                      FStar_TypeChecker_Rel.conj_guard guard1
                                        g_u in
                                    (((u, aq) :: uvs), uu____1628,
                                      ((FStar_Syntax_Syntax.NT (b, u)) ::
                                      subst1)))) ([], guard, []) bs in
                  (match uu____1538 with
                   | (uvs,implicits,subst1) ->
                       let uvs1 = FStar_List.rev uvs in
                       let comp1 = FStar_Syntax_Subst.subst_comp subst1 comp in
                       let uu____1660 =
                         let uu____1667 =
                           let uu____1673 =
                             FStar_Syntax_Util.comp_to_comp_typ comp1 in
                           uu____1673.FStar_Syntax_Syntax.effect_args in
                         match uu____1667 with
                         | pre::post::uu____1682 -> ((fst pre), (fst post))
                         | uu____1712 ->
                             failwith "apply_lemma: impossible: not a lemma" in
                       (match uu____1660 with
                        | (pre,post) ->
                            let uu____1735 =
                              let uu____1737 =
                                FStar_Syntax_Util.mk_squash post in
                              FStar_TypeChecker_Rel.try_teq false
                                goal.context uu____1737 goal.goal_ty in
                            (match uu____1735 with
                             | None  ->
                                 let uu____1739 =
                                   let uu____1740 =
                                     let uu____1741 =
                                       FStar_Syntax_Util.mk_squash post in
                                     FStar_Syntax_Print.term_to_string
                                       uu____1741 in
                                   let uu____1742 =
                                     FStar_Syntax_Print.term_to_string
                                       goal.goal_ty in
                                   FStar_Util.format2
                                     "apply_lemma: does not unify with goal: %s vs %s"
                                     uu____1740 uu____1742 in
                                 fail uu____1739
                             | Some g ->
                                 let g1 =
                                   let uu____1745 =
                                     FStar_TypeChecker_Rel.solve_deferred_constraints
                                       goal.context g in
                                   FStar_All.pipe_right uu____1745
                                     FStar_TypeChecker_Rel.resolve_implicits in
                                 let solution =
                                   FStar_Syntax_Syntax.mk_Tm_app tm1 uvs1
                                     None
                                     (goal.context).FStar_TypeChecker_Env.range in
                                 let implicits1 =
                                   FStar_All.pipe_right
                                     implicits.FStar_TypeChecker_Env.implicits
                                     (FStar_List.filter
                                        (fun uu____1779  ->
                                           match uu____1779 with
                                           | (uu____1786,uu____1787,uu____1788,tm2,uu____1790,uu____1791)
                                               ->
                                               let uu____1792 =
                                                 FStar_Syntax_Util.head_and_args
                                                   tm2 in
                                               (match uu____1792 with
                                                | (hd1,uu____1803) ->
                                                    let uu____1818 =
                                                      let uu____1819 =
                                                        FStar_Syntax_Subst.compress
                                                          hd1 in
                                                      uu____1819.FStar_Syntax_Syntax.n in
                                                    (match uu____1818 with
                                                     | FStar_Syntax_Syntax.Tm_uvar
                                                         uu____1822 -> true
                                                     | uu____1831 -> false)))) in
                                 (solve goal solution;
                                  (let is_free_uvar uv t1 =
                                     let free_uvars =
                                       let uu____1850 =
                                         let uu____1854 =
                                           FStar_Syntax_Free.uvars t1 in
                                         FStar_Util.set_elements uu____1854 in
                                       FStar_List.map FStar_Pervasives.fst
                                         uu____1850 in
                                     FStar_List.existsML
                                       (fun u  ->
                                          FStar_Unionfind.equivalent u uv)
                                       free_uvars in
                                   let appears uv goals =
                                     FStar_List.existsML
                                       (fun g'  -> is_free_uvar uv g'.goal_ty)
                                       goals in
                                   let checkone t1 goals =
                                     let uu____1901 =
                                       FStar_Syntax_Util.head_and_args t1 in
                                     match uu____1901 with
                                     | (hd1,uu____1912) ->
                                         (match hd1.FStar_Syntax_Syntax.n
                                          with
                                          | FStar_Syntax_Syntax.Tm_uvar
                                              (uv,uu____1928) ->
                                              appears uv goals
                                          | uu____1941 -> false) in
                                   let sub_goals =
                                     FStar_All.pipe_right implicits1
                                       (FStar_List.map
                                          (fun uu____1958  ->
                                             match uu____1958 with
                                             | (_msg,_env,_uvar,term,typ,uu____1970)
                                                 ->
                                                 let uu____1971 =
                                                   bnorm goal.context term in
                                                 let uu____1972 =
                                                   bnorm goal.context typ in
                                                 {
                                                   context = (goal.context);
                                                   witness = uu____1971;
                                                   goal_ty = uu____1972
                                                 })) in
                                   let rec filter' f xs =
                                     match xs with
                                     | [] -> []
                                     | x::xs1 ->
                                         let uu____2004 = f x xs1 in
                                         if uu____2004
                                         then
                                           let uu____2006 = filter' f xs1 in
                                           x :: uu____2006
                                         else filter' f xs1 in
                                   let sub_goals1 =
                                     filter'
                                       (fun g2  ->
                                          fun goals  ->
                                            let uu____2014 =
                                              checkone g2.witness goals in
                                            Prims.op_Negation uu____2014)
                                       sub_goals in
                                   let pregoal =
                                     mk_irrelevant goal.context pre in
                                   let sub_goals2 =
                                     let uu____2018 =
                                       istrivial goal.context pregoal.goal_ty in
                                     if uu____2018
                                     then sub_goals1
                                     else pregoal :: sub_goals1 in
                                   let uu____2021 =
                                     add_implicits
                                       g1.FStar_TypeChecker_Env.implicits in
                                   bind uu____2021
                                     (fun uu____2023  ->
                                        bind dismiss
                                          (fun uu____2024  ->
                                             add_goals sub_goals2)))))))))
let exact: FStar_Syntax_Syntax.term -> Prims.unit tac =
  fun t  ->
    bind cur_goal
      (fun goal  ->
         try
           let uu____2034 =
             (goal.context).FStar_TypeChecker_Env.type_of goal.context t in
           match uu____2034 with
           | (t1,typ,guard) ->
               let uu____2042 =
                 FStar_TypeChecker_Rel.teq_nosmt goal.context typ
                   goal.goal_ty in
               if uu____2042
               then (solve goal t1; dismiss)
               else
                 (let msg =
                    let uu____2047 = FStar_Syntax_Print.term_to_string t1 in
                    let uu____2048 =
                      let uu____2049 = bnorm goal.context typ in
                      FStar_Syntax_Print.term_to_string uu____2049 in
                    let uu____2050 =
                      FStar_Syntax_Print.term_to_string goal.goal_ty in
                    FStar_Util.format3
                      "%s : %s does not exactly solve the goal %s" uu____2047
                      uu____2048 uu____2050 in
                  fail msg)
         with
         | e ->
             let uu____2054 =
               let uu____2055 = FStar_Syntax_Print.term_to_string t in
               let uu____2056 = FStar_Syntax_Print.tag_of_term t in
               FStar_Util.format2 "Term is not typeable: %s (%s)" uu____2055
                 uu____2056 in
             fail uu____2054)
let rewrite: FStar_Syntax_Syntax.binder -> Prims.unit tac =
  fun h  ->
    bind cur_goal
      (fun goal  ->
         let uu____2063 =
           FStar_All.pipe_left mlog
             (fun uu____2068  ->
                let uu____2069 = FStar_Syntax_Print.bv_to_string (fst h) in
                let uu____2070 =
                  FStar_Syntax_Print.term_to_string
                    (fst h).FStar_Syntax_Syntax.sort in
                FStar_Util.print2 "+++Rewrite %s : %s\n" uu____2069
                  uu____2070) in
         bind uu____2063
           (fun uu____2071  ->
              let uu____2072 =
                let uu____2074 =
                  let uu____2075 =
                    FStar_TypeChecker_Env.lookup_bv goal.context (fst h) in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____2075 in
                FStar_Syntax_Util.destruct_typ_as_formula uu____2074 in
              match uu____2072 with
              | Some (FStar_Syntax_Util.BaseConn
                  (l,uu____2082::(x,uu____2084)::(e,uu____2086)::[])) when
                  FStar_Ident.lid_equals l FStar_Syntax_Const.eq2_lid ->
                  let uu____2120 =
                    let uu____2121 = FStar_Syntax_Subst.compress x in
                    uu____2121.FStar_Syntax_Syntax.n in
                  (match uu____2120 with
                   | FStar_Syntax_Syntax.Tm_name x1 ->
                       let goal1 =
                         let uu___94_2127 = goal in
                         let uu____2128 =
                           FStar_Syntax_Subst.subst
                             [FStar_Syntax_Syntax.NT (x1, e)] goal.goal_ty in
                         {
                           context = (uu___94_2127.context);
                           witness = (uu___94_2127.witness);
                           goal_ty = uu____2128
                         } in
                       replace_cur goal1
                   | uu____2131 ->
                       fail
                         "Not an equality hypothesis with a variable on the LHS")
              | uu____2132 -> fail "Not an equality hypothesis"))
let clear: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2136 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2136 with
       | None  -> fail "Cannot clear; empty context"
       | Some (x,env') ->
           let fns_ty = FStar_Syntax_Free.names goal.goal_ty in
           let fns_tm = FStar_Syntax_Free.names goal.witness in
           let uu____2151 = FStar_Util.set_mem x fns_ty in
           if uu____2151
           then fail "Cannot clear; variable appears in goal"
           else
             (let uu____2154 = FStar_Util.set_mem x fns_tm in
              if uu____2154
              then fail "Cannot clear; variable appears in witness"
              else
                (let new_goal =
                   let uu___95_2158 = goal in
                   {
                     context = env';
                     witness = (uu___95_2158.witness);
                     goal_ty = (uu___95_2158.goal_ty)
                   } in
                 bind dismiss (fun uu____2159  -> add_goals [new_goal]))))
let clear_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2166 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2166 with
         | None  -> fail "Cannot clear_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then fail "Cannot clear_hd; head variable mismatch"
             else clear)
let revert: Prims.unit tac =
  bind cur_goal
    (fun goal  ->
       let uu____2181 = FStar_TypeChecker_Env.pop_bv goal.context in
       match uu____2181 with
       | None  -> fail "Cannot revert; empty context"
       | Some (x,env') ->
           let typ' =
             let uu____2195 = FStar_Syntax_Syntax.mk_Total goal.goal_ty in
             FStar_Syntax_Util.arrow [(x, None)] uu____2195 in
           let w' = FStar_Syntax_Util.abs [(x, None)] goal.witness None in
           replace_cur
             (let uu___96_2218 = goal in
              { context = env'; witness = w'; goal_ty = typ' }))
let revert_hd: name -> Prims.unit tac =
  fun x  ->
    bind cur_goal
      (fun goal  ->
         let uu____2225 = FStar_TypeChecker_Env.pop_bv goal.context in
         match uu____2225 with
         | None  -> fail "Cannot revert_hd; empty context"
         | Some (y,env') ->
             if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
             then
               let uu____2237 =
                 let uu____2238 = FStar_Syntax_Print.bv_to_string x in
                 let uu____2239 = FStar_Syntax_Print.bv_to_string y in
                 FStar_Util.format2
                   "Cannot revert_hd %s; head variable mismatch ... egot %s"
                   uu____2238 uu____2239 in
               fail uu____2237
             else revert)
let rec revert_all_hd: name Prims.list -> Prims.unit tac =
  fun xs  ->
    match xs with
    | [] -> ret ()
    | x::xs1 ->
        let uu____2252 = revert_all_hd xs1 in
        bind uu____2252 (fun uu____2254  -> revert_hd x)
let prune: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.rem_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___97_2264 = g in
           {
             context = ctx';
             witness = (uu___97_2264.witness);
             goal_ty = (uu___97_2264.goal_ty)
           } in
         bind dismiss (fun uu____2265  -> add_goals [g']))
let addns: Prims.string -> Prims.unit tac =
  fun s  ->
    bind cur_goal
      (fun g  ->
         let ctx = g.context in
         let ctx' =
           FStar_TypeChecker_Env.add_proof_ns ctx
             (FStar_Ident.path_of_text s) in
         let g' =
           let uu___98_2275 = g in
           {
             context = ctx';
             witness = (uu___98_2275.witness);
             goal_ty = (uu___98_2275.goal_ty)
           } in
         bind dismiss (fun uu____2276  -> add_goals [g']))
let rec bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2297 = FStar_Syntax_Subst.compress t in
          uu____2297.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = bottom_fold_env f env in
              let uu____2320 =
                let uu____2330 = ff hd1 in
                let uu____2331 =
                  FStar_List.map
                    (fun uu____2339  ->
                       match uu____2339 with
                       | (a,q) -> let uu____2346 = ff a in (uu____2346, q))
                    args in
                (uu____2330, uu____2331) in
              FStar_Syntax_Syntax.Tm_app uu____2320
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2375 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2375 with
               | (bs1,t') ->
                   let t'' =
                     let uu____2381 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     bottom_fold_env f uu____2381 t' in
                   let uu____2382 =
                     let uu____2397 = FStar_Syntax_Subst.close bs1 t'' in
                     (bs1, uu____2397, k) in
                   FStar_Syntax_Syntax.Tm_abs uu____2382)
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
          | uu____2416 -> tn in
        f env
          (let uu___99_2417 = t in
           {
             FStar_Syntax_Syntax.n = tn1;
             FStar_Syntax_Syntax.tk = (uu___99_2417.FStar_Syntax_Syntax.tk);
             FStar_Syntax_Syntax.pos = (uu___99_2417.FStar_Syntax_Syntax.pos);
             FStar_Syntax_Syntax.vars =
               (uu___99_2417.FStar_Syntax_Syntax.vars)
           })
let rec mapM f l =
  match l with
  | [] -> ret []
  | x::xs ->
      let uu____2451 = f x in
      bind uu____2451
        (fun y  ->
           let uu____2455 = mapM f xs in
           bind uu____2455 (fun ys  -> ret (y :: ys)))
let rec tac_bottom_fold_env:
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun f  ->
    fun env  ->
      fun t  ->
        let tn =
          let uu____2487 = FStar_Syntax_Subst.compress t in
          uu____2487.FStar_Syntax_Syntax.n in
        let tn1 =
          match tn with
          | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
              let ff = tac_bottom_fold_env f env in
              let uu____2513 = ff hd1 in
              bind uu____2513
                (fun hd2  ->
                   let fa uu____2524 =
                     match uu____2524 with
                     | (a,q) ->
                         let uu____2532 = ff a in
                         bind uu____2532 (fun a1  -> ret (a1, q)) in
                   let uu____2539 = mapM fa args in
                   bind uu____2539
                     (fun args1  ->
                        ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
          | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
              let uu____2583 = FStar_Syntax_Subst.open_term bs t1 in
              (match uu____2583 with
               | (bs1,t') ->
                   let uu____2589 =
                     let uu____2591 =
                       FStar_TypeChecker_Env.push_binders env bs1 in
                     tac_bottom_fold_env f uu____2591 t' in
                   bind uu____2589
                     (fun t''  ->
                        let uu____2593 =
                          let uu____2594 =
                            let uu____2609 = FStar_Syntax_Subst.close bs1 t'' in
                            (bs1, uu____2609, k) in
                          FStar_Syntax_Syntax.Tm_abs uu____2594 in
                        ret uu____2593))
          | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
          | uu____2628 -> ret tn in
        bind tn1
          (fun tn2  ->
             f env
               (let uu___100_2630 = t in
                {
                  FStar_Syntax_Syntax.n = tn2;
                  FStar_Syntax_Syntax.tk =
                    (uu___100_2630.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos =
                    (uu___100_2630.FStar_Syntax_Syntax.pos);
                  FStar_Syntax_Syntax.vars =
                    (uu___100_2630.FStar_Syntax_Syntax.vars)
                }))
let pointwise_rec:
  proofstate ->
    Prims.unit tac ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac
  =
  fun ps  ->
    fun tau  ->
      fun env  ->
        fun t  ->
          let uu____2651 = FStar_TypeChecker_TcTerm.tc_term env t in
          match uu____2651 with
          | (t1,lcomp,g) ->
              let uu____2659 =
                (let uu____2660 = FStar_Syntax_Util.is_total_lcomp lcomp in
                 Prims.op_Negation uu____2660) ||
                  (let uu____2661 = FStar_TypeChecker_Rel.is_trivial g in
                   Prims.op_Negation uu____2661) in
              if uu____2659
              then ret t1
              else
                (let typ = lcomp.FStar_Syntax_Syntax.res_typ in
                 let uu____2667 =
                   FStar_TypeChecker_Util.new_implicit_var "pointwise tactic"
                     t1.FStar_Syntax_Syntax.pos env typ in
                 match uu____2667 with
                 | (ut,uvs,guard) ->
                     (log ps
                        (fun uu____2685  ->
                           let uu____2686 =
                             FStar_Syntax_Print.term_to_string t1 in
                           let uu____2687 =
                             FStar_Syntax_Print.term_to_string ut in
                           FStar_Util.print2
                             "Pointwise_rec: making equality %s = %s\n"
                             uu____2686 uu____2687);
                      (let g' =
                         let uu____2689 =
                           let uu____2690 =
                             FStar_TypeChecker_TcTerm.universe_of env typ in
                           FStar_Syntax_Util.mk_eq2 uu____2690 typ t1 ut in
                         mk_irrelevant env uu____2689 in
                       let uu____2691 = add_goals [g'] in
                       bind uu____2691
                         (fun uu____2693  ->
                            let uu____2694 =
                              bind tau
                                (fun uu____2696  ->
                                   let guard1 =
                                     let uu____2698 =
                                       FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env guard in
                                     FStar_All.pipe_right uu____2698
                                       FStar_TypeChecker_Rel.resolve_implicits in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env guard1;
                                   (let ut1 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Normalize.WHNF]
                                        env ut in
                                    ret ut1)) in
                            focus_cur_goal uu____2694))))
let pointwise: Prims.unit tac -> Prims.unit tac =
  fun tau  ->
    bind get
      (fun ps  ->
         let uu____2709 =
           match ps.goals with
           | g::gs -> (g, gs)
           | [] -> failwith "Pointwise: no goals" in
         match uu____2709 with
         | (g,gs) ->
             let gt1 = g.goal_ty in
             (log ps
                (fun uu____2730  ->
                   let uu____2731 = FStar_Syntax_Print.term_to_string gt1 in
                   FStar_Util.print1 "Pointwise starting with %s\n"
                     uu____2731);
              bind dismiss_all
                (fun uu____2732  ->
                   let uu____2733 =
                     tac_bottom_fold_env (pointwise_rec ps tau) g.context gt1 in
                   bind uu____2733
                     (fun gt'  ->
                        log ps
                          (fun uu____2737  ->
                             let uu____2738 =
                               FStar_Syntax_Print.term_to_string gt' in
                             FStar_Util.print1
                               "Pointwise seems to have succeded with %s\n"
                               uu____2738);
                        (let uu____2739 = push_goals gs in
                         bind uu____2739
                           (fun uu____2741  ->
                              add_goals
                                [(let uu___101_2742 = g in
                                  {
                                    context = (uu___101_2742.context);
                                    witness = (uu___101_2742.witness);
                                    goal_ty = gt'
                                  })]))))))
let trefl: Prims.unit tac =
  bind cur_goal
    (fun g  ->
       let uu____2745 = FStar_Syntax_Util.un_squash g.goal_ty in
       match uu____2745 with
       | Some t ->
           let uu____2755 = FStar_Syntax_Util.head_and_args' t in
           (match uu____2755 with
            | (hd1,args) ->
                let uu____2776 =
                  let uu____2784 =
                    let uu____2785 = FStar_Syntax_Util.un_uinst hd1 in
                    uu____2785.FStar_Syntax_Syntax.n in
                  (uu____2784, args) in
                (match uu____2776 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____2795::(l,uu____2797)::(r,uu____2799)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.eq2_lid
                     ->
                     let uu____2833 =
                       let uu____2834 =
                         FStar_TypeChecker_Rel.teq_nosmt g.context l r in
                       Prims.op_Negation uu____2834 in
                     if uu____2833
                     then
                       let uu____2836 =
                         let uu____2837 = FStar_Syntax_Print.term_to_string l in
                         let uu____2838 = FStar_Syntax_Print.term_to_string r in
                         FStar_Util.format2
                           "trefl: not a trivial equality (%s vs %s)"
                           uu____2837 uu____2838 in
                       fail uu____2836
                     else
                       (let t_unit1 = FStar_TypeChecker_Common.t_unit in
                        solve g t_unit1; dismiss)
                 | (hd2,uu____2845) ->
                     let uu____2856 =
                       let uu____2857 = FStar_Syntax_Print.term_to_string t in
                       FStar_Util.format1 "trefl: not an equality (%s)"
                         uu____2857 in
                     fail uu____2856))
       | None  -> fail "not an irrelevant goal")
let flip: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | g1::g2::gs ->
           set
             (let uu___102_2867 = ps in
              {
                main_context = (uu___102_2867.main_context);
                main_goal = (uu___102_2867.main_goal);
                all_implicits = (uu___102_2867.all_implicits);
                goals = (g2 :: g1 :: gs);
                smt_goals = (uu___102_2867.smt_goals)
              })
       | uu____2868 -> fail "flip: less than 2 goals")
let later: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with
       | [] -> ret ()
       | g::gs ->
           set
             (let uu___103_2876 = ps in
              {
                main_context = (uu___103_2876.main_context);
                main_goal = (uu___103_2876.main_goal);
                all_implicits = (uu___103_2876.all_implicits);
                goals = (FStar_List.append gs [g]);
                smt_goals = (uu___103_2876.smt_goals)
              }))
let qed: Prims.unit tac =
  bind get
    (fun ps  ->
       match ps.goals with | [] -> ret () | uu____2880 -> fail "Not done!")
let cases:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) tac
  =
  fun t  ->
    bind cur_goal
      (fun g  ->
         let uu____2894 =
           (g.context).FStar_TypeChecker_Env.type_of g.context t in
         match uu____2894 with
         | (t1,typ,guard) ->
             let uu____2904 = FStar_Syntax_Util.head_and_args typ in
             (match uu____2904 with
              | (hd1,args) ->
                  let uu____2933 =
                    let uu____2941 =
                      let uu____2942 = FStar_Syntax_Util.un_uinst hd1 in
                      uu____2942.FStar_Syntax_Syntax.n in
                    (uu____2941, args) in
                  (match uu____2933 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,(p,uu____2955)::(q,uu____2957)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.or_lid
                       ->
                       let v_p = FStar_Syntax_Syntax.new_bv None p in
                       let v_q = FStar_Syntax_Syntax.new_bv None q in
                       let g1 =
                         let uu___104_2986 = g in
                         let uu____2987 =
                           FStar_TypeChecker_Env.push_bv g.context v_p in
                         {
                           context = uu____2987;
                           witness = (uu___104_2986.witness);
                           goal_ty = (uu___104_2986.goal_ty)
                         } in
                       let g2 =
                         let uu___105_2989 = g in
                         let uu____2990 =
                           FStar_TypeChecker_Env.push_bv g.context v_q in
                         {
                           context = uu____2990;
                           witness = (uu___105_2989.witness);
                           goal_ty = (uu___105_2989.goal_ty)
                         } in
                       bind dismiss
                         (fun uu____2993  ->
                            let uu____2994 = add_goals [g1; g2] in
                            bind uu____2994
                              (fun uu____2998  ->
                                 let uu____2999 =
                                   let uu____3002 =
                                     FStar_Syntax_Syntax.bv_to_name v_p in
                                   let uu____3003 =
                                     FStar_Syntax_Syntax.bv_to_name v_q in
                                   (uu____3002, uu____3003) in
                                 ret uu____2999))
                   | uu____3006 ->
                       let uu____3014 =
                         let uu____3015 =
                           FStar_Syntax_Print.term_to_string typ in
                         FStar_Util.format1 "Not a disjunction: %s"
                           uu____3015 in
                       fail uu____3014)))
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____3021 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____3025 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____3029 -> false
let order_binder:
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder -> order =
  fun x  ->
    fun y  ->
      let n1 = FStar_Syntax_Syntax.order_bv (fst x) (fst y) in
      if n1 < (Prims.parse_int "0")
      then Lt
      else if n1 = (Prims.parse_int "0") then Eq else Gt
let proofstate_of_goal_ty: env -> FStar_Syntax_Syntax.term -> proofstate =
  fun env  ->
    fun g  ->
      let g1 = let uu____3046 = bnorm env g in mk_irrelevant env uu____3046 in
      {
        main_context = env;
        main_goal = g1;
        all_implicits = [];
        goals = [g1];
        smt_goals = []
      }
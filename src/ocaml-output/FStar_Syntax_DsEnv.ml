open Prims
type local_binding = (FStar_Ident.ident * FStar_Syntax_Syntax.bv)
type rec_binding =
  (FStar_Ident.ident * FStar_Ident.lid * FStar_Syntax_Syntax.delta_depth)
type module_abbrev = (FStar_Ident.ident * FStar_Ident.lident)
type open_kind =
  | Open_module 
  | Open_namespace 
let (uu___is_Open_module : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_module  -> true | uu____23 -> false
  
let (uu___is_Open_namespace : open_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Open_namespace  -> true | uu____34 -> false
  
type open_module_or_namespace = (FStar_Ident.lident * open_kind)
type record_or_dc =
  {
  typename: FStar_Ident.lident ;
  constrname: FStar_Ident.ident ;
  parms: FStar_Syntax_Syntax.binders ;
  fields: (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list ;
  is_private_or_abstract: Prims.bool ;
  is_record: Prims.bool }
let (__proj__Mkrecord_or_dc__item__typename :
  record_or_dc -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> typename
  
let (__proj__Mkrecord_or_dc__item__constrname :
  record_or_dc -> FStar_Ident.ident) =
  fun projectee  ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> constrname
  
let (__proj__Mkrecord_or_dc__item__parms :
  record_or_dc -> FStar_Syntax_Syntax.binders) =
  fun projectee  ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> parms
  
let (__proj__Mkrecord_or_dc__item__fields :
  record_or_dc -> (FStar_Ident.ident * FStar_Syntax_Syntax.typ) Prims.list) =
  fun projectee  ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> fields
  
let (__proj__Mkrecord_or_dc__item__is_private_or_abstract :
  record_or_dc -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> is_private_or_abstract
  
let (__proj__Mkrecord_or_dc__item__is_record : record_or_dc -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { typename; constrname; parms; fields; is_private_or_abstract;
        is_record;_} -> is_record
  
type scope_mod =
  | Local_binding of local_binding 
  | Rec_binding of rec_binding 
  | Module_abbrev of module_abbrev 
  | Open_module_or_namespace of open_module_or_namespace 
  | Top_level_def of FStar_Ident.ident 
  | Record_or_dc of record_or_dc 
let (uu___is_Local_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Local_binding _0 -> true | uu____254 -> false
  
let (__proj__Local_binding__item___0 : scope_mod -> local_binding) =
  fun projectee  -> match projectee with | Local_binding _0 -> _0 
let (uu___is_Rec_binding : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec_binding _0 -> true | uu____274 -> false
  
let (__proj__Rec_binding__item___0 : scope_mod -> rec_binding) =
  fun projectee  -> match projectee with | Rec_binding _0 -> _0 
let (uu___is_Module_abbrev : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Module_abbrev _0 -> true | uu____294 -> false
  
let (__proj__Module_abbrev__item___0 : scope_mod -> module_abbrev) =
  fun projectee  -> match projectee with | Module_abbrev _0 -> _0 
let (uu___is_Open_module_or_namespace : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Open_module_or_namespace _0 -> true
    | uu____314 -> false
  
let (__proj__Open_module_or_namespace__item___0 :
  scope_mod -> open_module_or_namespace) =
  fun projectee  -> match projectee with | Open_module_or_namespace _0 -> _0 
let (uu___is_Top_level_def : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Top_level_def _0 -> true | uu____334 -> false
  
let (__proj__Top_level_def__item___0 : scope_mod -> FStar_Ident.ident) =
  fun projectee  -> match projectee with | Top_level_def _0 -> _0 
let (uu___is_Record_or_dc : scope_mod -> Prims.bool) =
  fun projectee  ->
    match projectee with | Record_or_dc _0 -> true | uu____354 -> false
  
let (__proj__Record_or_dc__item___0 : scope_mod -> record_or_dc) =
  fun projectee  -> match projectee with | Record_or_dc _0 -> _0 
type string_set = Prims.string FStar_Util.set
type exported_id_kind =
  | Exported_id_term_type 
  | Exported_id_field 
let (uu___is_Exported_id_term_type : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Exported_id_term_type  -> true
    | uu____376 -> false
  
let (uu___is_Exported_id_field : exported_id_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exported_id_field  -> true | uu____387 -> false
  
type exported_id_set = exported_id_kind -> string_set FStar_ST.ref
type env =
  {
  curmodule: FStar_Ident.lident FStar_Pervasives_Native.option ;
  curmonad: FStar_Ident.ident FStar_Pervasives_Native.option ;
  modules: (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list ;
  scope_mods: scope_mod Prims.list ;
  exported_ids: exported_id_set FStar_Util.smap ;
  trans_exported_ids: exported_id_set FStar_Util.smap ;
  includes: FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap ;
  sigaccum: FStar_Syntax_Syntax.sigelts ;
  sigmap: (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap ;
  iface: Prims.bool ;
  admitted_iface: Prims.bool ;
  expect_typ: Prims.bool ;
  docs: FStar_Parser_AST.fsdoc FStar_Util.smap ;
  remaining_iface_decls:
    (FStar_Ident.lident * FStar_Parser_AST.decl Prims.list) Prims.list ;
  syntax_only: Prims.bool ;
  ds_hooks: dsenv_hooks ;
  dep_graph: FStar_Parser_Dep.deps }
and dsenv_hooks =
  {
  ds_push_open_hook: env -> open_module_or_namespace -> unit ;
  ds_push_include_hook: env -> FStar_Ident.lident -> unit ;
  ds_push_module_abbrev_hook:
    env -> FStar_Ident.ident -> FStar_Ident.lident -> unit }
let (__proj__Mkenv__item__curmodule :
  env -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> curmodule
  
let (__proj__Mkenv__item__curmonad :
  env -> FStar_Ident.ident FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> curmonad
  
let (__proj__Mkenv__item__modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> modules
  
let (__proj__Mkenv__item__scope_mods : env -> scope_mod Prims.list) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> scope_mods
  
let (__proj__Mkenv__item__exported_ids :
  env -> exported_id_set FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> exported_ids
  
let (__proj__Mkenv__item__trans_exported_ids :
  env -> exported_id_set FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> trans_exported_ids
  
let (__proj__Mkenv__item__includes :
  env -> FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> includes
  
let (__proj__Mkenv__item__sigaccum : env -> FStar_Syntax_Syntax.sigelts) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> sigaccum
  
let (__proj__Mkenv__item__sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> sigmap
  
let (__proj__Mkenv__item__iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> iface
  
let (__proj__Mkenv__item__admitted_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> admitted_iface
  
let (__proj__Mkenv__item__expect_typ : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> expect_typ
  
let (__proj__Mkenv__item__docs :
  env -> FStar_Parser_AST.fsdoc FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> docs
  
let (__proj__Mkenv__item__remaining_iface_decls :
  env -> (FStar_Ident.lident * FStar_Parser_AST.decl Prims.list) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> remaining_iface_decls
  
let (__proj__Mkenv__item__syntax_only : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> syntax_only
  
let (__proj__Mkenv__item__ds_hooks : env -> dsenv_hooks) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> ds_hooks
  
let (__proj__Mkenv__item__dep_graph : env -> FStar_Parser_Dep.deps) =
  fun projectee  ->
    match projectee with
    | { curmodule; curmonad; modules; scope_mods; exported_ids;
        trans_exported_ids; includes; sigaccum; sigmap; iface;
        admitted_iface; expect_typ; docs; remaining_iface_decls; syntax_only;
        ds_hooks; dep_graph;_} -> dep_graph
  
let (__proj__Mkdsenv_hooks__item__ds_push_open_hook :
  dsenv_hooks -> env -> open_module_or_namespace -> unit) =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook; ds_push_include_hook;
        ds_push_module_abbrev_hook;_} -> ds_push_open_hook
  
let (__proj__Mkdsenv_hooks__item__ds_push_include_hook :
  dsenv_hooks -> env -> FStar_Ident.lident -> unit) =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook; ds_push_include_hook;
        ds_push_module_abbrev_hook;_} -> ds_push_include_hook
  
let (__proj__Mkdsenv_hooks__item__ds_push_module_abbrev_hook :
  dsenv_hooks -> env -> FStar_Ident.ident -> FStar_Ident.lident -> unit) =
  fun projectee  ->
    match projectee with
    | { ds_push_open_hook; ds_push_include_hook;
        ds_push_module_abbrev_hook;_} -> ds_push_module_abbrev_hook
  
type 'a withenv = env -> ('a * env)
let (default_ds_hooks : dsenv_hooks) =
  {
    ds_push_open_hook = (fun uu____2007  -> fun uu____2008  -> ());
    ds_push_include_hook = (fun uu____2011  -> fun uu____2012  -> ());
    ds_push_module_abbrev_hook =
      (fun uu____2016  -> fun uu____2017  -> fun uu____2018  -> ())
  } 
type foundname =
  | Term_name of (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute
  Prims.list) 
  | Eff_name of (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident) 
let (uu___is_Term_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Term_name _0 -> true | uu____2055 -> false
  
let (__proj__Term_name__item___0 :
  foundname ->
    (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.attribute Prims.list))
  = fun projectee  -> match projectee with | Term_name _0 -> _0 
let (uu___is_Eff_name : foundname -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eff_name _0 -> true | uu____2097 -> false
  
let (__proj__Eff_name__item___0 :
  foundname -> (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)) =
  fun projectee  -> match projectee with | Eff_name _0 -> _0 
let (set_iface : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___204_2132 = env  in
      {
        curmodule = (uu___204_2132.curmodule);
        curmonad = (uu___204_2132.curmonad);
        modules = (uu___204_2132.modules);
        scope_mods = (uu___204_2132.scope_mods);
        exported_ids = (uu___204_2132.exported_ids);
        trans_exported_ids = (uu___204_2132.trans_exported_ids);
        includes = (uu___204_2132.includes);
        sigaccum = (uu___204_2132.sigaccum);
        sigmap = (uu___204_2132.sigmap);
        iface = b;
        admitted_iface = (uu___204_2132.admitted_iface);
        expect_typ = (uu___204_2132.expect_typ);
        docs = (uu___204_2132.docs);
        remaining_iface_decls = (uu___204_2132.remaining_iface_decls);
        syntax_only = (uu___204_2132.syntax_only);
        ds_hooks = (uu___204_2132.ds_hooks);
        dep_graph = (uu___204_2132.dep_graph)
      }
  
let (iface : env -> Prims.bool) = fun e  -> e.iface 
let (set_admitted_iface : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___205_2153 = e  in
      {
        curmodule = (uu___205_2153.curmodule);
        curmonad = (uu___205_2153.curmonad);
        modules = (uu___205_2153.modules);
        scope_mods = (uu___205_2153.scope_mods);
        exported_ids = (uu___205_2153.exported_ids);
        trans_exported_ids = (uu___205_2153.trans_exported_ids);
        includes = (uu___205_2153.includes);
        sigaccum = (uu___205_2153.sigaccum);
        sigmap = (uu___205_2153.sigmap);
        iface = (uu___205_2153.iface);
        admitted_iface = b;
        expect_typ = (uu___205_2153.expect_typ);
        docs = (uu___205_2153.docs);
        remaining_iface_decls = (uu___205_2153.remaining_iface_decls);
        syntax_only = (uu___205_2153.syntax_only);
        ds_hooks = (uu___205_2153.ds_hooks);
        dep_graph = (uu___205_2153.dep_graph)
      }
  
let (admitted_iface : env -> Prims.bool) = fun e  -> e.admitted_iface 
let (set_expect_typ : env -> Prims.bool -> env) =
  fun e  ->
    fun b  ->
      let uu___206_2174 = e  in
      {
        curmodule = (uu___206_2174.curmodule);
        curmonad = (uu___206_2174.curmonad);
        modules = (uu___206_2174.modules);
        scope_mods = (uu___206_2174.scope_mods);
        exported_ids = (uu___206_2174.exported_ids);
        trans_exported_ids = (uu___206_2174.trans_exported_ids);
        includes = (uu___206_2174.includes);
        sigaccum = (uu___206_2174.sigaccum);
        sigmap = (uu___206_2174.sigmap);
        iface = (uu___206_2174.iface);
        admitted_iface = (uu___206_2174.admitted_iface);
        expect_typ = b;
        docs = (uu___206_2174.docs);
        remaining_iface_decls = (uu___206_2174.remaining_iface_decls);
        syntax_only = (uu___206_2174.syntax_only);
        ds_hooks = (uu___206_2174.ds_hooks);
        dep_graph = (uu___206_2174.dep_graph)
      }
  
let (expect_typ : env -> Prims.bool) = fun e  -> e.expect_typ 
let (all_exported_id_kinds : exported_id_kind Prims.list) =
  [Exported_id_field; Exported_id_term_type] 
let (transitive_exported_ids :
  env -> FStar_Ident.lident -> Prims.string Prims.list) =
  fun env  ->
    fun lid  ->
      let module_name = FStar_Ident.string_of_lid lid  in
      let uu____2201 =
        FStar_Util.smap_try_find env.trans_exported_ids module_name  in
      match uu____2201 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some exported_id_set ->
          let uu____2214 =
            let uu____2218 = exported_id_set Exported_id_term_type  in
            FStar_ST.op_Bang uu____2218  in
          FStar_All.pipe_right uu____2214 FStar_Util.set_elements
  
let (open_modules :
  env -> (FStar_Ident.lident * FStar_Syntax_Syntax.modul) Prims.list) =
  fun e  -> e.modules 
let (open_modules_and_namespaces : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    FStar_List.filter_map
      (fun uu___171_2359  ->
         match uu___171_2359 with
         | Open_module_or_namespace (lid,_info) ->
             FStar_Pervasives_Native.Some lid
         | uu____2364 -> FStar_Pervasives_Native.None) env.scope_mods
  
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun e  ->
    fun l  ->
      let uu___207_2376 = e  in
      {
        curmodule = (FStar_Pervasives_Native.Some l);
        curmonad = (uu___207_2376.curmonad);
        modules = (uu___207_2376.modules);
        scope_mods = (uu___207_2376.scope_mods);
        exported_ids = (uu___207_2376.exported_ids);
        trans_exported_ids = (uu___207_2376.trans_exported_ids);
        includes = (uu___207_2376.includes);
        sigaccum = (uu___207_2376.sigaccum);
        sigmap = (uu___207_2376.sigmap);
        iface = (uu___207_2376.iface);
        admitted_iface = (uu___207_2376.admitted_iface);
        expect_typ = (uu___207_2376.expect_typ);
        docs = (uu___207_2376.docs);
        remaining_iface_decls = (uu___207_2376.remaining_iface_decls);
        syntax_only = (uu___207_2376.syntax_only);
        ds_hooks = (uu___207_2376.ds_hooks);
        dep_graph = (uu___207_2376.dep_graph)
      }
  
let (current_module : env -> FStar_Ident.lident) =
  fun env  ->
    match env.curmodule with
    | FStar_Pervasives_Native.None  -> failwith "Unset current module"
    | FStar_Pervasives_Native.Some m -> m
  
let (iface_decls :
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.decl Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____2400 =
        FStar_All.pipe_right env.remaining_iface_decls
          (FStar_List.tryFind
             (fun uu____2434  ->
                match uu____2434 with
                | (m,uu____2443) -> FStar_Ident.lid_equals l m))
         in
      match uu____2400 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____2460,decls) ->
          FStar_Pervasives_Native.Some decls
  
let (set_iface_decls :
  env -> FStar_Ident.lident -> FStar_Parser_AST.decl Prims.list -> env) =
  fun env  ->
    fun l  ->
      fun ds  ->
        let uu____2494 =
          FStar_List.partition
            (fun uu____2524  ->
               match uu____2524 with
               | (m,uu____2533) -> FStar_Ident.lid_equals l m)
            env.remaining_iface_decls
           in
        match uu____2494 with
        | (uu____2538,rest) ->
            let uu___208_2572 = env  in
            {
              curmodule = (uu___208_2572.curmodule);
              curmonad = (uu___208_2572.curmonad);
              modules = (uu___208_2572.modules);
              scope_mods = (uu___208_2572.scope_mods);
              exported_ids = (uu___208_2572.exported_ids);
              trans_exported_ids = (uu___208_2572.trans_exported_ids);
              includes = (uu___208_2572.includes);
              sigaccum = (uu___208_2572.sigaccum);
              sigmap = (uu___208_2572.sigmap);
              iface = (uu___208_2572.iface);
              admitted_iface = (uu___208_2572.admitted_iface);
              expect_typ = (uu___208_2572.expect_typ);
              docs = (uu___208_2572.docs);
              remaining_iface_decls = ((l, ds) :: rest);
              syntax_only = (uu___208_2572.syntax_only);
              ds_hooks = (uu___208_2572.ds_hooks);
              dep_graph = (uu___208_2572.dep_graph)
            }
  
let (qual : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  FStar_Syntax_Util.qual_id 
let (qualify : env -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun env  ->
    fun id1  ->
      match env.curmonad with
      | FStar_Pervasives_Native.None  ->
          let uu____2601 = current_module env  in qual uu____2601 id1
      | FStar_Pervasives_Native.Some monad ->
          let uu____2603 =
            let uu____2604 = current_module env  in qual uu____2604 monad  in
          FStar_Syntax_Util.mk_field_projector_name_from_ident uu____2603 id1
  
let (syntax_only : env -> Prims.bool) = fun env  -> env.syntax_only 
let (set_syntax_only : env -> Prims.bool -> env) =
  fun env  ->
    fun b  ->
      let uu___209_2625 = env  in
      {
        curmodule = (uu___209_2625.curmodule);
        curmonad = (uu___209_2625.curmonad);
        modules = (uu___209_2625.modules);
        scope_mods = (uu___209_2625.scope_mods);
        exported_ids = (uu___209_2625.exported_ids);
        trans_exported_ids = (uu___209_2625.trans_exported_ids);
        includes = (uu___209_2625.includes);
        sigaccum = (uu___209_2625.sigaccum);
        sigmap = (uu___209_2625.sigmap);
        iface = (uu___209_2625.iface);
        admitted_iface = (uu___209_2625.admitted_iface);
        expect_typ = (uu___209_2625.expect_typ);
        docs = (uu___209_2625.docs);
        remaining_iface_decls = (uu___209_2625.remaining_iface_decls);
        syntax_only = b;
        ds_hooks = (uu___209_2625.ds_hooks);
        dep_graph = (uu___209_2625.dep_graph)
      }
  
let (ds_hooks : env -> dsenv_hooks) = fun env  -> env.ds_hooks 
let (set_ds_hooks : env -> dsenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___210_2643 = env  in
      {
        curmodule = (uu___210_2643.curmodule);
        curmonad = (uu___210_2643.curmonad);
        modules = (uu___210_2643.modules);
        scope_mods = (uu___210_2643.scope_mods);
        exported_ids = (uu___210_2643.exported_ids);
        trans_exported_ids = (uu___210_2643.trans_exported_ids);
        includes = (uu___210_2643.includes);
        sigaccum = (uu___210_2643.sigaccum);
        sigmap = (uu___210_2643.sigmap);
        iface = (uu___210_2643.iface);
        admitted_iface = (uu___210_2643.admitted_iface);
        expect_typ = (uu___210_2643.expect_typ);
        docs = (uu___210_2643.docs);
        remaining_iface_decls = (uu___210_2643.remaining_iface_decls);
        syntax_only = (uu___210_2643.syntax_only);
        ds_hooks = hooks;
        dep_graph = (uu___210_2643.dep_graph)
      }
  
let new_sigmap : 'Auu____2649 . unit -> 'Auu____2649 FStar_Util.smap =
  fun uu____2656  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (empty_env : FStar_Parser_Dep.deps -> env) =
  fun deps  ->
    let uu____2664 = new_sigmap ()  in
    let uu____2669 = new_sigmap ()  in
    let uu____2674 = new_sigmap ()  in
    let uu____2685 = new_sigmap ()  in
    let uu____2698 = new_sigmap ()  in
    {
      curmodule = FStar_Pervasives_Native.None;
      curmonad = FStar_Pervasives_Native.None;
      modules = [];
      scope_mods = [];
      exported_ids = uu____2664;
      trans_exported_ids = uu____2669;
      includes = uu____2674;
      sigaccum = [];
      sigmap = uu____2685;
      iface = false;
      admitted_iface = false;
      expect_typ = false;
      docs = uu____2698;
      remaining_iface_decls = [];
      syntax_only = false;
      ds_hooks = default_ds_hooks;
      dep_graph = deps
    }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun env  -> env.dep_graph 
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun env  ->
    fun ds  ->
      let uu___211_2732 = env  in
      {
        curmodule = (uu___211_2732.curmodule);
        curmonad = (uu___211_2732.curmonad);
        modules = (uu___211_2732.modules);
        scope_mods = (uu___211_2732.scope_mods);
        exported_ids = (uu___211_2732.exported_ids);
        trans_exported_ids = (uu___211_2732.trans_exported_ids);
        includes = (uu___211_2732.includes);
        sigaccum = (uu___211_2732.sigaccum);
        sigmap = (uu___211_2732.sigmap);
        iface = (uu___211_2732.iface);
        admitted_iface = (uu___211_2732.admitted_iface);
        expect_typ = (uu___211_2732.expect_typ);
        docs = (uu___211_2732.docs);
        remaining_iface_decls = (uu___211_2732.remaining_iface_decls);
        syntax_only = (uu___211_2732.syntax_only);
        ds_hooks = (uu___211_2732.ds_hooks);
        dep_graph = ds
      }
  
let (sigmap :
  env -> (FStar_Syntax_Syntax.sigelt * Prims.bool) FStar_Util.smap) =
  fun env  -> env.sigmap 
let (has_all_in_scope : env -> Prims.bool) =
  fun env  ->
    FStar_List.existsb
      (fun uu____2760  ->
         match uu____2760 with
         | (m,uu____2767) ->
             FStar_Ident.lid_equals m FStar_Parser_Const.all_lid) env.modules
  
let (set_bv_range :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.bv) =
  fun bv  ->
    fun r  ->
      let id1 =
        let uu___212_2780 = bv.FStar_Syntax_Syntax.ppname  in
        {
          FStar_Ident.idText = (uu___212_2780.FStar_Ident.idText);
          FStar_Ident.idRange = r
        }  in
      let uu___213_2781 = bv  in
      {
        FStar_Syntax_Syntax.ppname = id1;
        FStar_Syntax_Syntax.index = (uu___213_2781.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = (uu___213_2781.FStar_Syntax_Syntax.sort)
      }
  
let (bv_to_name :
  FStar_Syntax_Syntax.bv -> FStar_Range.range -> FStar_Syntax_Syntax.term) =
  fun bv  -> fun r  -> FStar_Syntax_Syntax.bv_to_name (set_bv_range bv r) 
let (unmangleMap :
  (Prims.string * Prims.string * FStar_Syntax_Syntax.delta_depth *
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option) Prims.list)
  =
  [("op_ColonColon", "Cons", FStar_Syntax_Syntax.delta_constant,
     (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor));
  ("not", "op_Negation", FStar_Syntax_Syntax.delta_equational,
    FStar_Pervasives_Native.None)]
  
let (unmangleOpName :
  FStar_Ident.ident ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun id1  ->
    FStar_Util.find_map unmangleMap
      (fun uu____2884  ->
         match uu____2884 with
         | (x,y,dd,dq) ->
             if id1.FStar_Ident.idText = x
             then
               let uu____2915 =
                 let uu____2916 =
                   FStar_Ident.lid_of_path ["Prims"; y]
                     id1.FStar_Ident.idRange
                    in
                 FStar_Syntax_Syntax.fvar uu____2916 dd dq  in
               FStar_Pervasives_Native.Some uu____2915
             else FStar_Pervasives_Native.None)
  
type 'a cont_t =
  | Cont_ok of 'a 
  | Cont_fail 
  | Cont_ignore 
let uu___is_Cont_ok : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ok _0 -> true | uu____2956 -> false
  
let __proj__Cont_ok__item___0 : 'a . 'a cont_t -> 'a =
  fun projectee  -> match projectee with | Cont_ok _0 -> _0 
let uu___is_Cont_fail : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_fail  -> true | uu____2994 -> false
  
let uu___is_Cont_ignore : 'a . 'a cont_t -> Prims.bool =
  fun projectee  ->
    match projectee with | Cont_ignore  -> true | uu____3015 -> false
  
let option_of_cont :
  'a .
    (unit -> 'a FStar_Pervasives_Native.option) ->
      'a cont_t -> 'a FStar_Pervasives_Native.option
  =
  fun k_ignore  ->
    fun uu___172_3045  ->
      match uu___172_3045 with
      | Cont_ok a -> FStar_Pervasives_Native.Some a
      | Cont_fail  -> FStar_Pervasives_Native.None
      | Cont_ignore  -> k_ignore ()
  
let find_in_record :
  'Auu____3064 .
    FStar_Ident.ident Prims.list ->
      FStar_Ident.ident ->
        record_or_dc ->
          (record_or_dc -> 'Auu____3064 cont_t) -> 'Auu____3064 cont_t
  =
  fun ns  ->
    fun id1  ->
      fun record  ->
        fun cont  ->
          let typename' =
            FStar_Ident.lid_of_ids
              (FStar_List.append ns [(record.typename).FStar_Ident.ident])
             in
          let uu____3101 = FStar_Ident.lid_equals typename' record.typename
             in
          if uu____3101
          then
            let fname =
              FStar_Ident.lid_of_ids
                (FStar_List.append (record.typename).FStar_Ident.ns [id1])
               in
            let find1 =
              FStar_Util.find_map record.fields
                (fun uu____3117  ->
                   match uu____3117 with
                   | (f,uu____3125) ->
                       if id1.FStar_Ident.idText = f.FStar_Ident.idText
                       then FStar_Pervasives_Native.Some record
                       else FStar_Pervasives_Native.None)
               in
            match find1 with
            | FStar_Pervasives_Native.Some r -> cont r
            | FStar_Pervasives_Native.None  -> Cont_ignore
          else Cont_ignore
  
let (get_exported_id_set :
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option)
  = fun e  -> fun mname  -> FStar_Util.smap_try_find e.exported_ids mname 
let (get_trans_exported_id_set :
  env ->
    Prims.string ->
      (exported_id_kind -> string_set FStar_ST.ref)
        FStar_Pervasives_Native.option)
  =
  fun e  -> fun mname  -> FStar_Util.smap_try_find e.trans_exported_ids mname 
let (string_of_exported_id_kind : exported_id_kind -> Prims.string) =
  fun uu___173_3199  ->
    match uu___173_3199 with
    | Exported_id_field  -> "field"
    | Exported_id_term_type  -> "term/type"
  
let find_in_module_with_includes :
  'a .
    exported_id_kind ->
      (FStar_Ident.lident -> 'a cont_t) ->
        'a cont_t ->
          env -> FStar_Ident.lident -> FStar_Ident.ident -> 'a cont_t
  =
  fun eikind  ->
    fun find_in_module  ->
      fun find_in_module_default  ->
        fun env  ->
          fun ns  ->
            fun id1  ->
              let idstr = id1.FStar_Ident.idText  in
              let rec aux uu___174_3275 =
                match uu___174_3275 with
                | [] -> find_in_module_default
                | modul::q ->
                    let mname = modul.FStar_Ident.str  in
                    let not_shadowed =
                      let uu____3288 = get_exported_id_set env mname  in
                      match uu____3288 with
                      | FStar_Pervasives_Native.None  -> true
                      | FStar_Pervasives_Native.Some mex ->
                          let mexports =
                            let uu____3315 = mex eikind  in
                            FStar_ST.op_Bang uu____3315  in
                          FStar_Util.set_mem idstr mexports
                       in
                    let mincludes =
                      let uu____3430 =
                        FStar_Util.smap_try_find env.includes mname  in
                      match uu____3430 with
                      | FStar_Pervasives_Native.None  -> []
                      | FStar_Pervasives_Native.Some minc ->
                          FStar_ST.op_Bang minc
                       in
                    let look_into =
                      if not_shadowed
                      then
                        let uu____3507 = qual modul id1  in
                        find_in_module uu____3507
                      else Cont_ignore  in
                    (match look_into with
                     | Cont_ignore  -> aux (FStar_List.append mincludes q)
                     | uu____3512 -> look_into)
                 in
              aux [ns]
  
let (is_exported_id_field : exported_id_kind -> Prims.bool) =
  fun uu___175_3521  ->
    match uu___175_3521 with
    | Exported_id_field  -> true
    | uu____3524 -> false
  
let try_lookup_id'' :
  'a .
    env ->
      FStar_Ident.ident ->
        exported_id_kind ->
          (local_binding -> 'a cont_t) ->
            (rec_binding -> 'a cont_t) ->
              (record_or_dc -> 'a cont_t) ->
                (FStar_Ident.lident -> 'a cont_t) ->
                  ('a cont_t -> FStar_Ident.ident -> 'a cont_t) ->
                    'a FStar_Pervasives_Native.option
  =
  fun env  ->
    fun id1  ->
      fun eikind  ->
        fun k_local_binding  ->
          fun k_rec_binding  ->
            fun k_record  ->
              fun find_in_module  ->
                fun lookup_default_id  ->
                  let check_local_binding_id uu___176_3648 =
                    match uu___176_3648 with
                    | (id',uu____3651) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let check_rec_binding_id uu___177_3659 =
                    match uu___177_3659 with
                    | (id',uu____3662,uu____3663) ->
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText
                     in
                  let curmod_ns =
                    let uu____3668 = current_module env  in
                    FStar_Ident.ids_of_lid uu____3668  in
                  let proc uu___178_3676 =
                    match uu___178_3676 with
                    | Local_binding l when check_local_binding_id l ->
                        k_local_binding l
                    | Rec_binding r when check_rec_binding_id r ->
                        k_rec_binding r
                    | Open_module_or_namespace (ns,Open_module ) ->
                        find_in_module_with_includes eikind find_in_module
                          Cont_ignore env ns id1
                    | Top_level_def id' when
                        id'.FStar_Ident.idText = id1.FStar_Ident.idText ->
                        lookup_default_id Cont_ignore id1
                    | Record_or_dc r when is_exported_id_field eikind ->
                        let uu____3685 = FStar_Ident.lid_of_ids curmod_ns  in
                        find_in_module_with_includes Exported_id_field
                          (fun lid  ->
                             let id2 = lid.FStar_Ident.ident  in
                             find_in_record lid.FStar_Ident.ns id2 r k_record)
                          Cont_ignore env uu____3685 id1
                    | uu____3690 -> Cont_ignore  in
                  let rec aux uu___179_3700 =
                    match uu___179_3700 with
                    | a::q ->
                        let uu____3709 = proc a  in
                        option_of_cont (fun uu____3713  -> aux q) uu____3709
                    | [] ->
                        let uu____3714 = lookup_default_id Cont_fail id1  in
                        option_of_cont
                          (fun uu____3718  -> FStar_Pervasives_Native.None)
                          uu____3714
                     in
                  aux env.scope_mods
  
let found_local_binding :
  'Auu____3726 .
    FStar_Range.range ->
      ('Auu____3726 * FStar_Syntax_Syntax.bv) -> FStar_Syntax_Syntax.term
  =
  fun r  ->
    fun uu____3740  -> match uu____3740 with | (id',x) -> bv_to_name x r
  
let find_in_module :
  'Auu____3758 .
    env ->
      FStar_Ident.lident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'Auu____3758)
          -> 'Auu____3758 -> 'Auu____3758
  =
  fun env  ->
    fun lid  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let uu____3799 =
            FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str  in
          match uu____3799 with
          | FStar_Pervasives_Native.Some sb -> k_global_def lid sb
          | FStar_Pervasives_Native.None  -> k_not_found
  
let (try_lookup_id :
  env ->
    FStar_Ident.ident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun id1  ->
      let uu____3843 = unmangleOpName id1  in
      match uu____3843 with
      | FStar_Pervasives_Native.Some f -> FStar_Pervasives_Native.Some f
      | uu____3849 ->
          try_lookup_id'' env id1 Exported_id_term_type
            (fun r  ->
               let uu____3855 = found_local_binding id1.FStar_Ident.idRange r
                  in
               Cont_ok uu____3855) (fun uu____3857  -> Cont_fail)
            (fun uu____3859  -> Cont_ignore)
            (fun i  ->
               find_in_module env i
                 (fun uu____3866  -> fun uu____3867  -> Cont_fail)
                 Cont_ignore)
            (fun uu____3875  -> fun uu____3876  -> Cont_fail)
  
let lookup_default_id :
  'a .
    env ->
      FStar_Ident.ident ->
        (FStar_Ident.lident ->
           (FStar_Syntax_Syntax.sigelt * Prims.bool) -> 'a cont_t)
          -> 'a cont_t -> 'a cont_t
  =
  fun env  ->
    fun id1  ->
      fun k_global_def  ->
        fun k_not_found  ->
          let find_in_monad =
            match env.curmonad with
            | FStar_Pervasives_Native.Some uu____3950 ->
                let lid = qualify env id1  in
                let uu____3952 =
                  FStar_Util.smap_try_find (sigmap env) lid.FStar_Ident.str
                   in
                (match uu____3952 with
                 | FStar_Pervasives_Native.Some r ->
                     let uu____3980 = k_global_def lid r  in
                     FStar_Pervasives_Native.Some uu____3980
                 | FStar_Pervasives_Native.None  ->
                     FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             in
          match find_in_monad with
          | FStar_Pervasives_Native.Some v1 -> v1
          | FStar_Pervasives_Native.None  ->
              let lid =
                let uu____4004 = current_module env  in qual uu____4004 id1
                 in
              find_in_module env lid k_global_def k_not_found
  
let (lid_is_curmod : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some m -> FStar_Ident.lid_equals lid m
  
let (module_is_defined : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      (lid_is_curmod env lid) ||
        (FStar_List.existsb
           (fun x  ->
              FStar_Ident.lid_equals lid (FStar_Pervasives_Native.fst x))
           env.modules)
  
let (resolve_module_name :
  env ->
    FStar_Ident.lident ->
      Prims.bool -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      fun honor_ns  ->
        let nslen = FStar_List.length lid.FStar_Ident.ns  in
        let rec aux uu___180_4076 =
          match uu___180_4076 with
          | [] ->
              let uu____4081 = module_is_defined env lid  in
              if uu____4081
              then FStar_Pervasives_Native.Some lid
              else FStar_Pervasives_Native.None
          | (Open_module_or_namespace (ns,Open_namespace ))::q when honor_ns
              ->
              let new_lid =
                let uu____4093 =
                  let uu____4094 = FStar_Ident.path_of_lid ns  in
                  let uu____4098 = FStar_Ident.path_of_lid lid  in
                  FStar_List.append uu____4094 uu____4098  in
                let uu____4103 = FStar_Ident.range_of_lid lid  in
                FStar_Ident.lid_of_path uu____4093 uu____4103  in
              let uu____4104 = module_is_defined env new_lid  in
              if uu____4104
              then FStar_Pervasives_Native.Some new_lid
              else aux q
          | (Module_abbrev (name,modul))::uu____4113 when
              (nslen = (Prims.parse_int "0")) &&
                (name.FStar_Ident.idText =
                   (lid.FStar_Ident.ident).FStar_Ident.idText)
              -> FStar_Pervasives_Native.Some modul
          | uu____4123::q -> aux q  in
        aux env.scope_mods
  
let (fail_if_curmodule :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun ns_original  ->
      fun ns_resolved  ->
        let uu____4143 =
          let uu____4145 = current_module env  in
          FStar_Ident.lid_equals ns_resolved uu____4145  in
        if uu____4143
        then
          let uu____4147 =
            FStar_Ident.lid_equals ns_resolved FStar_Parser_Const.prims_lid
             in
          (if uu____4147
           then ()
           else
             (let uu____4152 =
                let uu____4158 =
                  FStar_Util.format1
                    "Reference %s to current module is forbidden (see GitHub issue #451)"
                    ns_original.FStar_Ident.str
                   in
                (FStar_Errors.Fatal_ForbiddenReferenceToCurrentModule,
                  uu____4158)
                 in
              let uu____4162 = FStar_Ident.range_of_lid ns_original  in
              FStar_Errors.raise_error uu____4152 uu____4162))
        else ()
  
let (fail_if_qualified_by_curmodule : env -> FStar_Ident.lident -> unit) =
  fun env  ->
    fun lid  ->
      match lid.FStar_Ident.ns with
      | [] -> ()
      | uu____4176 ->
          let modul_orig = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          let uu____4180 = resolve_module_name env modul_orig true  in
          (match uu____4180 with
           | FStar_Pervasives_Native.Some modul_res ->
               fail_if_curmodule env modul_orig modul_res
           | uu____4185 -> ())
  
let (is_open : env -> FStar_Ident.lident -> open_kind -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun open_kind  ->
        FStar_List.existsb
          (fun uu___181_4208  ->
             match uu___181_4208 with
             | Open_module_or_namespace (ns,k) ->
                 (k = open_kind) && (FStar_Ident.lid_equals lid ns)
             | uu____4212 -> false) env.scope_mods
  
let (namespace_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  -> fun lid  -> is_open env lid Open_namespace 
let (module_is_open : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  -> (lid_is_curmod env lid) || (is_open env lid Open_module)
  
let (shorten_module_path :
  env ->
    FStar_Ident.ident Prims.list ->
      Prims.bool ->
        (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun ids  ->
      fun is_full_path  ->
        let rec aux revns id1 =
          let lid = FStar_Ident.lid_of_ns_and_id (FStar_List.rev revns) id1
             in
          if namespace_is_open env lid
          then
            FStar_Pervasives_Native.Some
              ((FStar_List.rev (id1 :: revns)), [])
          else
            (match revns with
             | [] -> FStar_Pervasives_Native.None
             | ns_last_id::rev_ns_prefix ->
                 let uu____4341 = aux rev_ns_prefix ns_last_id  in
                 FStar_All.pipe_right uu____4341
                   (FStar_Util.map_option
                      (fun uu____4391  ->
                         match uu____4391 with
                         | (stripped_ids,rev_kept_ids) ->
                             (stripped_ids, (id1 :: rev_kept_ids)))))
           in
        let do_shorten env1 ids1 =
          match FStar_List.rev ids1 with
          | [] -> ([], [])
          | ns_last_id::ns_rev_prefix ->
              let uu____4461 = aux ns_rev_prefix ns_last_id  in
              (match uu____4461 with
               | FStar_Pervasives_Native.None  -> ([], ids1)
               | FStar_Pervasives_Native.Some (stripped_ids,rev_kept_ids) ->
                   (stripped_ids, (FStar_List.rev rev_kept_ids)))
           in
        if is_full_path && ((FStar_List.length ids) > (Prims.parse_int "0"))
        then
          let uu____4524 =
            let uu____4527 = FStar_Ident.lid_of_ids ids  in
            resolve_module_name env uu____4527 true  in
          match uu____4524 with
          | FStar_Pervasives_Native.Some m when module_is_open env m ->
              (ids, [])
          | uu____4542 -> do_shorten env ids
        else do_shorten env ids
  
let resolve_in_open_namespaces'' :
  'a .
    env ->
      FStar_Ident.lident ->
        exported_id_kind ->
          (local_binding -> 'a cont_t) ->
            (rec_binding -> 'a cont_t) ->
              (record_or_dc -> 'a cont_t) ->
                (FStar_Ident.lident -> 'a cont_t) ->
                  ('a cont_t -> FStar_Ident.ident -> 'a cont_t) ->
                    'a FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      fun eikind  ->
        fun k_local_binding  ->
          fun k_rec_binding  ->
            fun k_record  ->
              fun f_module  ->
                fun l_default  ->
                  match lid.FStar_Ident.ns with
                  | uu____4663::uu____4664 ->
                      let uu____4667 =
                        let uu____4670 =
                          let uu____4671 =
                            FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                          let uu____4672 = FStar_Ident.range_of_lid lid  in
                          FStar_Ident.set_lid_range uu____4671 uu____4672  in
                        resolve_module_name env uu____4670 true  in
                      (match uu____4667 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some modul ->
                           let uu____4677 =
                             find_in_module_with_includes eikind f_module
                               Cont_fail env modul lid.FStar_Ident.ident
                              in
                           option_of_cont
                             (fun uu____4681  -> FStar_Pervasives_Native.None)
                             uu____4677)
                  | [] ->
                      try_lookup_id'' env lid.FStar_Ident.ident eikind
                        k_local_binding k_rec_binding k_record f_module
                        l_default
  
let cont_of_option :
  'a . 'a cont_t -> 'a FStar_Pervasives_Native.option -> 'a cont_t =
  fun k_none  ->
    fun uu___182_4705  ->
      match uu___182_4705 with
      | FStar_Pervasives_Native.Some v1 -> Cont_ok v1
      | FStar_Pervasives_Native.None  -> k_none
  
let resolve_in_open_namespaces' :
  'a .
    env ->
      FStar_Ident.lident ->
        (local_binding -> 'a FStar_Pervasives_Native.option) ->
          (rec_binding -> 'a FStar_Pervasives_Native.option) ->
            (FStar_Ident.lident ->
               (FStar_Syntax_Syntax.sigelt * Prims.bool) ->
                 'a FStar_Pervasives_Native.option)
              -> 'a FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      fun k_local_binding  ->
        fun k_rec_binding  ->
          fun k_global_def  ->
            let k_global_def' k lid1 def =
              let uu____4826 = k_global_def lid1 def  in
              cont_of_option k uu____4826  in
            let f_module lid' =
              let k = Cont_ignore  in
              find_in_module env lid' (k_global_def' k) k  in
            let l_default k i = lookup_default_id env i (k_global_def' k) k
               in
            resolve_in_open_namespaces'' env lid Exported_id_term_type
              (fun l  ->
                 let uu____4862 = k_local_binding l  in
                 cont_of_option Cont_fail uu____4862)
              (fun r  ->
                 let uu____4868 = k_rec_binding r  in
                 cont_of_option Cont_fail uu____4868)
              (fun uu____4872  -> Cont_ignore) f_module l_default
  
let (fv_qual_of_se :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4883,uu____4884,uu____4885,l,uu____4887,uu____4888) ->
        let qopt =
          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
            (fun uu___183_4901  ->
               match uu___183_4901 with
               | FStar_Syntax_Syntax.RecordConstructor (uu____4904,fs) ->
                   FStar_Pervasives_Native.Some
                     (FStar_Syntax_Syntax.Record_ctor (l, fs))
               | uu____4916 -> FStar_Pervasives_Native.None)
           in
        (match qopt with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
         | x -> x)
    | FStar_Syntax_Syntax.Sig_declare_typ (uu____4922,uu____4923,uu____4924)
        -> FStar_Pervasives_Native.None
    | uu____4925 -> FStar_Pervasives_Native.None
  
let (lb_fv :
  FStar_Syntax_Syntax.letbinding Prims.list ->
    FStar_Ident.lident -> FStar_Syntax_Syntax.fv)
  =
  fun lbs  ->
    fun lid  ->
      let uu____4941 =
        FStar_Util.find_map lbs
          (fun lb  ->
             let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
             let uu____4949 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
             if uu____4949
             then FStar_Pervasives_Native.Some fv
             else FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____4941 FStar_Util.must
  
let (ns_of_lid_equals :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    fun ns  ->
      (let uu____4972 =
         let uu____4973 = FStar_Ident.ids_of_lid ns  in
         FStar_List.length uu____4973  in
       (FStar_List.length lid.FStar_Ident.ns) = uu____4972) &&
        (let uu____4981 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
         FStar_Ident.lid_equals uu____4981 ns)
  
let (delta_depth_of_declaration :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.delta_depth)
  =
  fun lid  ->
    fun quals  ->
      let dd =
        let uu____4998 =
          (FStar_Syntax_Util.is_primop_lid lid) ||
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___184_5005  ->
                     match uu___184_5005 with
                     | FStar_Syntax_Syntax.Projector uu____5007 -> true
                     | FStar_Syntax_Syntax.Discriminator uu____5013 -> true
                     | uu____5015 -> false)))
           in
        if uu____4998
        then FStar_Syntax_Syntax.delta_equational
        else FStar_Syntax_Syntax.delta_constant  in
      let uu____5020 =
        (FStar_All.pipe_right quals
           (FStar_Util.for_some
              (fun uu___185_5026  ->
                 match uu___185_5026 with
                 | FStar_Syntax_Syntax.Abstract  -> true
                 | uu____5029 -> false)))
          ||
          ((FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___186_5035  ->
                    match uu___186_5035 with
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____5038 -> false)))
             &&
             (let uu____5041 =
                FStar_All.pipe_right quals
                  (FStar_Util.for_some
                     (fun uu___187_5047  ->
                        match uu___187_5047 with
                        | FStar_Syntax_Syntax.New  -> true
                        | uu____5050 -> false))
                 in
              Prims.op_Negation uu____5041))
         in
      if uu____5020 then FStar_Syntax_Syntax.Delta_abstract dd else dd
  
let (try_lookup_name :
  Prims.bool ->
    Prims.bool ->
      env -> FStar_Ident.lident -> foundname FStar_Pervasives_Native.option)
  =
  fun any_val  ->
    fun exclude_interf  ->
      fun env  ->
        fun lid  ->
          let occurrence_range = FStar_Ident.range_of_lid lid  in
          let k_global_def source_lid uu___190_5102 =
            match uu___190_5102 with
            | (uu____5110,true ) when exclude_interf ->
                FStar_Pervasives_Native.None
            | (se,uu____5114) ->
                (match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ uu____5119 ->
                     let uu____5136 =
                       let uu____5137 =
                         let uu____5144 =
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         (uu____5144, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____5137  in
                     FStar_Pervasives_Native.Some uu____5136
                 | FStar_Syntax_Syntax.Sig_datacon uu____5147 ->
                     let uu____5163 =
                       let uu____5164 =
                         let uu____5171 =
                           let uu____5172 = fv_qual_of_se se  in
                           FStar_Syntax_Syntax.fvar source_lid
                             FStar_Syntax_Syntax.delta_constant uu____5172
                            in
                         (uu____5171, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____5164  in
                     FStar_Pervasives_Native.Some uu____5163
                 | FStar_Syntax_Syntax.Sig_let ((uu____5177,lbs),uu____5179)
                     ->
                     let fv = lb_fv lbs source_lid  in
                     let uu____5191 =
                       let uu____5192 =
                         let uu____5199 =
                           FStar_Syntax_Syntax.fvar source_lid
                             fv.FStar_Syntax_Syntax.fv_delta
                             fv.FStar_Syntax_Syntax.fv_qual
                            in
                         (uu____5199, (se.FStar_Syntax_Syntax.sigattrs))  in
                       Term_name uu____5192  in
                     FStar_Pervasives_Native.Some uu____5191
                 | FStar_Syntax_Syntax.Sig_declare_typ
                     (lid1,uu____5203,uu____5204) ->
                     let quals = se.FStar_Syntax_Syntax.sigquals  in
                     let uu____5208 =
                       any_val ||
                         (FStar_All.pipe_right quals
                            (FStar_Util.for_some
                               (fun uu___188_5214  ->
                                  match uu___188_5214 with
                                  | FStar_Syntax_Syntax.Assumption  -> true
                                  | uu____5217 -> false)))
                        in
                     if uu____5208
                     then
                       let lid2 =
                         let uu____5223 = FStar_Ident.range_of_lid source_lid
                            in
                         FStar_Ident.set_lid_range lid1 uu____5223  in
                       let dd = delta_depth_of_declaration lid2 quals  in
                       let uu____5225 =
                         FStar_Util.find_map quals
                           (fun uu___189_5230  ->
                              match uu___189_5230 with
                              | FStar_Syntax_Syntax.Reflectable refl_monad ->
                                  FStar_Pervasives_Native.Some refl_monad
                              | uu____5234 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____5225 with
                        | FStar_Pervasives_Native.Some refl_monad ->
                            let refl_const =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_reflect refl_monad))
                                FStar_Pervasives_Native.None occurrence_range
                               in
                            FStar_Pervasives_Native.Some
                              (Term_name
                                 (refl_const,
                                   (se.FStar_Syntax_Syntax.sigattrs)))
                        | uu____5243 ->
                            let uu____5246 =
                              let uu____5247 =
                                let uu____5254 =
                                  let uu____5255 = fv_qual_of_se se  in
                                  FStar_Syntax_Syntax.fvar lid2 dd uu____5255
                                   in
                                (uu____5254,
                                  (se.FStar_Syntax_Syntax.sigattrs))
                                 in
                              Term_name uu____5247  in
                            FStar_Pervasives_Native.Some uu____5246)
                     else FStar_Pervasives_Native.None
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5263 =
                       let uu____5264 =
                         let uu____5269 =
                           let uu____5270 =
                             FStar_Ident.range_of_lid source_lid  in
                           FStar_Ident.set_lid_range
                             ne.FStar_Syntax_Syntax.mname uu____5270
                            in
                         (se, uu____5269)  in
                       Eff_name uu____5264  in
                     FStar_Pervasives_Native.Some uu____5263
                 | FStar_Syntax_Syntax.Sig_effect_abbrev uu____5271 ->
                     FStar_Pervasives_Native.Some (Eff_name (se, source_lid))
                 | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
                     let uu____5290 =
                       let uu____5291 =
                         let uu____5298 =
                           FStar_Syntax_Syntax.fvar source_lid
                             (FStar_Syntax_Syntax.Delta_constant_at_level
                                (Prims.parse_int "1"))
                             FStar_Pervasives_Native.None
                            in
                         (uu____5298, [])  in
                       Term_name uu____5291  in
                     FStar_Pervasives_Native.Some uu____5290
                 | uu____5302 -> FStar_Pervasives_Native.None)
             in
          let k_local_binding r =
            let t =
              let uu____5320 = FStar_Ident.range_of_lid lid  in
              found_local_binding uu____5320 r  in
            FStar_Pervasives_Native.Some (Term_name (t, []))  in
          let k_rec_binding uu____5336 =
            match uu____5336 with
            | (id1,l,dd) ->
                let uu____5348 =
                  let uu____5349 =
                    let uu____5356 =
                      let uu____5357 =
                        let uu____5358 = FStar_Ident.range_of_lid lid  in
                        FStar_Ident.set_lid_range l uu____5358  in
                      FStar_Syntax_Syntax.fvar uu____5357 dd
                        FStar_Pervasives_Native.None
                       in
                    (uu____5356, [])  in
                  Term_name uu____5349  in
                FStar_Pervasives_Native.Some uu____5348
             in
          let found_unmangled =
            match lid.FStar_Ident.ns with
            | [] ->
                let uu____5366 = unmangleOpName lid.FStar_Ident.ident  in
                (match uu____5366 with
                 | FStar_Pervasives_Native.Some t ->
                     FStar_Pervasives_Native.Some (Term_name (t, []))
                 | uu____5374 -> FStar_Pervasives_Native.None)
            | uu____5377 -> FStar_Pervasives_Native.None  in
          match found_unmangled with
          | FStar_Pervasives_Native.None  ->
              resolve_in_open_namespaces' env lid k_local_binding
                k_rec_binding k_global_def
          | x -> x
  
let (try_lookup_effect_name' :
  Prims.bool ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.sigelt * FStar_Ident.lident)
          FStar_Pervasives_Native.option)
  =
  fun exclude_interf  ->
    fun env  ->
      fun lid  ->
        let uu____5415 = try_lookup_name true exclude_interf env lid  in
        match uu____5415 with
        | FStar_Pervasives_Native.Some (Eff_name (o,l)) ->
            FStar_Pervasives_Native.Some (o, l)
        | uu____5431 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5451 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5451 with
      | FStar_Pervasives_Native.Some (o,l1) ->
          FStar_Pervasives_Native.Some l1
      | uu____5466 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_name_and_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * FStar_Syntax_Syntax.cflag Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5492 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5492 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5508;
             FStar_Syntax_Syntax.sigquals = uu____5509;
             FStar_Syntax_Syntax.sigmeta = uu____5510;
             FStar_Syntax_Syntax.sigattrs = uu____5511;_},l1)
          ->
          FStar_Pervasives_Native.Some
            (l1, (ne.FStar_Syntax_Syntax.cattributes))
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (uu____5529,uu____5530,uu____5531,uu____5532,cattributes);
             FStar_Syntax_Syntax.sigrng = uu____5534;
             FStar_Syntax_Syntax.sigquals = uu____5535;
             FStar_Syntax_Syntax.sigmeta = uu____5536;
             FStar_Syntax_Syntax.sigattrs = uu____5537;_},l1)
          -> FStar_Pervasives_Native.Some (l1, cattributes)
      | uu____5559 -> FStar_Pervasives_Native.None
  
let (try_lookup_effect_defn :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.eff_decl FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5585 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5585 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
               ne;
             FStar_Syntax_Syntax.sigrng = uu____5595;
             FStar_Syntax_Syntax.sigquals = uu____5596;
             FStar_Syntax_Syntax.sigmeta = uu____5597;
             FStar_Syntax_Syntax.sigattrs = uu____5598;_},uu____5599)
          -> FStar_Pervasives_Native.Some ne
      | uu____5608 -> FStar_Pervasives_Native.None
  
let (is_effect_name : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____5627 = try_lookup_effect_name env lid  in
      match uu____5627 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5632 -> true
  
let (try_lookup_root_effect_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____5647 =
        try_lookup_effect_name' (Prims.op_Negation env.iface) env l  in
      match uu____5647 with
      | FStar_Pervasives_Native.Some
          ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_effect_abbrev
               (l',uu____5657,uu____5658,uu____5659,uu____5660);
             FStar_Syntax_Syntax.sigrng = uu____5661;
             FStar_Syntax_Syntax.sigquals = uu____5662;
             FStar_Syntax_Syntax.sigmeta = uu____5663;
             FStar_Syntax_Syntax.sigattrs = uu____5664;_},uu____5665)
          ->
          let rec aux new_name =
            let uu____5686 =
              FStar_Util.smap_try_find (sigmap env) new_name.FStar_Ident.str
               in
            match uu____5686 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (s,uu____5707) ->
                (match s.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_new_effect ne ->
                     let uu____5718 =
                       let uu____5719 = FStar_Ident.range_of_lid l  in
                       FStar_Ident.set_lid_range ne.FStar_Syntax_Syntax.mname
                         uu____5719
                        in
                     FStar_Pervasives_Native.Some uu____5718
                 | FStar_Syntax_Syntax.Sig_effect_abbrev
                     (uu____5720,uu____5721,uu____5722,cmp,uu____5724) ->
                     let l'' = FStar_Syntax_Util.comp_effect_name cmp  in
                     aux l''
                 | uu____5730 -> FStar_Pervasives_Native.None)
             in
          aux l'
      | FStar_Pervasives_Native.Some (uu____5731,l') ->
          FStar_Pervasives_Native.Some l'
      | uu____5737 -> FStar_Pervasives_Native.None
  
let (lookup_letbinding_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___191_5776 =
        match uu___191_5776 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____5786,uu____5787,uu____5788);
             FStar_Syntax_Syntax.sigrng = uu____5789;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____5791;
             FStar_Syntax_Syntax.sigattrs = uu____5792;_},uu____5793)
            -> FStar_Pervasives_Native.Some quals
        | uu____5802 -> FStar_Pervasives_Native.None  in
      let uu____5810 =
        resolve_in_open_namespaces' env lid
          (fun uu____5818  -> FStar_Pervasives_Native.None)
          (fun uu____5822  -> FStar_Pervasives_Native.None) k_global_def
         in
      match uu____5810 with
      | FStar_Pervasives_Native.Some quals -> quals
      | uu____5832 -> []
  
let (try_lookup_module :
  env ->
    FStar_Ident.path ->
      FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun path  ->
      let uu____5850 =
        FStar_List.tryFind
          (fun uu____5865  ->
             match uu____5865 with
             | (mlid,modul) ->
                 let uu____5873 = FStar_Ident.path_of_lid mlid  in
                 uu____5873 = path) env.modules
         in
      match uu____5850 with
      | FStar_Pervasives_Native.Some (uu____5876,modul) ->
          FStar_Pervasives_Native.Some modul
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_let :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___192_5916 =
        match uu___192_5916 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               ((uu____5924,lbs),uu____5926);
             FStar_Syntax_Syntax.sigrng = uu____5927;
             FStar_Syntax_Syntax.sigquals = uu____5928;
             FStar_Syntax_Syntax.sigmeta = uu____5929;
             FStar_Syntax_Syntax.sigattrs = uu____5930;_},uu____5931)
            ->
            let fv = lb_fv lbs lid1  in
            let uu____5949 =
              FStar_Syntax_Syntax.fvar lid1 fv.FStar_Syntax_Syntax.fv_delta
                fv.FStar_Syntax_Syntax.fv_qual
               in
            FStar_Pervasives_Native.Some uu____5949
        | uu____5950 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____5957  -> FStar_Pervasives_Native.None)
        (fun uu____5959  -> FStar_Pervasives_Native.None) k_global_def
  
let (try_lookup_definition :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___193_5992 =
        match uu___193_5992 with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
               (lbs,uu____6003);
             FStar_Syntax_Syntax.sigrng = uu____6004;
             FStar_Syntax_Syntax.sigquals = uu____6005;
             FStar_Syntax_Syntax.sigmeta = uu____6006;
             FStar_Syntax_Syntax.sigattrs = uu____6007;_},uu____6008)
            ->
            FStar_Util.find_map (FStar_Pervasives_Native.snd lbs)
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inr fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv lid1 ->
                     FStar_Pervasives_Native.Some
                       (lb.FStar_Syntax_Syntax.lbdef)
                 | uu____6034 -> FStar_Pervasives_Native.None)
        | uu____6041 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6052  -> FStar_Pervasives_Native.None)
        (fun uu____6056  -> FStar_Pervasives_Native.None) k_global_def
  
let (empty_include_smap :
  FStar_Ident.lident Prims.list FStar_ST.ref FStar_Util.smap) = new_sigmap () 
let (empty_exported_id_smap : exported_id_set FStar_Util.smap) =
  new_sigmap () 
let (try_lookup_lid' :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute
            Prims.list) FStar_Pervasives_Native.option)
  =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let uu____6116 = try_lookup_name any_val exclude_interface env lid
             in
          match uu____6116 with
          | FStar_Pervasives_Native.Some (Term_name (e,attrs)) ->
              FStar_Pervasives_Native.Some (e, attrs)
          | uu____6141 -> FStar_Pervasives_Native.None
  
let (drop_attributes :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun x  ->
    match x with
    | FStar_Pervasives_Native.Some (t,uu____6179) ->
        FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (try_lookup_lid_with_attributes :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  = fun env  -> fun l  -> try_lookup_lid' env.iface false env l 
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____6237 = try_lookup_lid_with_attributes env l  in
      FStar_All.pipe_right uu____6237 drop_attributes
  
let (resolve_to_fully_qualified_name :
  env ->
    FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____6269 = try_lookup_lid env l  in
      match uu____6269 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some e ->
          let uu____6275 =
            let uu____6276 = FStar_Syntax_Subst.compress e  in
            uu____6276.FStar_Syntax_Syntax.n  in
          (match uu____6275 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Pervasives_Native.Some
                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
           | uu____6282 -> FStar_Pervasives_Native.None)
  
let (shorten_lid' : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____6294 = shorten_module_path env lid.FStar_Ident.ns true  in
      match uu____6294 with
      | (uu____6304,short) ->
          FStar_Ident.lid_of_ns_and_id short lid.FStar_Ident.ident
  
let (shorten_lid : env -> FStar_Ident.lid -> FStar_Ident.lid) =
  fun env  ->
    fun lid  ->
      match env.curmodule with
      | FStar_Pervasives_Native.None  -> shorten_lid' env lid
      | uu____6325 ->
          let lid_without_ns =
            FStar_Ident.lid_of_ns_and_id [] lid.FStar_Ident.ident  in
          let uu____6329 = resolve_to_fully_qualified_name env lid_without_ns
             in
          (match uu____6329 with
           | FStar_Pervasives_Native.Some lid' when
               lid'.FStar_Ident.str = lid.FStar_Ident.str -> lid_without_ns
           | uu____6334 -> shorten_lid' env lid)
  
let (try_lookup_lid_with_attributes_no_resolve :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let env' =
        let uu___214_6365 = env  in
        {
          curmodule = (uu___214_6365.curmodule);
          curmonad = (uu___214_6365.curmonad);
          modules = (uu___214_6365.modules);
          scope_mods = [];
          exported_ids = empty_exported_id_smap;
          trans_exported_ids = (uu___214_6365.trans_exported_ids);
          includes = empty_include_smap;
          sigaccum = (uu___214_6365.sigaccum);
          sigmap = (uu___214_6365.sigmap);
          iface = (uu___214_6365.iface);
          admitted_iface = (uu___214_6365.admitted_iface);
          expect_typ = (uu___214_6365.expect_typ);
          docs = (uu___214_6365.docs);
          remaining_iface_decls = (uu___214_6365.remaining_iface_decls);
          syntax_only = (uu___214_6365.syntax_only);
          ds_hooks = (uu___214_6365.ds_hooks);
          dep_graph = (uu___214_6365.dep_graph)
        }  in
      try_lookup_lid_with_attributes env' l
  
let (try_lookup_lid_no_resolve :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____6381 = try_lookup_lid_with_attributes_no_resolve env l  in
      FStar_All.pipe_right uu____6381 drop_attributes
  
let (try_lookup_doc :
  env ->
    FStar_Ident.lid -> FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option)
  = fun env  -> fun l  -> FStar_Util.smap_try_find env.docs l.FStar_Ident.str 
let (try_lookup_datacon :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 se =
        match se with
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
               (uu____6451,uu____6452,uu____6453);
             FStar_Syntax_Syntax.sigrng = uu____6454;
             FStar_Syntax_Syntax.sigquals = quals;
             FStar_Syntax_Syntax.sigmeta = uu____6456;
             FStar_Syntax_Syntax.sigattrs = uu____6457;_},uu____6458)
            ->
            let uu____6465 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___194_6471  ->
                      match uu___194_6471 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | uu____6474 -> false))
               in
            if uu____6465
            then
              let uu____6479 =
                FStar_Syntax_Syntax.lid_as_fv lid1
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Pervasives_Native.Some uu____6479
            else FStar_Pervasives_Native.None
        | ({
             FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
               uu____6482;
             FStar_Syntax_Syntax.sigrng = uu____6483;
             FStar_Syntax_Syntax.sigquals = uu____6484;
             FStar_Syntax_Syntax.sigmeta = uu____6485;
             FStar_Syntax_Syntax.sigattrs = uu____6486;_},uu____6487)
            ->
            let qual1 = fv_qual_of_se (FStar_Pervasives_Native.fst se)  in
            let uu____6513 =
              FStar_Syntax_Syntax.lid_as_fv lid1
                FStar_Syntax_Syntax.delta_constant qual1
               in
            FStar_Pervasives_Native.Some uu____6513
        | uu____6514 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6521  -> FStar_Pervasives_Native.None)
        (fun uu____6523  -> FStar_Pervasives_Native.None) k_global_def
  
let (find_all_datacons :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let k_global_def lid1 uu___195_6558 =
        match uu___195_6558 with
        | ({
             FStar_Syntax_Syntax.sigel =
               FStar_Syntax_Syntax.Sig_inductive_typ
               (uu____6568,uu____6569,uu____6570,uu____6571,datas,uu____6573);
             FStar_Syntax_Syntax.sigrng = uu____6574;
             FStar_Syntax_Syntax.sigquals = uu____6575;
             FStar_Syntax_Syntax.sigmeta = uu____6576;
             FStar_Syntax_Syntax.sigattrs = uu____6577;_},uu____6578)
            -> FStar_Pervasives_Native.Some datas
        | uu____6595 -> FStar_Pervasives_Native.None  in
      resolve_in_open_namespaces' env lid
        (fun uu____6606  -> FStar_Pervasives_Native.None)
        (fun uu____6610  -> FStar_Pervasives_Native.None) k_global_def
  
let (record_cache_aux_with_filter :
  ((((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))) *
    (unit -> unit)))
  =
  let record_cache = FStar_Util.mk_ref [[]]  in
  let push1 uu____6689 =
    let uu____6690 =
      let uu____6695 =
        let uu____6698 = FStar_ST.op_Bang record_cache  in
        FStar_List.hd uu____6698  in
      let uu____6754 = FStar_ST.op_Bang record_cache  in uu____6695 ::
        uu____6754
       in
    FStar_ST.op_Colon_Equals record_cache uu____6690  in
  let pop1 uu____6864 =
    let uu____6865 =
      let uu____6870 = FStar_ST.op_Bang record_cache  in
      FStar_List.tl uu____6870  in
    FStar_ST.op_Colon_Equals record_cache uu____6865  in
  let snapshot1 uu____6985 = FStar_Common.snapshot push1 record_cache ()  in
  let rollback1 depth = FStar_Common.rollback pop1 record_cache depth  in
  let peek1 uu____7053 =
    let uu____7054 = FStar_ST.op_Bang record_cache  in
    FStar_List.hd uu____7054  in
  let insert r =
    let uu____7116 =
      let uu____7121 = let uu____7124 = peek1 ()  in r :: uu____7124  in
      let uu____7127 =
        let uu____7132 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____7132  in
      uu____7121 :: uu____7127  in
    FStar_ST.op_Colon_Equals record_cache uu____7116  in
  let filter1 uu____7244 =
    let rc = peek1 ()  in
    let filtered =
      FStar_List.filter
        (fun r  -> Prims.op_Negation r.is_private_or_abstract) rc
       in
    let uu____7253 =
      let uu____7258 =
        let uu____7263 = FStar_ST.op_Bang record_cache  in
        FStar_List.tl uu____7263  in
      filtered :: uu____7258  in
    FStar_ST.op_Colon_Equals record_cache uu____7253  in
  let aux = ((push1, pop1), ((snapshot1, rollback1), (peek1, insert)))  in
  (aux, filter1) 
let (record_cache_aux :
  (((unit -> unit) * (unit -> unit)) * (((unit -> (Prims.int * unit)) *
    (Prims.int FStar_Pervasives_Native.option -> unit)) *
    ((unit -> record_or_dc Prims.list) * (record_or_dc -> unit)))))
  = FStar_Pervasives_Native.fst record_cache_aux_with_filter 
let (filter_record_cache : unit -> unit) =
  FStar_Pervasives_Native.snd record_cache_aux_with_filter 
let (push_record_cache : unit -> unit) =
  FStar_Pervasives_Native.fst (FStar_Pervasives_Native.fst record_cache_aux) 
let (pop_record_cache : unit -> unit) =
  FStar_Pervasives_Native.snd (FStar_Pervasives_Native.fst record_cache_aux) 
let (snapshot_record_cache : unit -> (Prims.int * unit)) =
  FStar_Pervasives_Native.fst
    (FStar_Pervasives_Native.fst
       (FStar_Pervasives_Native.snd record_cache_aux))
  
let (rollback_record_cache :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  FStar_Pervasives_Native.snd
    (FStar_Pervasives_Native.fst
       (FStar_Pervasives_Native.snd record_cache_aux))
  
let (peek_record_cache : unit -> record_or_dc Prims.list) =
  FStar_Pervasives_Native.fst
    (FStar_Pervasives_Native.snd
       (FStar_Pervasives_Native.snd record_cache_aux))
  
let (insert_record_cache : record_or_dc -> unit) =
  FStar_Pervasives_Native.snd
    (FStar_Pervasives_Native.snd
       (FStar_Pervasives_Native.snd record_cache_aux))
  
let (extract_record :
  env ->
    scope_mod Prims.list FStar_ST.ref -> FStar_Syntax_Syntax.sigelt -> unit)
  =
  fun e  ->
    fun new_globs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_bundle (sigs,uu____8255) ->
            let is_record =
              FStar_Util.for_some
                (fun uu___196_8274  ->
                   match uu___196_8274 with
                   | FStar_Syntax_Syntax.RecordType uu____8276 -> true
                   | FStar_Syntax_Syntax.RecordConstructor uu____8286 -> true
                   | uu____8296 -> false)
               in
            let find_dc dc =
              FStar_All.pipe_right sigs
                (FStar_Util.find_opt
                   (fun uu___197_8321  ->
                      match uu___197_8321 with
                      | {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid,uu____8324,uu____8325,uu____8326,uu____8327,uu____8328);
                          FStar_Syntax_Syntax.sigrng = uu____8329;
                          FStar_Syntax_Syntax.sigquals = uu____8330;
                          FStar_Syntax_Syntax.sigmeta = uu____8331;
                          FStar_Syntax_Syntax.sigattrs = uu____8332;_} ->
                          FStar_Ident.lid_equals dc lid
                      | uu____8343 -> false))
               in
            FStar_All.pipe_right sigs
              (FStar_List.iter
                 (fun uu___198_8379  ->
                    match uu___198_8379 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ
                          (typename,univs1,parms,uu____8383,uu____8384,dc::[]);
                        FStar_Syntax_Syntax.sigrng = uu____8386;
                        FStar_Syntax_Syntax.sigquals = typename_quals;
                        FStar_Syntax_Syntax.sigmeta = uu____8388;
                        FStar_Syntax_Syntax.sigattrs = uu____8389;_} ->
                        let uu____8400 =
                          let uu____8401 = find_dc dc  in
                          FStar_All.pipe_left FStar_Util.must uu____8401  in
                        (match uu____8400 with
                         | {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_datacon
                               (constrname,uu____8407,t,uu____8409,uu____8410,uu____8411);
                             FStar_Syntax_Syntax.sigrng = uu____8412;
                             FStar_Syntax_Syntax.sigquals = uu____8413;
                             FStar_Syntax_Syntax.sigmeta = uu____8414;
                             FStar_Syntax_Syntax.sigattrs = uu____8415;_} ->
                             let uu____8426 =
                               FStar_Syntax_Util.arrow_formals t  in
                             (match uu____8426 with
                              | (formals,uu____8442) ->
                                  let is_rec = is_record typename_quals  in
                                  let formals' =
                                    FStar_All.pipe_right formals
                                      (FStar_List.collect
                                         (fun uu____8496  ->
                                            match uu____8496 with
                                            | (x,q) ->
                                                let uu____8509 =
                                                  (FStar_Syntax_Syntax.is_null_bv
                                                     x)
                                                    ||
                                                    (is_rec &&
                                                       (FStar_Syntax_Syntax.is_implicit
                                                          q))
                                                   in
                                                if uu____8509
                                                then []
                                                else [(x, q)]))
                                     in
                                  let fields' =
                                    FStar_All.pipe_right formals'
                                      (FStar_List.map
                                         (fun uu____8564  ->
                                            match uu____8564 with
                                            | (x,q) ->
                                                ((x.FStar_Syntax_Syntax.ppname),
                                                  (x.FStar_Syntax_Syntax.sort))))
                                     in
                                  let fields = fields'  in
                                  let record =
                                    {
                                      typename;
                                      constrname =
                                        (constrname.FStar_Ident.ident);
                                      parms;
                                      fields;
                                      is_private_or_abstract =
                                        ((FStar_List.contains
                                            FStar_Syntax_Syntax.Private
                                            typename_quals)
                                           ||
                                           (FStar_List.contains
                                              FStar_Syntax_Syntax.Abstract
                                              typename_quals));
                                      is_record = is_rec
                                    }  in
                                  ((let uu____8588 =
                                      let uu____8591 =
                                        FStar_ST.op_Bang new_globs  in
                                      (Record_or_dc record) :: uu____8591  in
                                    FStar_ST.op_Colon_Equals new_globs
                                      uu____8588);
                                   (match () with
                                    | () ->
                                        ((let add_field uu____8694 =
                                            match uu____8694 with
                                            | (id1,uu____8700) ->
                                                let modul =
                                                  let uu____8703 =
                                                    FStar_Ident.lid_of_ids
                                                      constrname.FStar_Ident.ns
                                                     in
                                                  uu____8703.FStar_Ident.str
                                                   in
                                                let uu____8704 =
                                                  get_exported_id_set e modul
                                                   in
                                                (match uu____8704 with
                                                 | FStar_Pervasives_Native.Some
                                                     my_ex ->
                                                     let my_exported_ids =
                                                       my_ex
                                                         Exported_id_field
                                                        in
                                                     ((let uu____8738 =
                                                         let uu____8739 =
                                                           FStar_ST.op_Bang
                                                             my_exported_ids
                                                            in
                                                         FStar_Util.set_add
                                                           id1.FStar_Ident.idText
                                                           uu____8739
                                                          in
                                                       FStar_ST.op_Colon_Equals
                                                         my_exported_ids
                                                         uu____8738);
                                                      (match () with
                                                       | () ->
                                                           let projname =
                                                             let uu____8828 =
                                                               let uu____8829
                                                                 =
                                                                 FStar_Syntax_Util.mk_field_projector_name_from_ident
                                                                   constrname
                                                                   id1
                                                                  in
                                                               uu____8829.FStar_Ident.ident
                                                                in
                                                             uu____8828.FStar_Ident.idText
                                                              in
                                                           let uu____8831 =
                                                             let uu____8832 =
                                                               FStar_ST.op_Bang
                                                                 my_exported_ids
                                                                in
                                                             FStar_Util.set_add
                                                               projname
                                                               uu____8832
                                                              in
                                                           FStar_ST.op_Colon_Equals
                                                             my_exported_ids
                                                             uu____8831))
                                                 | FStar_Pervasives_Native.None
                                                      -> ())
                                             in
                                          FStar_List.iter add_field fields');
                                         (match () with
                                          | () -> insert_record_cache record)))))
                         | uu____8928 -> ())
                    | uu____8929 -> ()))
        | uu____8930 -> ()
  
let (try_lookup_record_or_dc_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let find_in_cache fieldname1 =
        let uu____8952 =
          ((fieldname1.FStar_Ident.ns), (fieldname1.FStar_Ident.ident))  in
        match uu____8952 with
        | (ns,id1) ->
            let uu____8969 = peek_record_cache ()  in
            FStar_Util.find_map uu____8969
              (fun record  ->
                 let uu____8975 =
                   find_in_record ns id1 record (fun r  -> Cont_ok r)  in
                 option_of_cont
                   (fun uu____8981  -> FStar_Pervasives_Native.None)
                   uu____8975)
         in
      resolve_in_open_namespaces'' env fieldname Exported_id_field
        (fun uu____8983  -> Cont_ignore) (fun uu____8985  -> Cont_ignore)
        (fun r  -> Cont_ok r)
        (fun fn  ->
           let uu____8991 = find_in_cache fn  in
           cont_of_option Cont_ignore uu____8991)
        (fun k  -> fun uu____8997  -> k)
  
let (try_lookup_record_by_field_name :
  env -> FStar_Ident.lident -> record_or_dc FStar_Pervasives_Native.option) =
  fun env  ->
    fun fieldname  ->
      let uu____9013 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____9013 with
      | FStar_Pervasives_Native.Some r when r.is_record ->
          FStar_Pervasives_Native.Some r
      | uu____9019 -> FStar_Pervasives_Native.None
  
let (belongs_to_record :
  env -> FStar_Ident.lident -> record_or_dc -> Prims.bool) =
  fun env  ->
    fun lid  ->
      fun record  ->
        let uu____9039 = try_lookup_record_by_field_name env lid  in
        match uu____9039 with
        | FStar_Pervasives_Native.Some record' when
            let uu____9044 =
              let uu____9046 =
                FStar_Ident.path_of_ns (record.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____9046  in
            let uu____9047 =
              let uu____9049 =
                FStar_Ident.path_of_ns (record'.typename).FStar_Ident.ns  in
              FStar_Ident.text_of_path uu____9049  in
            uu____9044 = uu____9047 ->
            let uu____9051 =
              find_in_record (record.typename).FStar_Ident.ns
                lid.FStar_Ident.ident record (fun uu____9055  -> Cont_ok ())
               in
            (match uu____9051 with
             | Cont_ok uu____9057 -> true
             | uu____9059 -> false)
        | uu____9063 -> false
  
let (try_lookup_dc_by_field_name :
  env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fieldname  ->
      let uu____9085 = try_lookup_record_or_dc_by_field_name env fieldname
         in
      match uu____9085 with
      | FStar_Pervasives_Native.Some r ->
          let uu____9096 =
            let uu____9102 =
              let uu____9103 =
                FStar_Ident.lid_of_ids
                  (FStar_List.append (r.typename).FStar_Ident.ns
                     [r.constrname])
                 in
              let uu____9104 = FStar_Ident.range_of_lid fieldname  in
              FStar_Ident.set_lid_range uu____9103 uu____9104  in
            (uu____9102, (r.is_record))  in
          FStar_Pervasives_Native.Some uu____9096
      | uu____9111 -> FStar_Pervasives_Native.None
  
let (string_set_ref_new : unit -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____9140  ->
    let uu____9141 = FStar_Util.new_set FStar_Util.compare  in
    FStar_Util.mk_ref uu____9141
  
let (exported_id_set_new :
  unit -> exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref) =
  fun uu____9173  ->
    let term_type_set = string_set_ref_new ()  in
    let field_set = string_set_ref_new ()  in
    fun uu___199_9186  ->
      match uu___199_9186 with
      | Exported_id_term_type  -> term_type_set
      | Exported_id_field  -> field_set
  
let (unique :
  Prims.bool -> Prims.bool -> env -> FStar_Ident.lident -> Prims.bool) =
  fun any_val  ->
    fun exclude_interface  ->
      fun env  ->
        fun lid  ->
          let filter_scope_mods uu___200_9246 =
            match uu___200_9246 with
            | Rec_binding uu____9248 -> true
            | uu____9250 -> false  in
          let this_env =
            let uu___215_9253 = env  in
            let uu____9254 =
              FStar_List.filter filter_scope_mods env.scope_mods  in
            {
              curmodule = (uu___215_9253.curmodule);
              curmonad = (uu___215_9253.curmonad);
              modules = (uu___215_9253.modules);
              scope_mods = uu____9254;
              exported_ids = empty_exported_id_smap;
              trans_exported_ids = (uu___215_9253.trans_exported_ids);
              includes = empty_include_smap;
              sigaccum = (uu___215_9253.sigaccum);
              sigmap = (uu___215_9253.sigmap);
              iface = (uu___215_9253.iface);
              admitted_iface = (uu___215_9253.admitted_iface);
              expect_typ = (uu___215_9253.expect_typ);
              docs = (uu___215_9253.docs);
              remaining_iface_decls = (uu___215_9253.remaining_iface_decls);
              syntax_only = (uu___215_9253.syntax_only);
              ds_hooks = (uu___215_9253.ds_hooks);
              dep_graph = (uu___215_9253.dep_graph)
            }  in
          let uu____9257 =
            try_lookup_lid' any_val exclude_interface this_env lid  in
          match uu____9257 with
          | FStar_Pervasives_Native.None  -> true
          | FStar_Pervasives_Native.Some uu____9274 -> false
  
let (push_scope_mod : env -> scope_mod -> env) =
  fun env  ->
    fun scope_mod  ->
      let uu___216_9299 = env  in
      {
        curmodule = (uu___216_9299.curmodule);
        curmonad = (uu___216_9299.curmonad);
        modules = (uu___216_9299.modules);
        scope_mods = (scope_mod :: (env.scope_mods));
        exported_ids = (uu___216_9299.exported_ids);
        trans_exported_ids = (uu___216_9299.trans_exported_ids);
        includes = (uu___216_9299.includes);
        sigaccum = (uu___216_9299.sigaccum);
        sigmap = (uu___216_9299.sigmap);
        iface = (uu___216_9299.iface);
        admitted_iface = (uu___216_9299.admitted_iface);
        expect_typ = (uu___216_9299.expect_typ);
        docs = (uu___216_9299.docs);
        remaining_iface_decls = (uu___216_9299.remaining_iface_decls);
        syntax_only = (uu___216_9299.syntax_only);
        ds_hooks = (uu___216_9299.ds_hooks);
        dep_graph = (uu___216_9299.dep_graph)
      }
  
let (push_bv : env -> FStar_Ident.ident -> (env * FStar_Syntax_Syntax.bv)) =
  fun env  ->
    fun x  ->
      let bv =
        FStar_Syntax_Syntax.gen_bv x.FStar_Ident.idText
          (FStar_Pervasives_Native.Some (x.FStar_Ident.idRange))
          FStar_Syntax_Syntax.tun
         in
      ((push_scope_mod env (Local_binding (x, bv))), bv)
  
let (push_top_level_rec_binding :
  env -> FStar_Ident.ident -> FStar_Syntax_Syntax.delta_depth -> env) =
  fun env  ->
    fun x  ->
      fun dd  ->
        let l = qualify env x  in
        let uu____9333 =
          (unique false true env l) || (FStar_Options.interactive ())  in
        if uu____9333
        then push_scope_mod env (Rec_binding (x, l, dd))
        else
          (let uu____9340 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_DuplicateTopLevelNames,
               (Prims.strcat "Duplicate top-level names " l.FStar_Ident.str))
             uu____9340)
  
let (push_sigelt' : Prims.bool -> env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun fail_on_dup  ->
    fun env  ->
      fun s  ->
        let err l =
          let sopt = FStar_Util.smap_try_find (sigmap env) l.FStar_Ident.str
             in
          let r =
            match sopt with
            | FStar_Pervasives_Native.Some (se,uu____9384) ->
                let uu____9392 =
                  FStar_Util.find_opt (FStar_Ident.lid_equals l)
                    (FStar_Syntax_Util.lids_of_sigelt se)
                   in
                (match uu____9392 with
                 | FStar_Pervasives_Native.Some l1 ->
                     let uu____9397 = FStar_Ident.range_of_lid l1  in
                     FStar_All.pipe_left FStar_Range.string_of_range
                       uu____9397
                 | FStar_Pervasives_Native.None  -> "<unknown>")
            | FStar_Pervasives_Native.None  -> "<unknown>"  in
          let uu____9406 =
            let uu____9412 =
              let uu____9414 = FStar_Ident.text_of_lid l  in
              FStar_Util.format2
                "Duplicate top-level names [%s]; previously declared at %s"
                uu____9414 r
               in
            (FStar_Errors.Fatal_DuplicateTopLevelNames, uu____9412)  in
          let uu____9418 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____9406 uu____9418  in
        let globals = FStar_Util.mk_ref env.scope_mods  in
        let env1 =
          let uu____9427 =
            match s.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let uu____9440 -> (false, true)
            | FStar_Syntax_Syntax.Sig_bundle uu____9451 -> (false, true)
            | uu____9464 -> (false, false)  in
          match uu____9427 with
          | (any_val,exclude_interface) ->
              let lids = FStar_Syntax_Util.lids_of_sigelt s  in
              let uu____9478 =
                FStar_Util.find_map lids
                  (fun l  ->
                     let uu____9484 =
                       let uu____9486 =
                         unique any_val exclude_interface env l  in
                       Prims.op_Negation uu____9486  in
                     if uu____9484
                     then FStar_Pervasives_Native.Some l
                     else FStar_Pervasives_Native.None)
                 in
              (match uu____9478 with
               | FStar_Pervasives_Native.Some l when fail_on_dup -> err l
               | uu____9494 ->
                   (extract_record env globals s;
                    (let uu___217_9520 = env  in
                     {
                       curmodule = (uu___217_9520.curmodule);
                       curmonad = (uu___217_9520.curmonad);
                       modules = (uu___217_9520.modules);
                       scope_mods = (uu___217_9520.scope_mods);
                       exported_ids = (uu___217_9520.exported_ids);
                       trans_exported_ids =
                         (uu___217_9520.trans_exported_ids);
                       includes = (uu___217_9520.includes);
                       sigaccum = (s :: (env.sigaccum));
                       sigmap = (uu___217_9520.sigmap);
                       iface = (uu___217_9520.iface);
                       admitted_iface = (uu___217_9520.admitted_iface);
                       expect_typ = (uu___217_9520.expect_typ);
                       docs = (uu___217_9520.docs);
                       remaining_iface_decls =
                         (uu___217_9520.remaining_iface_decls);
                       syntax_only = (uu___217_9520.syntax_only);
                       ds_hooks = (uu___217_9520.ds_hooks);
                       dep_graph = (uu___217_9520.dep_graph)
                     })))
           in
        let env2 =
          let uu___218_9522 = env1  in
          let uu____9523 = FStar_ST.op_Bang globals  in
          {
            curmodule = (uu___218_9522.curmodule);
            curmonad = (uu___218_9522.curmonad);
            modules = (uu___218_9522.modules);
            scope_mods = uu____9523;
            exported_ids = (uu___218_9522.exported_ids);
            trans_exported_ids = (uu___218_9522.trans_exported_ids);
            includes = (uu___218_9522.includes);
            sigaccum = (uu___218_9522.sigaccum);
            sigmap = (uu___218_9522.sigmap);
            iface = (uu___218_9522.iface);
            admitted_iface = (uu___218_9522.admitted_iface);
            expect_typ = (uu___218_9522.expect_typ);
            docs = (uu___218_9522.docs);
            remaining_iface_decls = (uu___218_9522.remaining_iface_decls);
            syntax_only = (uu___218_9522.syntax_only);
            ds_hooks = (uu___218_9522.ds_hooks);
            dep_graph = (uu___218_9522.dep_graph)
          }  in
        let uu____9571 =
          match s.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses,uu____9597) ->
              let uu____9606 =
                FStar_List.map
                  (fun se  -> ((FStar_Syntax_Util.lids_of_sigelt se), se))
                  ses
                 in
              (env2, uu____9606)
          | uu____9633 -> (env2, [((FStar_Syntax_Util.lids_of_sigelt s), s)])
           in
        match uu____9571 with
        | (env3,lss) ->
            (FStar_All.pipe_right lss
               (FStar_List.iter
                  (fun uu____9692  ->
                     match uu____9692 with
                     | (lids,se) ->
                         FStar_All.pipe_right lids
                           (FStar_List.iter
                              (fun lid  ->
                                 (let uu____9714 =
                                    let uu____9717 = FStar_ST.op_Bang globals
                                       in
                                    (Top_level_def (lid.FStar_Ident.ident))
                                      :: uu____9717
                                     in
                                  FStar_ST.op_Colon_Equals globals uu____9714);
                                 (match () with
                                  | () ->
                                      let modul =
                                        let uu____9812 =
                                          FStar_Ident.lid_of_ids
                                            lid.FStar_Ident.ns
                                           in
                                        uu____9812.FStar_Ident.str  in
                                      ((let uu____9814 =
                                          get_exported_id_set env3 modul  in
                                        match uu____9814 with
                                        | FStar_Pervasives_Native.Some f ->
                                            let my_exported_ids =
                                              f Exported_id_term_type  in
                                            let uu____9847 =
                                              let uu____9848 =
                                                FStar_ST.op_Bang
                                                  my_exported_ids
                                                 in
                                              FStar_Util.set_add
                                                (lid.FStar_Ident.ident).FStar_Ident.idText
                                                uu____9848
                                               in
                                            FStar_ST.op_Colon_Equals
                                              my_exported_ids uu____9847
                                        | FStar_Pervasives_Native.None  -> ());
                                       (match () with
                                        | () ->
                                            let is_iface =
                                              env3.iface &&
                                                (Prims.op_Negation
                                                   env3.admitted_iface)
                                               in
                                            FStar_Util.smap_add (sigmap env3)
                                              lid.FStar_Ident.str
                                              (se,
                                                (env3.iface &&
                                                   (Prims.op_Negation
                                                      env3.admitted_iface))))))))));
             (let env4 =
                let uu___219_9949 = env3  in
                let uu____9950 = FStar_ST.op_Bang globals  in
                {
                  curmodule = (uu___219_9949.curmodule);
                  curmonad = (uu___219_9949.curmonad);
                  modules = (uu___219_9949.modules);
                  scope_mods = uu____9950;
                  exported_ids = (uu___219_9949.exported_ids);
                  trans_exported_ids = (uu___219_9949.trans_exported_ids);
                  includes = (uu___219_9949.includes);
                  sigaccum = (uu___219_9949.sigaccum);
                  sigmap = (uu___219_9949.sigmap);
                  iface = (uu___219_9949.iface);
                  admitted_iface = (uu___219_9949.admitted_iface);
                  expect_typ = (uu___219_9949.expect_typ);
                  docs = (uu___219_9949.docs);
                  remaining_iface_decls =
                    (uu___219_9949.remaining_iface_decls);
                  syntax_only = (uu___219_9949.syntax_only);
                  ds_hooks = (uu___219_9949.ds_hooks);
                  dep_graph = (uu___219_9949.dep_graph)
                }  in
              env4))
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' true env se 
let (push_sigelt_force : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  -> fun se  -> push_sigelt' false env se 
let (push_namespace : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let uu____10033 =
        let uu____10038 = resolve_module_name env ns false  in
        match uu____10038 with
        | FStar_Pervasives_Native.None  ->
            let modules = env.modules  in
            let uu____10053 =
              FStar_All.pipe_right modules
                (FStar_Util.for_some
                   (fun uu____10071  ->
                      match uu____10071 with
                      | (m,uu____10078) ->
                          let uu____10079 =
                            let uu____10081 = FStar_Ident.text_of_lid m  in
                            Prims.strcat uu____10081 "."  in
                          let uu____10084 =
                            let uu____10086 = FStar_Ident.text_of_lid ns  in
                            Prims.strcat uu____10086 "."  in
                          FStar_Util.starts_with uu____10079 uu____10084))
               in
            if uu____10053
            then (ns, Open_namespace)
            else
              (let uu____10096 =
                 let uu____10102 =
                   let uu____10104 = FStar_Ident.text_of_lid ns  in
                   FStar_Util.format1 "Namespace %s cannot be found"
                     uu____10104
                    in
                 (FStar_Errors.Fatal_NameSpaceNotFound, uu____10102)  in
               let uu____10108 = FStar_Ident.range_of_lid ns  in
               FStar_Errors.raise_error uu____10096 uu____10108)
        | FStar_Pervasives_Native.Some ns' ->
            (fail_if_curmodule env ns ns'; (ns', Open_module))
         in
      match uu____10033 with
      | (ns',kd) ->
          ((env.ds_hooks).ds_push_open_hook env (ns', kd);
           push_scope_mod env (Open_module_or_namespace (ns', kd)))
  
let (push_include : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun ns  ->
      let ns0 = ns  in
      let uu____10130 = resolve_module_name env ns false  in
      match uu____10130 with
      | FStar_Pervasives_Native.Some ns1 ->
          ((env.ds_hooks).ds_push_include_hook env ns1;
           fail_if_curmodule env ns0 ns1;
           (let env1 =
              push_scope_mod env
                (Open_module_or_namespace (ns1, Open_module))
               in
            let curmod =
              let uu____10140 = current_module env1  in
              uu____10140.FStar_Ident.str  in
            (let uu____10142 = FStar_Util.smap_try_find env1.includes curmod
                in
             match uu____10142 with
             | FStar_Pervasives_Native.None  -> ()
             | FStar_Pervasives_Native.Some incl ->
                 let uu____10166 =
                   let uu____10169 = FStar_ST.op_Bang incl  in ns1 ::
                     uu____10169
                    in
                 FStar_ST.op_Colon_Equals incl uu____10166);
            (match () with
             | () ->
                 let uu____10262 =
                   get_trans_exported_id_set env1 ns1.FStar_Ident.str  in
                 (match uu____10262 with
                  | FStar_Pervasives_Native.Some ns_trans_exports ->
                      ((let uu____10282 =
                          let uu____10379 = get_exported_id_set env1 curmod
                             in
                          let uu____10426 =
                            get_trans_exported_id_set env1 curmod  in
                          (uu____10379, uu____10426)  in
                        match uu____10282 with
                        | (FStar_Pervasives_Native.Some
                           cur_exports,FStar_Pervasives_Native.Some
                           cur_trans_exports) ->
                            let update_exports k =
                              let ns_ex =
                                let uu____10842 = ns_trans_exports k  in
                                FStar_ST.op_Bang uu____10842  in
                              let ex = cur_exports k  in
                              (let uu____11017 =
                                 let uu____11021 = FStar_ST.op_Bang ex  in
                                 FStar_Util.set_difference uu____11021 ns_ex
                                  in
                               FStar_ST.op_Colon_Equals ex uu____11017);
                              (match () with
                               | () ->
                                   let trans_ex = cur_trans_exports k  in
                                   let uu____11218 =
                                     let uu____11222 =
                                       FStar_ST.op_Bang trans_ex  in
                                     FStar_Util.set_union uu____11222 ns_ex
                                      in
                                   FStar_ST.op_Colon_Equals trans_ex
                                     uu____11218)
                               in
                            FStar_List.iter update_exports
                              all_exported_id_kinds
                        | uu____11355 -> ());
                       (match () with | () -> env1))
                  | FStar_Pervasives_Native.None  ->
                      let uu____11457 =
                        let uu____11463 =
                          FStar_Util.format1
                            "include: Module %s was not prepared"
                            ns1.FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_IncludeModuleNotPrepared,
                          uu____11463)
                         in
                      let uu____11467 = FStar_Ident.range_of_lid ns1  in
                      FStar_Errors.raise_error uu____11457 uu____11467))))
      | uu____11468 ->
          let uu____11471 =
            let uu____11477 =
              FStar_Util.format1 "include: Module %s cannot be found"
                ns.FStar_Ident.str
               in
            (FStar_Errors.Fatal_ModuleNotFound, uu____11477)  in
          let uu____11481 = FStar_Ident.range_of_lid ns  in
          FStar_Errors.raise_error uu____11471 uu____11481
  
let (push_module_abbrev :
  env -> FStar_Ident.ident -> FStar_Ident.lident -> env) =
  fun env  ->
    fun x  ->
      fun l  ->
        let uu____11498 = module_is_defined env l  in
        if uu____11498
        then
          (fail_if_curmodule env l l;
           (env.ds_hooks).ds_push_module_abbrev_hook env x l;
           push_scope_mod env (Module_abbrev (x, l)))
        else
          (let uu____11505 =
             let uu____11511 =
               let uu____11513 = FStar_Ident.text_of_lid l  in
               FStar_Util.format1 "Module %s cannot be found" uu____11513  in
             (FStar_Errors.Fatal_ModuleNotFound, uu____11511)  in
           let uu____11517 = FStar_Ident.range_of_lid l  in
           FStar_Errors.raise_error uu____11505 uu____11517)
  
let (push_doc :
  env ->
    FStar_Ident.lident ->
      FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option -> env)
  =
  fun env  ->
    fun l  ->
      fun doc_opt  ->
        match doc_opt with
        | FStar_Pervasives_Native.None  -> env
        | FStar_Pervasives_Native.Some doc1 ->
            ((let uu____11540 =
                FStar_Util.smap_try_find env.docs l.FStar_Ident.str  in
              match uu____11540 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some old_doc ->
                  let uu____11544 = FStar_Ident.range_of_lid l  in
                  let uu____11545 =
                    let uu____11551 =
                      let uu____11553 = FStar_Ident.string_of_lid l  in
                      let uu____11555 =
                        FStar_Parser_AST.string_of_fsdoc old_doc  in
                      let uu____11557 = FStar_Parser_AST.string_of_fsdoc doc1
                         in
                      FStar_Util.format3
                        "Overwriting doc of %s; old doc was [%s]; new doc are [%s]"
                        uu____11553 uu____11555 uu____11557
                       in
                    (FStar_Errors.Warning_DocOverwrite, uu____11551)  in
                  FStar_Errors.log_issue uu____11544 uu____11545);
             FStar_Util.smap_add env.docs l.FStar_Ident.str doc1;
             env)
  
let (check_admits :
  env -> FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul) =
  fun env  ->
    fun m  ->
      let admitted_sig_lids =
        FStar_All.pipe_right env.sigaccum
          (FStar_List.fold_left
             (fun lids  ->
                fun se  ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) when
                      let uu____11603 =
                        FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption)
                         in
                      Prims.op_Negation uu____11603 ->
                      let uu____11608 =
                        FStar_Util.smap_try_find (sigmap env)
                          l.FStar_Ident.str
                         in
                      (match uu____11608 with
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_let uu____11623;
                              FStar_Syntax_Syntax.sigrng = uu____11624;
                              FStar_Syntax_Syntax.sigquals = uu____11625;
                              FStar_Syntax_Syntax.sigmeta = uu____11626;
                              FStar_Syntax_Syntax.sigattrs = uu____11627;_},uu____11628)
                           -> lids
                       | FStar_Pervasives_Native.Some
                           ({
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_inductive_typ
                                uu____11646;
                              FStar_Syntax_Syntax.sigrng = uu____11647;
                              FStar_Syntax_Syntax.sigquals = uu____11648;
                              FStar_Syntax_Syntax.sigmeta = uu____11649;
                              FStar_Syntax_Syntax.sigattrs = uu____11650;_},uu____11651)
                           -> lids
                       | uu____11679 ->
                           ((let uu____11688 =
                               let uu____11690 = FStar_Options.interactive ()
                                  in
                               Prims.op_Negation uu____11690  in
                             if uu____11688
                             then
                               let uu____11693 = FStar_Ident.range_of_lid l
                                  in
                               let uu____11694 =
                                 let uu____11700 =
                                   let uu____11702 =
                                     FStar_Ident.string_of_lid l  in
                                   FStar_Util.format1
                                     "Admitting %s without a definition"
                                     uu____11702
                                    in
                                 (FStar_Errors.Warning_AdmitWithoutDefinition,
                                   uu____11700)
                                  in
                               FStar_Errors.log_issue uu____11693 uu____11694
                             else ());
                            (let quals = FStar_Syntax_Syntax.Assumption ::
                               (se.FStar_Syntax_Syntax.sigquals)  in
                             FStar_Util.smap_add (sigmap env)
                               l.FStar_Ident.str
                               ((let uu___220_11719 = se  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (uu___220_11719.FStar_Syntax_Syntax.sigel);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___220_11719.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___220_11719.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___220_11719.FStar_Syntax_Syntax.sigattrs)
                                 }), false);
                             l
                             ::
                             lids)))
                  | uu____11721 -> lids) [])
         in
      let uu___221_11722 = m  in
      let uu____11723 =
        FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
          (FStar_List.map
             (fun s  ->
                match s.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_declare_typ
                    (lid,uu____11733,uu____11734) when
                    FStar_List.existsb
                      (fun l  -> FStar_Ident.lid_equals l lid)
                      admitted_sig_lids
                    ->
                    let uu___222_11737 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___222_11737.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___222_11737.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (FStar_Syntax_Syntax.Assumption ::
                        (s.FStar_Syntax_Syntax.sigquals));
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___222_11737.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___222_11737.FStar_Syntax_Syntax.sigattrs)
                    }
                | uu____11738 -> s))
         in
      {
        FStar_Syntax_Syntax.name = (uu___221_11722.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____11723;
        FStar_Syntax_Syntax.exports =
          (uu___221_11722.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface =
          (uu___221_11722.FStar_Syntax_Syntax.is_interface)
      }
  
let (finish : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun modul  ->
      FStar_All.pipe_right modul.FStar_Syntax_Syntax.declarations
        (FStar_List.iter
           (fun se  ->
              let quals = se.FStar_Syntax_Syntax.sigquals  in
              match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11762) ->
                  if
                    (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                      ||
                      (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                  then
                    FStar_All.pipe_right ses
                      (FStar_List.iter
                         (fun se1  ->
                            match se1.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_datacon
                                (lid,uu____11783,uu____11784,uu____11785,uu____11786,uu____11787)
                                ->
                                FStar_Util.smap_remove (sigmap env)
                                  lid.FStar_Ident.str
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,univ_names,binders,typ,uu____11803,uu____11804)
                                ->
                                (FStar_Util.smap_remove (sigmap env)
                                   lid.FStar_Ident.str;
                                 if
                                   Prims.op_Negation
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Private quals)
                                 then
                                   (let sigel =
                                      let uu____11821 =
                                        let uu____11828 =
                                          let uu____11829 =
                                            FStar_Ident.range_of_lid lid  in
                                          let uu____11830 =
                                            let uu____11837 =
                                              let uu____11838 =
                                                let uu____11853 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    typ
                                                   in
                                                (binders, uu____11853)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____11838
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____11837
                                             in
                                          uu____11830
                                            FStar_Pervasives_Native.None
                                            uu____11829
                                           in
                                        (lid, univ_names, uu____11828)  in
                                      FStar_Syntax_Syntax.Sig_declare_typ
                                        uu____11821
                                       in
                                    let se2 =
                                      let uu___223_11870 = se1  in
                                      {
                                        FStar_Syntax_Syntax.sigel = sigel;
                                        FStar_Syntax_Syntax.sigrng =
                                          (uu___223_11870.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (FStar_Syntax_Syntax.Assumption ::
                                          quals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (uu___223_11870.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (uu___223_11870.FStar_Syntax_Syntax.sigattrs)
                                      }  in
                                    FStar_Util.smap_add (sigmap env)
                                      lid.FStar_Ident.str (se2, false))
                                 else ())
                            | uu____11880 -> ()))
                  else ()
              | FStar_Syntax_Syntax.Sig_declare_typ
                  (lid,uu____11884,uu____11885) ->
                  if FStar_List.contains FStar_Syntax_Syntax.Private quals
                  then
                    FStar_Util.smap_remove (sigmap env) lid.FStar_Ident.str
                  else ()
              | FStar_Syntax_Syntax.Sig_let ((uu____11894,lbs),uu____11896)
                  ->
                  (if
                     (FStar_List.contains FStar_Syntax_Syntax.Private quals)
                       ||
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract
                          quals)
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let uu____11914 =
                               let uu____11916 =
                                 let uu____11917 =
                                   let uu____11920 =
                                     FStar_Util.right
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   uu____11920.FStar_Syntax_Syntax.fv_name
                                    in
                                 uu____11917.FStar_Syntax_Syntax.v  in
                               uu____11916.FStar_Ident.str  in
                             FStar_Util.smap_remove (sigmap env) uu____11914))
                   else ();
                   if
                     (FStar_List.contains FStar_Syntax_Syntax.Abstract quals)
                       &&
                       (Prims.op_Negation
                          (FStar_List.contains FStar_Syntax_Syntax.Private
                             quals))
                   then
                     FStar_All.pipe_right lbs
                       (FStar_List.iter
                          (fun lb  ->
                             let lid =
                               let uu____11937 =
                                 let uu____11940 =
                                   FStar_Util.right
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 uu____11940.FStar_Syntax_Syntax.fv_name  in
                               uu____11937.FStar_Syntax_Syntax.v  in
                             let quals1 = FStar_Syntax_Syntax.Assumption ::
                               quals  in
                             let decl =
                               let uu___224_11945 = se  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                        (lb.FStar_Syntax_Syntax.lbtyp)));
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___224_11945.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals = quals1;
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___224_11945.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___224_11945.FStar_Syntax_Syntax.sigattrs)
                               }  in
                             FStar_Util.smap_add (sigmap env)
                               lid.FStar_Ident.str (decl, false)))
                   else ())
              | uu____11955 -> ()));
      (let curmod =
         let uu____11958 = current_module env  in uu____11958.FStar_Ident.str
          in
       (let uu____11960 =
          let uu____12057 = get_exported_id_set env curmod  in
          let uu____12104 = get_trans_exported_id_set env curmod  in
          (uu____12057, uu____12104)  in
        match uu____11960 with
        | (FStar_Pervasives_Native.Some cur_ex,FStar_Pervasives_Native.Some
           cur_trans_ex) ->
            let update_exports eikind =
              let cur_ex_set =
                let uu____12523 = cur_ex eikind  in
                FStar_ST.op_Bang uu____12523  in
              let cur_trans_ex_set_ref = cur_trans_ex eikind  in
              let uu____12713 =
                let uu____12717 = FStar_ST.op_Bang cur_trans_ex_set_ref  in
                FStar_Util.set_union cur_ex_set uu____12717  in
              FStar_ST.op_Colon_Equals cur_trans_ex_set_ref uu____12713  in
            FStar_List.iter update_exports all_exported_id_kinds
        | uu____12850 -> ());
       (match () with
        | () ->
            (filter_record_cache ();
             (match () with
              | () ->
                  let uu___225_12948 = env  in
                  {
                    curmodule = FStar_Pervasives_Native.None;
                    curmonad = (uu___225_12948.curmonad);
                    modules = (((modul.FStar_Syntax_Syntax.name), modul) ::
                      (env.modules));
                    scope_mods = [];
                    exported_ids = (uu___225_12948.exported_ids);
                    trans_exported_ids = (uu___225_12948.trans_exported_ids);
                    includes = (uu___225_12948.includes);
                    sigaccum = [];
                    sigmap = (uu___225_12948.sigmap);
                    iface = (uu___225_12948.iface);
                    admitted_iface = (uu___225_12948.admitted_iface);
                    expect_typ = (uu___225_12948.expect_typ);
                    docs = (uu___225_12948.docs);
                    remaining_iface_decls =
                      (uu___225_12948.remaining_iface_decls);
                    syntax_only = (uu___225_12948.syntax_only);
                    ds_hooks = (uu___225_12948.ds_hooks);
                    dep_graph = (uu___225_12948.dep_graph)
                  }))))
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push : env -> env) =
  fun env  ->
    FStar_Util.atomically
      (fun uu____12986  ->
         push_record_cache ();
         (let uu____12989 =
            let uu____12992 = FStar_ST.op_Bang stack  in env :: uu____12992
             in
          FStar_ST.op_Colon_Equals stack uu____12989);
         (let uu___226_13041 = env  in
          let uu____13042 = FStar_Util.smap_copy env.exported_ids  in
          let uu____13047 = FStar_Util.smap_copy env.trans_exported_ids  in
          let uu____13052 = FStar_Util.smap_copy env.includes  in
          let uu____13063 = FStar_Util.smap_copy env.sigmap  in
          let uu____13076 = FStar_Util.smap_copy env.docs  in
          {
            curmodule = (uu___226_13041.curmodule);
            curmonad = (uu___226_13041.curmonad);
            modules = (uu___226_13041.modules);
            scope_mods = (uu___226_13041.scope_mods);
            exported_ids = uu____13042;
            trans_exported_ids = uu____13047;
            includes = uu____13052;
            sigaccum = (uu___226_13041.sigaccum);
            sigmap = uu____13063;
            iface = (uu___226_13041.iface);
            admitted_iface = (uu___226_13041.admitted_iface);
            expect_typ = (uu___226_13041.expect_typ);
            docs = uu____13076;
            remaining_iface_decls = (uu___226_13041.remaining_iface_decls);
            syntax_only = (uu___226_13041.syntax_only);
            ds_hooks = (uu___226_13041.ds_hooks);
            dep_graph = (uu___226_13041.dep_graph)
          }))
  
let (pop : unit -> env) =
  fun uu____13084  ->
    FStar_Util.atomically
      (fun uu____13091  ->
         let uu____13092 = FStar_ST.op_Bang stack  in
         match uu____13092 with
         | env::tl1 ->
             (pop_record_cache (); FStar_ST.op_Colon_Equals stack tl1; env)
         | uu____13147 -> failwith "Impossible: Too many pops")
  
let (snapshot : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push stack env 
let (rollback : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop stack depth 
let (export_interface : FStar_Ident.lident -> env -> env) =
  fun m  ->
    fun env  ->
      let sigelt_in_m se =
        match FStar_Syntax_Util.lids_of_sigelt se with
        | l::uu____13194 -> l.FStar_Ident.nsstr = m.FStar_Ident.str
        | uu____13198 -> false  in
      let sm = sigmap env  in
      let env1 = pop ()  in
      let keys = FStar_Util.smap_keys sm  in
      let sm' = sigmap env1  in
      FStar_All.pipe_right keys
        (FStar_List.iter
           (fun k  ->
              let uu____13240 = FStar_Util.smap_try_find sm' k  in
              match uu____13240 with
              | FStar_Pervasives_Native.Some (se,true ) when sigelt_in_m se
                  ->
                  (FStar_Util.smap_remove sm' k;
                   (let se1 =
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_declare_typ (l,u,t) ->
                          let uu___227_13271 = se  in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (uu___227_13271.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (uu___227_13271.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (FStar_Syntax_Syntax.Assumption ::
                              (se.FStar_Syntax_Syntax.sigquals));
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___227_13271.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___227_13271.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____13272 -> se  in
                    FStar_Util.smap_add sm' k (se1, false)))
              | uu____13280 -> ()));
      env1
  
let (finish_module_or_interface :
  env -> FStar_Syntax_Syntax.modul -> (env * FStar_Syntax_Syntax.modul)) =
  fun env  ->
    fun modul  ->
      let modul1 =
        if Prims.op_Negation modul.FStar_Syntax_Syntax.is_interface
        then check_admits env modul
        else modul  in
      let uu____13307 = finish env modul1  in (uu____13307, modul1)
  
type exported_ids =
  {
  exported_id_terms: Prims.string Prims.list ;
  exported_id_fields: Prims.string Prims.list }
let (__proj__Mkexported_ids__item__exported_id_terms :
  exported_ids -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { exported_id_terms; exported_id_fields;_} -> exported_id_terms
  
let (__proj__Mkexported_ids__item__exported_id_fields :
  exported_ids -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { exported_id_terms; exported_id_fields;_} -> exported_id_fields
  
let (as_exported_ids : exported_id_set -> exported_ids) =
  fun e  ->
    let terms =
      let uu____13409 =
        let uu____13413 = e Exported_id_term_type  in
        FStar_ST.op_Bang uu____13413  in
      FStar_Util.set_elements uu____13409  in
    let fields =
      let uu____13529 =
        let uu____13533 = e Exported_id_field  in
        FStar_ST.op_Bang uu____13533  in
      FStar_Util.set_elements uu____13529  in
    { exported_id_terms = terms; exported_id_fields = fields }
  
let (as_exported_id_set :
  exported_ids FStar_Pervasives_Native.option ->
    exported_id_kind -> Prims.string FStar_Util.set FStar_ST.ref)
  =
  fun e  ->
    match e with
    | FStar_Pervasives_Native.None  -> exported_id_set_new ()
    | FStar_Pervasives_Native.Some e1 ->
        let terms =
          let uu____13689 =
            FStar_Util.as_set e1.exported_id_terms FStar_Util.compare  in
          FStar_Util.mk_ref uu____13689  in
        let fields =
          let uu____13703 =
            FStar_Util.as_set e1.exported_id_fields FStar_Util.compare  in
          FStar_Util.mk_ref uu____13703  in
        (fun uu___201_13711  ->
           match uu___201_13711 with
           | Exported_id_term_type  -> terms
           | Exported_id_field  -> fields)
  
type module_inclusion_info =
  {
  mii_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_trans_exported_ids: exported_ids FStar_Pervasives_Native.option ;
  mii_includes: FStar_Ident.lident Prims.list FStar_Pervasives_Native.option }
let (__proj__Mkmodule_inclusion_info__item__mii_exported_ids :
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids; mii_trans_exported_ids; mii_includes;_} ->
        mii_exported_ids
  
let (__proj__Mkmodule_inclusion_info__item__mii_trans_exported_ids :
  module_inclusion_info -> exported_ids FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids; mii_trans_exported_ids; mii_includes;_} ->
        mii_trans_exported_ids
  
let (__proj__Mkmodule_inclusion_info__item__mii_includes :
  module_inclusion_info ->
    FStar_Ident.lident Prims.list FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { mii_exported_ids; mii_trans_exported_ids; mii_includes;_} ->
        mii_includes
  
let (default_mii : module_inclusion_info) =
  {
    mii_exported_ids = FStar_Pervasives_Native.None;
    mii_trans_exported_ids = FStar_Pervasives_Native.None;
    mii_includes = FStar_Pervasives_Native.None
  } 
let as_includes :
  'Auu____13848 .
    'Auu____13848 Prims.list FStar_Pervasives_Native.option ->
      'Auu____13848 Prims.list FStar_ST.ref
  =
  fun uu___202_13861  ->
    match uu___202_13861 with
    | FStar_Pervasives_Native.None  -> FStar_Util.mk_ref []
    | FStar_Pervasives_Native.Some l -> FStar_Util.mk_ref l
  
let (inclusion_info : env -> FStar_Ident.lident -> module_inclusion_info) =
  fun env  ->
    fun l  ->
      let mname = FStar_Ident.string_of_lid l  in
      let as_ids_opt m =
        let uu____13904 = FStar_Util.smap_try_find m mname  in
        FStar_Util.map_opt uu____13904 as_exported_ids  in
      let uu____13910 = as_ids_opt env.exported_ids  in
      let uu____13913 = as_ids_opt env.trans_exported_ids  in
      let uu____13916 =
        let uu____13921 = FStar_Util.smap_try_find env.includes mname  in
        FStar_Util.map_opt uu____13921 (fun r  -> FStar_ST.op_Bang r)  in
      {
        mii_exported_ids = uu____13910;
        mii_trans_exported_ids = uu____13913;
        mii_includes = uu____13916
      }
  
let (prepare_module_or_interface :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Ident.lident -> module_inclusion_info -> (env * Prims.bool))
  =
  fun intf  ->
    fun admitted  ->
      fun env  ->
        fun mname  ->
          fun mii  ->
            let prep env1 =
              let filename =
                let uu____14043 = FStar_Ident.text_of_lid mname  in
                FStar_Util.strcat uu____14043 ".fst"  in
              let auto_open =
                FStar_Parser_Dep.hard_coded_dependencies filename  in
              let auto_open1 =
                let convert_kind uu___203_14065 =
                  match uu___203_14065 with
                  | FStar_Parser_Dep.Open_namespace  -> Open_namespace
                  | FStar_Parser_Dep.Open_module  -> Open_module  in
                FStar_List.map
                  (fun uu____14077  ->
                     match uu____14077 with
                     | (lid,kind) -> (lid, (convert_kind kind))) auto_open
                 in
              let namespace_of_module =
                if
                  (FStar_List.length mname.FStar_Ident.ns) >
                    (Prims.parse_int "0")
                then
                  let uu____14103 =
                    let uu____14108 =
                      FStar_Ident.lid_of_ids mname.FStar_Ident.ns  in
                    (uu____14108, Open_namespace)  in
                  [uu____14103]
                else []  in
              let auto_open2 =
                FStar_List.append namespace_of_module
                  (FStar_List.rev auto_open1)
                 in
              (let uu____14139 = as_exported_id_set mii.mii_exported_ids  in
               FStar_Util.smap_add env1.exported_ids mname.FStar_Ident.str
                 uu____14139);
              (match () with
               | () ->
                   ((let uu____14166 =
                       as_exported_id_set mii.mii_trans_exported_ids  in
                     FStar_Util.smap_add env1.trans_exported_ids
                       mname.FStar_Ident.str uu____14166);
                    (match () with
                     | () ->
                         ((let uu____14193 = as_includes mii.mii_includes  in
                           FStar_Util.smap_add env1.includes
                             mname.FStar_Ident.str uu____14193);
                          (match () with
                           | () ->
                               let env' =
                                 let uu___228_14225 = env1  in
                                 let uu____14226 =
                                   FStar_List.map
                                     (fun x  -> Open_module_or_namespace x)
                                     auto_open2
                                    in
                                 {
                                   curmodule =
                                     (FStar_Pervasives_Native.Some mname);
                                   curmonad = (uu___228_14225.curmonad);
                                   modules = (uu___228_14225.modules);
                                   scope_mods = uu____14226;
                                   exported_ids =
                                     (uu___228_14225.exported_ids);
                                   trans_exported_ids =
                                     (uu___228_14225.trans_exported_ids);
                                   includes = (uu___228_14225.includes);
                                   sigaccum = (uu___228_14225.sigaccum);
                                   sigmap = (env1.sigmap);
                                   iface = intf;
                                   admitted_iface = admitted;
                                   expect_typ = (uu___228_14225.expect_typ);
                                   docs = (uu___228_14225.docs);
                                   remaining_iface_decls =
                                     (uu___228_14225.remaining_iface_decls);
                                   syntax_only = (uu___228_14225.syntax_only);
                                   ds_hooks = (uu___228_14225.ds_hooks);
                                   dep_graph = (uu___228_14225.dep_graph)
                                 }  in
                               (FStar_List.iter
                                  (fun op  ->
                                     (env1.ds_hooks).ds_push_open_hook env'
                                       op) (FStar_List.rev auto_open2);
                                env'))))))
               in
            let uu____14238 =
              FStar_All.pipe_right env.modules
                (FStar_Util.find_opt
                   (fun uu____14264  ->
                      match uu____14264 with
                      | (l,uu____14271) -> FStar_Ident.lid_equals l mname))
               in
            match uu____14238 with
            | FStar_Pervasives_Native.None  ->
                let uu____14281 = prep env  in (uu____14281, false)
            | FStar_Pervasives_Native.Some (uu____14284,m) ->
                ((let uu____14291 =
                    (let uu____14295 = FStar_Options.interactive ()  in
                     Prims.op_Negation uu____14295) &&
                      ((Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)
                         || intf)
                     in
                  if uu____14291
                  then
                    let uu____14298 =
                      let uu____14304 =
                        FStar_Util.format1
                          "Duplicate module or interface name: %s"
                          mname.FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DuplicateModuleOrInterface,
                        uu____14304)
                       in
                    let uu____14308 = FStar_Ident.range_of_lid mname  in
                    FStar_Errors.raise_error uu____14298 uu____14308
                  else ());
                 (let uu____14311 =
                    let uu____14312 = push env  in prep uu____14312  in
                  (uu____14311, true)))
  
let (enter_monad_scope : env -> FStar_Ident.ident -> env) =
  fun env  ->
    fun mname  ->
      match env.curmonad with
      | FStar_Pervasives_Native.Some mname' ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_MonadAlreadyDefined,
              (Prims.strcat "Trying to define monad "
                 (Prims.strcat mname.FStar_Ident.idText
                    (Prims.strcat ", but already in monad scope "
                       mname'.FStar_Ident.idText))))
            mname.FStar_Ident.idRange
      | FStar_Pervasives_Native.None  ->
          let uu___229_14330 = env  in
          {
            curmodule = (uu___229_14330.curmodule);
            curmonad = (FStar_Pervasives_Native.Some mname);
            modules = (uu___229_14330.modules);
            scope_mods = (uu___229_14330.scope_mods);
            exported_ids = (uu___229_14330.exported_ids);
            trans_exported_ids = (uu___229_14330.trans_exported_ids);
            includes = (uu___229_14330.includes);
            sigaccum = (uu___229_14330.sigaccum);
            sigmap = (uu___229_14330.sigmap);
            iface = (uu___229_14330.iface);
            admitted_iface = (uu___229_14330.admitted_iface);
            expect_typ = (uu___229_14330.expect_typ);
            docs = (uu___229_14330.docs);
            remaining_iface_decls = (uu___229_14330.remaining_iface_decls);
            syntax_only = (uu___229_14330.syntax_only);
            ds_hooks = (uu___229_14330.ds_hooks);
            dep_graph = (uu___229_14330.dep_graph)
          }
  
let fail_or :
  'a .
    env ->
      (FStar_Ident.lident -> 'a FStar_Pervasives_Native.option) ->
        FStar_Ident.lident -> 'a
  =
  fun env  ->
    fun lookup1  ->
      fun lid  ->
        let uu____14365 = lookup1 lid  in
        match uu____14365 with
        | FStar_Pervasives_Native.None  ->
            let opened_modules =
              FStar_List.map
                (fun uu____14380  ->
                   match uu____14380 with
                   | (lid1,uu____14387) -> FStar_Ident.text_of_lid lid1)
                env.modules
               in
            let msg =
              let uu____14390 = FStar_Ident.text_of_lid lid  in
              FStar_Util.format1 "Identifier not found: [%s]" uu____14390  in
            let msg1 =
              if
                (FStar_List.length lid.FStar_Ident.ns) =
                  (Prims.parse_int "0")
              then msg
              else
                (let modul =
                   let uu____14402 =
                     FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
                   let uu____14403 = FStar_Ident.range_of_lid lid  in
                   FStar_Ident.set_lid_range uu____14402 uu____14403  in
                 let uu____14404 = resolve_module_name env modul true  in
                 match uu____14404 with
                 | FStar_Pervasives_Native.None  ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules  in
                     FStar_Util.format3
                       "%s\nModule %s does not belong to the list of modules in scope, namely %s"
                       msg modul.FStar_Ident.str opened_modules1
                 | FStar_Pervasives_Native.Some modul' when
                     Prims.op_Negation
                       (FStar_List.existsb
                          (fun m  -> m = modul'.FStar_Ident.str)
                          opened_modules)
                     ->
                     let opened_modules1 =
                       FStar_String.concat ", " opened_modules  in
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, which does not belong to the list of modules in scope, namely %s"
                       msg modul.FStar_Ident.str modul'.FStar_Ident.str
                       opened_modules1
                 | FStar_Pervasives_Native.Some modul' ->
                     FStar_Util.format4
                       "%s\nModule %s resolved into %s, definition %s not found"
                       msg modul.FStar_Ident.str modul'.FStar_Ident.str
                       (lid.FStar_Ident.ident).FStar_Ident.idText)
               in
            let uu____14425 = FStar_Ident.range_of_lid lid  in
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_IdentifierNotFound, msg1) uu____14425
        | FStar_Pervasives_Native.Some r -> r
  
let fail_or2 :
  'a .
    (FStar_Ident.ident -> 'a FStar_Pervasives_Native.option) ->
      FStar_Ident.ident -> 'a
  =
  fun lookup1  ->
    fun id1  ->
      let uu____14455 = lookup1 id1  in
      match uu____14455 with
      | FStar_Pervasives_Native.None  ->
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_IdentifierNotFound,
              (Prims.strcat "Identifier not found ["
                 (Prims.strcat id1.FStar_Ident.idText "]")))
            id1.FStar_Ident.idRange
      | FStar_Pervasives_Native.Some r -> r
  
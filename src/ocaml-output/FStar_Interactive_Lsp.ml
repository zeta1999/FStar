open Prims
let (arg :
  Prims.string ->
    (Prims.string * FStar_Util.json) Prims.list -> FStar_Util.json)
  =
  fun k ->
    fun r ->
      let uu____31 =
        let uu____39 = FStar_JsonHelper.assoc "params" r in
        FStar_All.pipe_right uu____39 FStar_JsonHelper.js_assoc in
      FStar_JsonHelper.assoc k uu____31
let (unpack_lsp_query : FStar_Util.json -> FStar_JsonHelper.lsp_query) =
  fun json ->
    let r = FStar_All.pipe_right json FStar_JsonHelper.js_assoc in
    let qid =
      let uu____71 = FStar_JsonHelper.assoc "id" r in
      FStar_All.pipe_right uu____71 FStar_JsonHelper.js_str in
    try
      (fun uu___6_77 ->
         match () with
         | () ->
             let method_78 =
               let uu____80 = FStar_JsonHelper.assoc "method" r in
               FStar_All.pipe_right uu____80 FStar_JsonHelper.js_str in
             let uu____83 =
               match method_78 with
               | "initialize" ->
                   let uu____85 =
                     let uu____92 =
                       let uu____94 = arg "processId" r in
                       FStar_All.pipe_right uu____94 FStar_JsonHelper.js_int in
                     let uu____97 =
                       let uu____99 = arg "rootUri" r in
                       FStar_All.pipe_right uu____99 FStar_JsonHelper.js_str in
                     (uu____92, uu____97) in
                   FStar_JsonHelper.Initialize uu____85
               | "initialized" -> FStar_JsonHelper.Initialized
               | "shutdown" -> FStar_JsonHelper.Shutdown
               | "exit" -> FStar_JsonHelper.Exit
               | "$/cancelRequest" ->
                   let uu____108 =
                     let uu____110 = arg "id" r in
                     FStar_All.pipe_right uu____110 FStar_JsonHelper.js_str in
                   FStar_JsonHelper.Cancel uu____108
               | "workspace/didChangeWorkspaceFolders" ->
                   let uu____114 =
                     let uu____115 = arg "event" r in
                     FStar_All.pipe_right uu____115
                       FStar_JsonHelper.js_wsch_event in
                   FStar_JsonHelper.FolderChange uu____114
               | "workspace/didChangeConfiguration" ->
                   FStar_JsonHelper.ChangeConfig
               | "workspace/didChangeWatchedFiles" ->
                   FStar_JsonHelper.ChangeWatch
               | "workspace/symbol" ->
                   let uu____120 =
                     let uu____122 = arg "query" r in
                     FStar_All.pipe_right uu____122 FStar_JsonHelper.js_str in
                   FStar_JsonHelper.Symbol uu____120
               | "workspace/executeCommand" ->
                   let uu____126 =
                     let uu____128 = arg "command" r in
                     FStar_All.pipe_right uu____128 FStar_JsonHelper.js_str in
                   FStar_JsonHelper.ExecCommand uu____126
               | "textDocument/didOpen" ->
                   let uu____132 =
                     let uu____133 = arg "textDocument" r in
                     FStar_All.pipe_right uu____133
                       FStar_JsonHelper.js_txdoc_item in
                   FStar_JsonHelper.DidOpen uu____132
               | "textDocument/didChange" -> FStar_JsonHelper.DidChange
               | "textDocument/willSave" ->
                   let uu____137 =
                     let uu____139 = arg "textDocument" r in
                     FStar_All.pipe_right uu____139 FStar_JsonHelper.js_str in
                   FStar_JsonHelper.WillSave uu____137
               | "textDocument/didSave" ->
                   let uu____143 =
                     let uu____145 = arg "textDocument" r in
                     FStar_All.pipe_right uu____145 FStar_JsonHelper.js_str in
                   FStar_JsonHelper.DidSave uu____143
               | "textDocument/didClose" ->
                   let uu____149 =
                     let uu____151 = arg "textDocument" r in
                     FStar_All.pipe_right uu____151 FStar_JsonHelper.js_str in
                   FStar_JsonHelper.DidClose uu____149
               | "textDocument/completion" ->
                   let uu____155 =
                     let uu____156 = arg "context" r in
                     FStar_All.pipe_right uu____156
                       FStar_JsonHelper.js_compl_context in
                   FStar_JsonHelper.Completion uu____155
               | "completionItem/resolve" -> FStar_JsonHelper.Resolve
               | "textDocument/hover" -> FStar_JsonHelper.Hover
               | "textDocument/signatureHelp" ->
                   FStar_JsonHelper.SignatureHelp
               | "textDocument/declaration" -> FStar_JsonHelper.Declaration
               | "textDocument/definition" -> FStar_JsonHelper.Definition
               | "textDocument/implementation" ->
                   FStar_JsonHelper.Implementation
               | "textDocument/references" -> FStar_JsonHelper.References
               | "textDocument/documentHighlight" ->
                   FStar_JsonHelper.DocumentHighlight
               | "textDocument/documentSymbol" ->
                   FStar_JsonHelper.DocumentSymbol
               | "textDocument/codeAction" -> FStar_JsonHelper.CodeAction
               | "textDocument/codeLens" -> FStar_JsonHelper.CodeLens
               | "textDocument/documentLink" -> FStar_JsonHelper.DocumentLink
               | "textDocument/documentColor" ->
                   FStar_JsonHelper.DocumentColor
               | "textDocument/colorPresentation" ->
                   FStar_JsonHelper.ColorPresentation
               | "textDocument/formatting" -> FStar_JsonHelper.Formatting
               | "textDocument/rangeFormatting" ->
                   FStar_JsonHelper.RangeFormatting
               | "textDocument/onTypeFormatting" ->
                   FStar_JsonHelper.TypeFormatting
               | "textDocument/rename" -> FStar_JsonHelper.Rename
               | "textDocument/prepareRename" ->
                   FStar_JsonHelper.PrepareRename
               | "textDocument/foldingRange" -> FStar_JsonHelper.FoldingRange
               | m ->
                   let uu____180 = FStar_Util.format1 "Unknown method '%s'" m in
                   FStar_JsonHelper.BadProtocolMsg uu____180 in
             { FStar_JsonHelper.query_id = qid; FStar_JsonHelper.q = uu____83
             }) ()
    with
    | FStar_JsonHelper.MissingKey msg ->
        {
          FStar_JsonHelper.query_id = qid;
          FStar_JsonHelper.q = (FStar_JsonHelper.BadProtocolMsg msg)
        }
    | FStar_JsonHelper.UnexpectedJsonType (expected, got) ->
        FStar_JsonHelper.wrap_jsfail qid expected got
let (deserialize_lsp_query : FStar_Util.json -> FStar_JsonHelper.lsp_query) =
  fun js_query ->
    try
      (fun uu___56_199 -> match () with | () -> unpack_lsp_query js_query) ()
    with
    | FStar_JsonHelper.InvalidQuery msg ->
        {
          FStar_JsonHelper.query_id = "?";
          FStar_JsonHelper.q = (FStar_JsonHelper.BadProtocolMsg msg)
        }
    | FStar_JsonHelper.UnexpectedJsonType (expected, got) ->
        FStar_JsonHelper.wrap_jsfail "?" expected got
let (parse_lsp_query : Prims.string -> FStar_JsonHelper.lsp_query) =
  fun query_str ->
    let uu____219 = FStar_Util.json_of_string query_str in
    match uu____219 with
    | FStar_Pervasives_Native.None ->
        {
          FStar_JsonHelper.query_id = "?";
          FStar_JsonHelper.q =
            (FStar_JsonHelper.BadProtocolMsg "Json parsing failed")
        }
    | FStar_Pervasives_Native.Some request -> deserialize_lsp_query request
type repl_state =
  {
  repl_line: Prims.int ;
  repl_column: Prims.int ;
  repl_stdin: FStar_Util.stream_reader ;
  repl_last: FStar_JsonHelper.lquery ;
  repl_names: FStar_Interactive_CompletionTable.table }
let (__proj__Mkrepl_state__item__repl_line : repl_state -> Prims.int) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_stdin; repl_last; repl_names;_} ->
        repl_line
let (__proj__Mkrepl_state__item__repl_column : repl_state -> Prims.int) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_stdin; repl_last; repl_names;_} ->
        repl_column
let (__proj__Mkrepl_state__item__repl_stdin :
  repl_state -> FStar_Util.stream_reader) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_stdin; repl_last; repl_names;_} ->
        repl_stdin
let (__proj__Mkrepl_state__item__repl_last :
  repl_state -> FStar_JsonHelper.lquery) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_stdin; repl_last; repl_names;_} ->
        repl_last
let (__proj__Mkrepl_state__item__repl_names :
  repl_state -> FStar_Interactive_CompletionTable.table) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_stdin; repl_last; repl_names;_} ->
        repl_names
let (run_exit : repl_state -> Prims.int) =
  fun st ->
    if st.repl_last <> FStar_JsonHelper.Shutdown
    then (Prims.parse_int "1")
    else (Prims.parse_int "0")
let (run_query :
  repl_state ->
    FStar_JsonHelper.lquery ->
      ((FStar_Util.json, FStar_Util.json) FStar_Util.either * (repl_state,
        Prims.int) FStar_Util.either))
  =
  fun st ->
    fun q ->
      match q with
      | FStar_JsonHelper.Initialize (pid, rootUri) ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.Initialized ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.Shutdown ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.Exit ->
          let uu____408 =
            let uu____414 = run_exit st in FStar_Util.Inr uu____414 in
          ((FStar_Util.Inl FStar_Util.JsonNull), uu____408)
      | FStar_JsonHelper.Cancel id1 ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.FolderChange evt ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.ChangeConfig ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.ChangeWatch ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.Symbol sym ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.ExecCommand cmd ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.DidOpen item ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.DidChange ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.WillSave txid ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.DidSave txid ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.DidClose txid ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.Completion ctx ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.Resolve ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.Hover ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.SignatureHelp ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.Declaration ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.Definition ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.Implementation ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.References ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.DocumentHighlight ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.DocumentSymbol ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.CodeAction ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.CodeLens ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.DocumentLink ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.DocumentColor ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.ColorPresentation ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.Formatting ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.RangeFormatting ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.TypeFormatting ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.Rename ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.PrepareRename ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.FoldingRange ->
          ((FStar_Util.Inl FStar_Util.JsonNull), (FStar_Util.Inl st))
      | FStar_JsonHelper.BadProtocolMsg msg ->
          let uu____763 =
            let uu____768 =
              FStar_JsonHelper.js_resperr FStar_JsonHelper.MethodNotFound msg in
            FStar_Util.Inr uu____768 in
          (uu____763, (FStar_Util.Inl st))
let (json_of_response :
  Prims.string ->
    (FStar_Util.json, FStar_Util.json) FStar_Util.either -> FStar_Util.json)
  =
  fun qid ->
    fun response ->
      let qid1 = FStar_Util.JsonStr qid in
      match response with
      | FStar_Util.Inl result ->
          FStar_Util.JsonAssoc [("id", qid1); ("result", result)]
      | FStar_Util.Inr err ->
          FStar_Util.JsonAssoc [("id", qid1); ("error", err)]
let (read_lsp_query : FStar_Util.stream_reader -> FStar_JsonHelper.lsp_query)
  =
  fun stream ->
    let uu____847 = FStar_Util.read_line stream in
    match uu____847 with
    | FStar_Pervasives_Native.None -> FStar_All.exit (Prims.parse_int "0")
    | FStar_Pervasives_Native.Some line -> parse_lsp_query line
let rec (go : repl_state -> Prims.int) =
  fun st ->
    let query = read_lsp_query st.repl_stdin in
    let uu____865 = run_query st query.FStar_JsonHelper.q in
    match uu____865 with
    | (response, state_opt) ->
        (FStar_JsonHelper.write_json
           (json_of_response query.FStar_JsonHelper.query_id response);
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
let (initial_repl_state : repl_state) =
  let uu____908 = FStar_Util.open_stdin () in
  {
    repl_line = (Prims.parse_int "1");
    repl_column = (Prims.parse_int "0");
    repl_stdin = uu____908;
    repl_last = FStar_JsonHelper.Exit;
    repl_names = FStar_Interactive_CompletionTable.empty
  }
let (start_server : unit -> unit) =
  fun uu____916 ->
    let uu____917 = go initial_repl_state in FStar_All.exit uu____917
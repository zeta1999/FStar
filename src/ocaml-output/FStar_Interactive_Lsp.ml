open Prims
let (arg :
  Prims.string ->
    (Prims.string * FStar_Util.json) Prims.list -> FStar_Util.json)
  =
  fun k ->
    fun r ->
      let uu____26 =
        let uu____34 = FStar_JsonHelper.assoc "params" r in
        FStar_All.pipe_right uu____34 FStar_JsonHelper.js_assoc in
      FStar_JsonHelper.assoc k uu____26
let (unpack_lsp_query :
  (Prims.string * FStar_Util.json) Prims.list -> FStar_JsonHelper.lsp_query)
  =
  fun r ->
    let qid =
      let uu____67 = FStar_JsonHelper.try_assoc "id" r in
      FStar_All.pipe_right uu____67
        (FStar_Util.map_option FStar_JsonHelper.js_str_int) in
    try
      (fun uu___5_80 ->
         match () with
         | () ->
             let method_81 =
               let uu____83 = FStar_JsonHelper.assoc "method" r in
               FStar_All.pipe_right uu____83 FStar_JsonHelper.js_str in
             let uu____86 =
               match method_81 with
               | "initialize" ->
                   let uu____88 =
                     let uu____95 =
                       let uu____97 = arg "processId" r in
                       FStar_All.pipe_right uu____97 FStar_JsonHelper.js_int in
                     let uu____100 =
                       let uu____102 = arg "rootUri" r in
                       FStar_All.pipe_right uu____102 FStar_JsonHelper.js_str in
                     (uu____95, uu____100) in
                   FStar_JsonHelper.Initialize uu____88
               | "initialized" -> FStar_JsonHelper.Initialized
               | "shutdown" -> FStar_JsonHelper.Shutdown
               | "exit" -> FStar_JsonHelper.Exit
               | "$/cancelRequest" ->
                   let uu____111 =
                     let uu____113 = arg "id" r in
                     FStar_All.pipe_right uu____113 FStar_JsonHelper.js_str in
                   FStar_JsonHelper.Cancel uu____111
               | "workspace/didChangeWorkspaceFolders" ->
                   let uu____117 =
                     let uu____118 = arg "event" r in
                     FStar_All.pipe_right uu____118
                       FStar_JsonHelper.js_wsch_event in
                   FStar_JsonHelper.FolderChange uu____117
               | "workspace/didChangeConfiguration" ->
                   FStar_JsonHelper.ChangeConfig
               | "workspace/didChangeWatchedFiles" ->
                   FStar_JsonHelper.ChangeWatch
               | "workspace/symbol" ->
                   let uu____123 =
                     let uu____125 = arg "query" r in
                     FStar_All.pipe_right uu____125 FStar_JsonHelper.js_str in
                   FStar_JsonHelper.Symbol uu____123
               | "workspace/executeCommand" ->
                   let uu____129 =
                     let uu____131 = arg "command" r in
                     FStar_All.pipe_right uu____131 FStar_JsonHelper.js_str in
                   FStar_JsonHelper.ExecCommand uu____129
               | "textDocument/didOpen" ->
                   let uu____135 =
                     let uu____136 = arg "textDocument" r in
                     FStar_All.pipe_right uu____136
                       FStar_JsonHelper.js_txdoc_item in
                   FStar_JsonHelper.DidOpen uu____135
               | "textDocument/didChange" -> FStar_JsonHelper.DidChange
               | "textDocument/willSave" ->
                   let uu____140 =
                     let uu____142 = arg "textDocument" r in
                     FStar_All.pipe_right uu____142 FStar_JsonHelper.js_str in
                   FStar_JsonHelper.WillSave uu____140
               | "textDocument/didSave" ->
                   let uu____146 =
                     let uu____148 = arg "textDocument" r in
                     FStar_All.pipe_right uu____148 FStar_JsonHelper.js_str in
                   FStar_JsonHelper.DidSave uu____146
               | "textDocument/didClose" ->
                   let uu____152 =
                     let uu____154 = arg "textDocument" r in
                     FStar_All.pipe_right uu____154 FStar_JsonHelper.js_str in
                   FStar_JsonHelper.DidClose uu____152
               | "textDocument/completion" ->
                   let uu____158 =
                     let uu____159 = arg "context" r in
                     FStar_All.pipe_right uu____159
                       FStar_JsonHelper.js_compl_context in
                   FStar_JsonHelper.Completion uu____158
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
                   let uu____183 = FStar_Util.format1 "Unknown method '%s'" m in
                   FStar_JsonHelper.BadProtocolMsg uu____183 in
             { FStar_JsonHelper.query_id = qid; FStar_JsonHelper.q = uu____86
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
      (fun uu___55_203 ->
         match () with
         | () ->
             let uu____204 =
               FStar_All.pipe_right js_query FStar_JsonHelper.js_assoc in
             unpack_lsp_query uu____204) ()
    with
    | FStar_JsonHelper.UnexpectedJsonType (expected, got) ->
        FStar_JsonHelper.wrap_jsfail FStar_Pervasives_Native.None expected
          got
let (parse_lsp_query : Prims.string -> FStar_JsonHelper.lsp_query) =
  fun query_str ->
    FStar_Util.print1_error ">>> %s\n" query_str;
    (let uu____238 = FStar_Util.json_of_string query_str in
     match uu____238 with
     | FStar_Pervasives_Native.None ->
         {
           FStar_JsonHelper.query_id = FStar_Pervasives_Native.None;
           FStar_JsonHelper.q =
             (FStar_JsonHelper.BadProtocolMsg "Json parsing failed")
         }
     | FStar_Pervasives_Native.Some request -> deserialize_lsp_query request)
let (run_exit : FStar_JsonHelper.repl_state -> Prims.int) =
  fun st ->
    if st.FStar_JsonHelper.repl_last <> FStar_JsonHelper.Shutdown
    then (Prims.parse_int "1")
    else (Prims.parse_int "0")
let (run_query :
  FStar_JsonHelper.repl_state ->
    FStar_JsonHelper.lquery ->
      (FStar_JsonHelper.optresponse * FStar_JsonHelper.either_st_exit))
  =
  fun st ->
    fun q ->
      match q with
      | FStar_JsonHelper.Initialize (pid, rootUri) ->
          ((FStar_Pervasives_Native.Some
              (FStar_Util.Inl FStar_JsonHelper.js_servcap)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.Initialized ->
          (FStar_Pervasives_Native.None, (FStar_Util.Inl st))
      | FStar_JsonHelper.Shutdown ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.Exit ->
          let uu____298 =
            let uu____299 = run_exit st in FStar_Util.Inr uu____299 in
          (FStar_Pervasives_Native.None, uu____298)
      | FStar_JsonHelper.Cancel id1 ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.FolderChange evt ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.ChangeConfig ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.ChangeWatch ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.Symbol sym ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.ExecCommand cmd ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.DidOpen item ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.DidChange ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.WillSave txid ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.DidSave txid ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.DidClose txid ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.Completion ctx ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.Resolve ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.Hover ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.SignatureHelp ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.Declaration ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.Definition ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.Implementation ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.References ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.DocumentHighlight ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.DocumentSymbol ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.CodeAction ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.CodeLens ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.DocumentLink ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.DocumentColor ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.ColorPresentation ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.Formatting ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.RangeFormatting ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.TypeFormatting ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.Rename ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.PrepareRename ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.FoldingRange ->
          ((FStar_Pervasives_Native.Some (FStar_Util.Inl FStar_Util.JsonNull)),
            (FStar_Util.Inl st))
      | FStar_JsonHelper.BadProtocolMsg msg ->
          let uu____483 =
            let uu____484 =
              let uu____489 =
                FStar_JsonHelper.js_resperr FStar_JsonHelper.MethodNotFound
                  msg in
              FStar_Util.Inr uu____489 in
            FStar_Pervasives_Native.Some uu____484 in
          (uu____483, (FStar_Util.Inl st))
let rec (parse_header_len :
  FStar_Util.stream_reader -> Prims.int -> Prims.int) =
  fun stream ->
    fun len ->
      let uu____510 = FStar_Util.read_line stream in
      match uu____510 with
      | FStar_Pervasives_Native.Some s ->
          if FStar_Util.starts_with s "Content-Length: "
          then
            let uu____521 =
              let uu____523 =
                FStar_Util.substring_from s (Prims.parse_int "16") in
              FStar_Util.int_of_string uu____523 in
            parse_header_len stream uu____521
          else
            if FStar_Util.starts_with s "Content-Type: "
            then parse_header_len stream len
            else
              if s = ""
              then len
              else FStar_Exn.raise FStar_JsonHelper.MalformedHeader
      | FStar_Pervasives_Native.None ->
          FStar_Exn.raise FStar_JsonHelper.InputExhausted
let rec (read_lsp_query :
  FStar_Util.stream_reader -> FStar_JsonHelper.lsp_query) =
  fun stream ->
    try
      (fun uu___132_552 ->
         match () with
         | () ->
             let n1 = parse_header_len stream (Prims.parse_int "0") in
             let uu____556 = FStar_Util.nread stream n1 in
             (match uu____556 with
              | FStar_Pervasives_Native.Some s -> parse_lsp_query s
              | FStar_Pervasives_Native.None ->
                  let uu____564 =
                    let uu____566 = FStar_Util.string_of_int n1 in
                    FStar_Util.format1 "Could not read %s bytes" uu____566 in
                  FStar_JsonHelper.wrap_content_szerr uu____564)) ()
    with
    | FStar_JsonHelper.MalformedHeader ->
        (FStar_Util.print_error "[E] Malformed Content Header\n";
         read_lsp_query stream)
    | FStar_JsonHelper.InputExhausted -> read_lsp_query stream
let rec (go : FStar_JsonHelper.repl_state -> Prims.int) =
  fun st ->
    let query = read_lsp_query st.FStar_JsonHelper.repl_stdin in
    let uu____583 = run_query st query.FStar_JsonHelper.q in
    match uu____583 with
    | (r, state_opt) ->
        ((match r with
          | FStar_Pervasives_Native.Some response ->
              let response' =
                FStar_JsonHelper.json_of_response
                  query.FStar_JsonHelper.query_id response in
              ((let uu____603 = FStar_Util.string_of_json response' in
                FStar_Util.print1_error "<<< %s\n" uu____603);
               FStar_JsonHelper.write_jsonrpc response')
          | FStar_Pervasives_Native.None -> FStar_Util.print_error "<<< ()\n");
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
let (initial_repl_state : FStar_JsonHelper.repl_state) =
  let uu____618 = FStar_Util.open_stdin () in
  {
    FStar_JsonHelper.repl_line = (Prims.parse_int "1");
    FStar_JsonHelper.repl_column = (Prims.parse_int "0");
    FStar_JsonHelper.repl_stdin = uu____618;
    FStar_JsonHelper.repl_last = FStar_JsonHelper.Exit;
    FStar_JsonHelper.repl_names = FStar_Interactive_CompletionTable.empty
  }
let (start_server : unit -> unit) =
  fun uu____626 ->
    let uu____627 = go initial_repl_state in FStar_All.exit uu____627
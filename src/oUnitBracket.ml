
open OUnitTest

type t = (unit -> unit) list

let create set_up tear_down test_ctxt =
  let fixture = set_up test_ctxt in
  let tear_down test_ctxt =
    tear_down fixture test_ctxt
  in
    OUnitShared.Mutex.with_lock
      test_ctxt.shared test_ctxt.tear_down_mutex
      (fun () ->
         test_ctxt.tear_down <- tear_down :: test_ctxt.tear_down);
    fixture

let logf logger lvl fmt = OUnitLogger.Test.logf logger lvl fmt

let bracket_tmpfile ?(prefix="ounit-") ?(suffix=".txt") ?mode test_ctxt =
  create
    (fun test_ctxt ->
       let (fn, chn) =
         Filename.open_temp_file ?mode prefix suffix
       in
         logf test_ctxt.test_logger `Info "Created a temporary file: %S." fn;
         (fn, chn))
    (fun (fn, chn) test_ctxt ->
       (try close_out chn with _ -> ());
       try
         Sys.remove fn;
         logf test_ctxt.test_logger `Info "Removed a temporary file: %S." fn
       with _ ->
         ())
    test_ctxt


let bracket_tmpdir ?(prefix="ounit-") ?(suffix=".dir") test_ctxt =
  let max_attempt = 10 in
  let rec try_hard_mkdir attempt =
    if max_attempt = attempt then begin
      OUnitUtils.failwithf
        "Unable to create temporary directory after %d attempts."
        attempt
    end else begin
      try
         let tmpdn = Filename.temp_file prefix suffix in
         Sys.remove tmpdn;
         Unix.mkdir tmpdn 0o755;
         tmpdn
      with Unix.Unix_error (Unix.EEXIST, "mkdir", _) ->
        try_hard_mkdir (max_attempt + 1)
    end
  in
  create
    (fun test_ctxt ->
       let tmpdn = try_hard_mkdir 0 in
       logf test_ctxt.test_logger `Info
         "Create a temporary directory: %S." tmpdn;
       tmpdn)
    (fun tmpdn test_ctxt ->
       let log_delete fn =
         logf test_ctxt.test_logger `Info
           "Delete in a temporary directory: %S." fn
       in
       let rec rmdir fn =
         Array.iter
           (fun bn ->
              let fn' = Filename.concat fn bn in
                if Sys.is_directory fn' then
                  begin
                    rmdir fn';
                    Unix.rmdir fn';
                    log_delete fn'
                  end
                else
                  begin
                    Sys.remove fn';
                    log_delete fn'
                  end)
           (Sys.readdir fn)
       in
         rmdir tmpdn;
         Unix.rmdir tmpdn;
         log_delete tmpdn)
    test_ctxt

let chdir_mutex = OUnitShared.Mutex.create OUnitShared.ScopeProcess

let bracket_chdir dir test_ctxt =
  let () =
    OUnitLogger.infof test_ctxt.logger "Change directory to %S" dir;
  in
  let () =
    try
      OUnitShared.Mutex.lock test_ctxt.shared chdir_mutex;
    with OUnitShared.Lock_failure ->
      failwith "Trying to do a nested chdir."
  in
  let cur_pwd =
    Sys.getcwd ()
  in
  create
    (fun test_ctxt -> Unix.chdir dir)
    (fun () test_ctxt ->
       Unix.chdir cur_pwd;
       OUnitShared.Mutex.unlock test_ctxt.shared chdir_mutex)
    test_ctxt

let with_bracket test_ctxt bracket f =
  section_ctxt test_ctxt
    (fun test_ctxt ->
       let res = bracket test_ctxt in
         f res test_ctxt)

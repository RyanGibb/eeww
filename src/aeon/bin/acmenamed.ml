
module Tls_le = struct
  exception Le_error of string
  let errcheck = function Ok v -> v | Error (`Msg m) -> raise (Le_error m)

  let (/) = Eio.Path.(/)

  let gen_account_key ~account_file () =
    let privkey = `RSA (Mirage_crypto_pk.Rsa.generate ~bits:2048 ()) in
    let key_pem = X509.Private_key.encode_pem privkey |> Cstruct.to_string in
    Eio.Path.save ~create:(`Or_truncate 0o600) account_file key_pem

  let gen_csr ~org ~email ~domain ~csr_file ~key_file () =
    let dn = X509.Distinguished_name.[
      Relative_distinguished_name.(singleton (CN domain));
      Relative_distinguished_name.(singleton (Mail email));
      Relative_distinguished_name.(singleton (O org));
    ] in
    let privkey = `RSA (Mirage_crypto_pk.Rsa.generate ~bits:4096 ()) in
    let csr = X509.Signing_request.create dn privkey |> errcheck in
    let csr_pem = X509.Signing_request.encode_pem csr |> Cstruct.to_string in
    let key_pem = X509.Private_key.encode_pem privkey |> Cstruct.to_string in
    Eio.Path.save ~create:(`Or_truncate 0o600) csr_file csr_pem;
    Eio.Path.save ~create:(`Or_truncate 0o600) key_file key_pem

  let gen_cert ~csr_pem ~account_pem ~email ~cert_file ~endpoint solver env =
    let account_key = X509.Private_key.decode_pem (Cstruct.of_string account_pem) |> errcheck in
    let request = X509.Signing_request.decode_pem (Cstruct.of_string csr_pem) |> errcheck in
    let sleep n = Eio.Time.sleep env#clock (float_of_int n) in
    let le = Letsencrypt.Client.initialise env ~endpoint ~email account_key |> errcheck in
    let certs = Letsencrypt.Client.sign_certificate env solver le sleep request |> errcheck in
    let cert = Cstruct.to_string @@ X509.Certificate.encode_pem_multiple certs in
    Eio.Path.save ~create:(`Or_truncate 0o600) cert_file cert

  let get_tls_server_config ?alpn_protocols ~key_file ~cert_file () =
    let certificate = X509_eio.private_of_pems ~cert:cert_file ~priv_key:key_file in
    let certificates = `Single  certificate in
    Tls.Config.(server ?alpn_protocols ~version:(`TLS_1_0, `TLS_1_3) ~certificates ~ciphers:Ciphers.supported ())

  module Eiox = struct
    (* UPSTREAM: need an Eio file exists check without opening *)
    let file_exists f =
      Eio.Switch.run @@ fun sw ->
      try ignore(Eio.Path.open_in ~sw f); true
      with _ -> false
  end

  let tls_config ?alpn_protocols ~cert_root ~org ~email ~domain ~endpoint solver env =
    let account_file = cert_root / "account.pem" in
    let csr_file = cert_root / "csr.pem" in
    let key_file = cert_root / "privkey.pem" in
    let cert_file = cert_root / "fullcert.pem" in
    if not (Eiox.file_exists account_file) then begin
      Eio.traceln "Generating account key";
      gen_account_key ~account_file ()
    end;
    if not (Eiox.file_exists key_file) then begin
      Eio.traceln "Generating key file and CSR";
      gen_csr ~org ~email ~domain ~csr_file ~key_file ();
    end;
    if not (Eiox.file_exists cert_file) then begin
      Eio.traceln "Generating cert file";
      let csr_pem = Eio.Path.load csr_file in
      let account_pem = Eio.Path.load account_file in
      gen_cert ~csr_pem ~account_pem ~email ~cert_file ~endpoint solver env
    end;
    get_tls_server_config ?alpn_protocols ~key_file ~cert_file ()
end

let run zonefiles log_level addressStrings port no_tcp no_udp
    email org domain prod cert =
  if no_tcp && no_udp then (
    Format.fprintf Format.err_formatter "Either UDP or TCP should be enabled\n";
    Format.pp_print_flush Format.err_formatter ();
    exit 1);
  let tcp = not no_tcp and udp = not no_udp in
  Eio_main.run @@ fun env ->
  let log = (Dns_log.get_log log_level) Format.std_formatter in
  let addresses = Server_args.parse_addresses port addressStrings in
  let rng ?_g length =
    let buf = Cstruct.create length in
    Eio.Flow.read_exact env#secure_random buf;
    buf
  in
  let server_state =
    let trie, keys = Zonefile.parse_zonefiles ~fs:env#fs zonefiles in
    ref
    @@ Dns_server.Primary.create ~keys ~rng ~tsig_verify:Dns_tsig.verify
         ~tsig_sign:Dns_tsig.sign trie
  in

  Eio.Switch.run @@ fun sw ->
  Eio.Fiber.fork ~sw (fun () -> Dns_server_eio.primary ~net:env#net ~clock:env#clock
    ~mono_clock:env#mono_clock ~tcp ~udp server_state log addresses);

  let acmeName = ref @@ None in
  let solver =
    let add_record name record =
      (* TODO verify name is for _acme-challenge *)
      let trie = Dns_server.Primary.data !server_state in
      let trie = Dns_trie.remove_ty name Dns.Rr_map.Txt trie in
      let ttl = 3600l in
      let rr =
        ttl, Dns.Rr_map.Txt_set.singleton record
      in
      let trie = Dns_trie.insert name Dns.Rr_map.Txt rr trie in
      (* TODO send out notifications *)
      let new_server_state, _notifications =
        let now = Ptime.of_float_s @@ Eio.Time.now env#clock |> Option.get
        and ts = Mtime.to_uint64_ns @@ Eio.Time.Mono.now env#mono_clock in
        Dns_server.Primary.with_data !server_state now ts trie in
      server_state := new_server_state;
      acmeName := Some name;
      Eio.traceln "Create '%a %ld IN TXT \"%s\"'" Domain_name.pp name ttl record;
      (* we could wait for dns propigation here...
         but we hope that a new un-cached record is created
         and if not, the server should retry (RFC 8555 S8.2) *)
      Ok ()
    in
    Letsencrypt_dns.dns_solver add_record
  in

  try
    let tls =
      match email, org, domain with
      | None, None, None -> Eio.traceln "Disabling TLS"; `No_tls
      | Some email, Some org, Some domain -> `With_tls (email, org, domain)
      | _ -> failwith "Must specify all of --email, --org, --domain in order to enable TLS"
    in
    match tls with
    | `No_tls -> ()
    | `With_tls (email, org, domain) ->
      let endpoint = if prod then Letsencrypt.letsencrypt_production_url else Letsencrypt.letsencrypt_staging_url in
      Eio.Switch.run @@ fun sw ->
      let cert_root = let ( / ) = Eio.Path.( / ) in Eio.Path.open_dir ~sw (env#fs / cert) in
      Mirage_crypto_rng_eio.run (module Mirage_crypto_rng.Fortuna) env @@ fun () ->
      let _config = Tls_le.tls_config ~cert_root ~org ~email ~domain ~endpoint solver env in
      (* once cert provisioned, remove the record *)
      match !acmeName with
      | None -> ()
      | Some name ->
        let trie = Dns_server.Primary.data !server_state in
        let ttl, records = Dns_trie.lookup name Dns.Rr_map.Txt trie |> Result.get_ok in
        let data = Dns_trie.remove_ty name Dns.Rr_map.Txt trie in
        (* TODO send out notifications *)
        let new_server_state, _notifications =
          let now = Ptime.of_float_s @@ Eio.Time.now env#clock |> Option.get
          and ts = Mtime.to_uint64_ns @@ Eio.Time.Mono.now env#mono_clock in
          Dns_server.Primary.with_data !server_state now ts data in
        server_state := new_server_state;
        Dns.Rr_map.Txt_set.iter (fun record ->
          Eio.traceln "Remove '%a %ld IN TXT \"%s\"'" Domain_name.pp name ttl record;
        ) records;
      ();
  with Tls_le.Le_error msg -> Eio.traceln "ACME error: %s" msg

let () =
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level (Some Logs.Info);
  let open Cmdliner in
  let open Server_args in
  let cmd =
    let email =
      let doc = "Contact e-mail for registering new LetsEncrypt keys" in
      Arg.(value & opt (some string) None & info [ "email" ] ~doc)
    in
    let org =
      let doc = "Organisation name for the LetsEncrypt keys" in
      Arg.(value & opt (some string) None & info [ "org" ] ~doc)
    in
    let domain =
      let doc = "Domain name to issue certificate for" in
      Arg.(value & opt (some string) None & info [ "domain" ] ~doc)
    in
    let prod =
      let doc = "Production certification generation" in
      Arg.(value & flag & info [ "prod" ] ~doc)
    in
    let cert =
      let doc = "Directory where to store the certificates" in
      Arg.(value & opt string "certs" & info [ "certs-dir" ] ~doc)
    in
    let term =
      Term.(
        const run $ zonefiles $ logging $ addresses $ port $ no_tcp $ no_udp
        $ email $ org $ domain $ prod $ cert)
    in
    let info = Cmd.info "aeon" ~man in
    Cmd.v info term
  in
  exit (Cmd.eval cmd)

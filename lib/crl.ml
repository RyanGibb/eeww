open Rresult

open Common

type revoked_cert = {
  serial : Z.t ;
  date : Ptime.t ;
  extensions : (bool * Extension.t) list
}

type tBS_CRL = {
  version : [ `V1 | `V2 ] ;
  signature : Algorithm.t ;
  issuer : Distinguished_name.t ;
  this_update : Ptime.t ;
  next_update : Ptime.t option ;
  revoked_certs : revoked_cert list ;
  extensions : (bool * Extension.t) list
}

type crl = {
  tbs_crl : tBS_CRL ;
  signature_algo : Algorithm.t ;
  signature_val : Cstruct.t
}

module Asn = struct
  open Asn.S
  open Asn_grammars

  let revokedCertificate =
    let f (serial, date, e) =
      let extensions = match e with None -> [] | Some xs -> xs in
      { serial ; date ; extensions }
    and g { serial ; date ; extensions } =
      let e = match extensions with [] -> None | xs -> Some xs in
      (serial, date, e)
    in
    map f g @@
    sequence3
      (required ~label:"userCertificate" @@ Certificate.Asn.certificate_sn)
      (required ~label:"revocationDate" @@ Certificate.Asn.time)
      (optional ~label:"crlEntryExtensions" @@ Extension.Asn.extensions_der)

  let version =
    map
      (function 0 -> `V1 | 1 -> `V2 | _ -> parse_error "unknown version")
      (function `V2 -> 1 | `V1 -> 0)
      int

  let tBSCertList =
    let f (a, (b, (c, (d, (e, (f, g)))))) =
      { version = def `V1 a ; signature = b ; issuer = c ;
        this_update = d ; next_update = e ;
        revoked_certs = (match f with None -> [] | Some xs -> xs) ;
        extensions = (match g with None -> [] | Some xs -> xs) }
    and g { version = a ; signature = b ; issuer = c ;
            this_update = d ; next_update = e ; revoked_certs = f ;
            extensions = g } =
      let f = match f with [] -> None | xs -> Some xs
      and g = match g with [] -> None | xs -> Some xs
      in
      (def' `V1 a, (b, (c, (d, (e, (f, g))))))
    in
    map f g @@
    sequence @@
    (optional ~label:"version" @@ version)
    @ (required ~label:"signature" @@ Algorithm.identifier)
    @ (required ~label:"issuer" @@ Distinguished_name.Asn.name)
    @ (required ~label:"thisUpdate" @@ Certificate.Asn.time)
    @ (optional ~label:"nextUpdate" @@ Certificate.Asn.time)
    @ (optional ~label:"revokedCertificates" @@ sequence_of revokedCertificate)
      -@ (optional ~label:"crlExtensions" @@ explicit 0 Extension.Asn.extensions_der)

  let certificateList =
    let f (cl, sa, sv) =
      if cl.signature <> sa then
        parse_error "signatureAlgorithm != tbsCertList.signature"
      else
        { tbs_crl = cl ; signature_algo = sa ; signature_val = sv }
    and g { tbs_crl ; signature_algo ; signature_val } =
      (tbs_crl, signature_algo, signature_val)
    in
    map f g @@
    sequence3
      (required ~label:"tbsCertList" @@ tBSCertList)
      (required ~label:"signatureAlgorithm" @@ Algorithm.identifier)
      (required ~label:"signatureValue" @@ bit_string_cs)

  let (crl_of_cstruct, crl_to_cstruct) =
    projections_of Asn.der certificateList

  let (tbs_CRL_of_cstruct, tbs_CRL_to_cstruct) =
    projections_of Asn.der tBSCertList
end

type t = {
  raw : Cstruct.t ;
  asn : crl ;
}

let decode_der raw =
  Asn.crl_of_cstruct raw >>| fun asn ->
  { raw ; asn }

let encode_der { raw ; _ } = raw

let issuer { asn ; _ } = asn.tbs_crl.issuer

let this_update { asn ; _ } = asn.tbs_crl.this_update

let next_update { asn ; _ } = asn.tbs_crl.next_update

let extensions { asn ; _ } = asn.tbs_crl.extensions

let revoked_certificates { asn ; _ } = asn.tbs_crl.revoked_certs

let crl_number { asn ; _ } =
  List_ext.map_find asn.tbs_crl.extensions ~f:(fun (_, ext) ->
      match ext with
      | `CRL_number x -> Some x
      | _ -> None)

let validate { raw ; asn } pub =
  let tbs_raw = Validation.raw_cert_hack raw asn.signature_val in
  Validation.validate_raw_signature tbs_raw asn.signature_algo asn.signature_val pub

let verify ({ asn ; _ } as crl) ?time cert =
  Distinguished_name.equal asn.tbs_crl.issuer (Certificate.subject cert) &&
  (match time with
   | None -> true
   | Some x -> Ptime.is_later ~than:asn.tbs_crl.this_update x &&
               match asn.tbs_crl.next_update with
               | None -> true
               | Some y -> Ptime.is_earlier ~than:y x) &&
  validate crl (Certificate.public_key cert)

let reason (revoked : revoked_cert) =
  List_ext.map_find revoked.extensions ~f:(fun (_, ext) ->
      match ext with
      | `Reason x -> Some x
      | _ -> None)

let is_revoked (crls : t list) ~issuer:super ~cert =
  List.exists (fun crl ->
      if
        Distinguished_name.equal (Certificate.subject super) (issuer crl) &&
        validate crl (Certificate.public_key super)
      then
        try
          let entry = List.find
              (fun r -> Z.equal (Certificate.serial cert) r.serial)
              (revoked_certificates crl)
          in
          match reason entry with
          | None -> true
          | Some `Remove_from_CRL -> false
          | Some _ -> true
        with Not_found -> false
      else
        false)
    crls

let sign_tbs (tbs : tBS_CRL) key =
  let tbs_raw = Asn.tbs_CRL_to_cstruct tbs in
  let digest = match Algorithm.to_signature_algorithm tbs.signature with
    | Some (_, h) -> h
    | _ -> invalid_arg "couldn't parse signature algorithm"
  in
  let signature_val = Ca.raw_sign tbs_raw digest key in
  let asn = { tbs_crl = tbs ; signature_algo = tbs.signature ; signature_val } in
  let raw = Asn.crl_to_cstruct asn in
  { asn ; raw }

let revoke
    ?(digest = `SHA256)
    ~issuer
    ~this_update ?next_update
    ?(extensions = [])
    revoked_certs
    key =
  let signature =
    Algorithm.of_signature_algorithm (Private_key.keytype key) digest
  in
  let tbs_crl = {
    version = `V2 ;
    signature ;
    issuer ;
    this_update ; next_update ;
    revoked_certs ;
    extensions
  }
  in
  sign_tbs tbs_crl key

let revoke_certificates (revoked : revoked_cert list) ~this_update ?next_update ({ asn ; _ } as crl) key =
  let tbs = asn.tbs_crl in
  let extensions = match crl_number crl with
    | None -> (false, `CRL_number 0) :: tbs.extensions
    | Some x -> (false, `CRL_number (succ x)) ::
                List.filter (function (_, `CRL_number _) -> false | _ -> true)
                  tbs.extensions
  in
  let tbs = {
    tbs with revoked_certs = tbs.revoked_certs @ revoked ;
             this_update ; next_update ;
             extensions
  }
  in
  sign_tbs tbs key

let revoke_certificate revoked ~this_update ?next_update crl key =
  revoke_certificates [revoked] ~this_update ?next_update crl key

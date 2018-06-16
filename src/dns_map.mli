(* (c) 2017, 2018 Hannes Mehnert, all rights reserved *)

type _ k =
  | Any : (Dns_packet.rr list * Domain_name.Set.t) k
  | Cname : (int32 * Domain_name.t) k
  | Mx : (int32 * (int * Domain_name.t) list) k
  | Ns : (int32 * Domain_name.Set.t) k
  | Ptr : (int32 * Domain_name.t) k
  | Soa : (int32 * Dns_packet.soa) k
  | Txt : (int32 * string list list) k
  | A : (int32 * Ipaddr.V4.t list) k
  | Aaaa : (int32 * Ipaddr.V6.t list) k
  | Srv : (int32 * Dns_packet.srv list) k
  | Dnskey : Dns_packet.dnskey list k
  | Caa : (int32 * Dns_packet.caa list) k
  | Tlsa : (int32 * Dns_packet.tlsa list) k
  | Sshfp : (int32 * Dns_packet.sshfp list) k

include Gmap.S with type 'a key = 'a k

val k_to_rr_typ : 'a k -> Dns_enum.rr_typ
val to_rr_typ : v -> Dns_enum.rr_typ
val to_rr : Domain_name.t -> v -> Dns_packet.rr list
val names : v -> Domain_name.Set.t
val glue :
  ((int32 * Ipaddr.V4.t list) * (int32 * Ipaddr.V6.t list)) Domain_name.Map.t ->
  Dns_packet.rr list

val of_rdata : int32 -> Dns_packet.rdata -> v option

val lookup_rr : Dns_enum.rr_typ -> t -> v option
val remove_rr : Dns_enum.rr_typ -> t -> t

val add_rdata : v -> Dns_packet.rdata -> v option
val remove_rdata : v -> Dns_packet.rdata -> v option

val pp_v : v Fmt.t

val equal_v : v -> v -> bool

val of_rrs : Dns_packet.rr list -> t Domain_name.Map.t

val text : Domain_name.t -> v -> string

(* TODO ideally there'd be something like mirage-flow-lwt that didn't depend
        on lwt and a ton of other things, and still provided [map]
        and [connect] and so on. leaving this stuff here for now until a
        better solution presents itself. *)

val default_resolver : string * string
(** [default_resolver] is a pair of IPv4 and IPv6 address in dotted-decimal
    (/hexadecimal) form of the default resolver. Currently it is the IP address
    of the UncensoredDNS.org anycast service. *)

module type S = sig
  type context
  (** A context is a network connection initialized by {!T.connect} *)

  type +'a io
  (** [io] is the type of an effect. ['err] is a polymorphic variant. *)

  type io_addr
  (** An address for a given context type, usually this will consist of
      IP address + a TCP/IP or UDP/IP port number, but for some context types
      it can carry additional information for purposes of cryptographic
      verification. *)

  type ns_addr = Dns.proto * io_addr
  (** A pair of the transport protocol and the [io_addr]. We need to know the
      protocol used so we can prefix packets for DNS-over-TCP and set correct
      socket options etc. therefore we can't just use the opaque [io_addr]. *)

  type stack
  (** A stack with which to connect. *)

  type t
  (** The abstract state of a DNS client. *)

  val create : ?nameserver:ns_addr -> timeout:int64 -> stack -> t
  (** [create ~nameserver ~timeout stack] creates the state record of the DNS
      client. We use [timeout] (ns) as a cumulative time budget for connect
      and request timeouts. *)

  val nameserver : t -> ns_addr
  (** The address of a nameserver that is supposed to work with
      the underlying context, can be used if the user does not want to
      bother with configuring their own.*)

  val rng : int -> Cstruct.t
  (** [rng t] is a random number generator. *)

  val clock : unit -> int64
  (** [clock t] is the monotonic clock. *)

  val connect : ?nameserver:ns_addr -> t -> (context, [> `Msg of string ])
      result io
  (** [connect addr] is a new connection ([context]) to [addr], or an error. *)

  val send : context -> Cstruct.t -> (unit, [> `Msg of string ]) result io
  (** [send context buffer] sends [buffer] to the [context] upstream.*)

  val recv : context -> (Cstruct.t, [> `Msg of string ]) result io
  (** [recv context] tries to read a [buffer] from the [context] downstream.*)

  val close : context -> unit io
  (** [close context] closes the [context], freeing up resources. *)

  val bind : 'a io -> ('a -> 'b io) -> 'b io
  (** a.k.a. [>>=] *)

  val lift : 'a -> 'a io
end

module Make : functor (T : S) ->
sig

  type t

  val create : ?size:int -> ?nameserver:T.ns_addr -> ?timeout:int64 ->
    T.stack -> t
  (** [create ~size ~nameserver ~timeout stack] creates the state of the DNS
      client. We use [timeout] (ns, default 3s) as a time budget for connect and
      request timeouts. To specify a timeout, use
      [create ~timeout:(Duration.of_sec 5)]. *)

  val nameserver : t -> T.ns_addr
  (** [nameserver state] returns the default nameserver to be used. *)

  val getaddrinfo : t -> ?nameserver:T.ns_addr -> 'response Dns.Rr_map.key ->
    'a Domain_name.t ->
    ('response, [> `Msg of string ]) result T.io
  (** [getaddrinfo state nameserver query_type name] is the
      [query_type]-dependent response from [nameserver] regarding [name], or
      an [Error _] message. See {!Dns_client.query_state} for more information
      about the result types. *)

  val gethostbyname : t -> ?nameserver:T.ns_addr -> [ `host ] Domain_name.t ->
    (Ipaddr.V4.t, [> `Msg of string ]) result T.io
  (** [gethostbyname state ~nameserver hostname] is the IPv4 address of
      [hostname] resolved via the [state] and [nameserver] specified.
      If the query fails, or if the [domain] does not have any IPv4 addresses,
      an [Error _] message is returned. Any extraneous IPv4 addresses are
      ignored. For an example of using this API, see [unix/ohost.ml] in the
      distribution of this package. *)

  val gethostbyname6 : t -> ?nameserver:T.ns_addr -> [ `host ] Domain_name.t ->
    (Ipaddr.V6.t, [> `Msg of string ]) result T.io
  (** [gethostbyname6 state ~nameserver hostname] is the IPv6 address of
      [hostname] resolved via the [state] and [nameserver] specified.

      It is the IPv6 equivalent of {!gethostbyname}. *)

  val get_resource_record : t -> ?nameserver:T.ns_addr ->
    'response Dns.Rr_map.key -> 'a Domain_name.t ->
    ('response,
     [> `Msg of string
     | `No_data of [ `raw ] Domain_name.t * Dns.Soa.t
     | `No_domain of [ `raw ] Domain_name.t * Dns.Soa.t ]) result T.io
    (** [get_resource_record state ~nameserver query_type name] resolves
        [query_type, name] via the [state] and [nameserver] specified. The
        behaviour is equivalent to {!getaddrinfo}, apart from the error return
        value - [get_resource_record] distinguishes some errors, at the moment
        [No_data] if the [name] exists, but not the [query_type], and
        [No_domain] if the [name] does not exist. This allows clients to treat
        these error conditions explicitly. *)

end

module Pure : sig
  (** The pure interface to the client part of uDns.

      Various helper modules to do with side effects are available from
      {!Dns_client_lwt}, {!Dns_client_unix} and so forth. *)

  type 'key query_state constraint 'key = 'a Dns.Rr_map.key
  (** [query_state] is parameterized over the query type, so the type of the
      representation of the answer depends on what the name server was asked to
      provide. See {!Dns_map.k} for a list of response types. The first element
      (the [int32]) in most of the tuples is the Time-To-Live (TTL) field
      returned from the server, which you can use to calculate when you should
      request fresh information in case you are writing a long-running
      application. *)

  val make_query :
    (int -> Cstruct.t) -> Dns.proto -> 'a Domain_name.t ->
    'query_type Dns.Rr_map.key ->
    Cstruct.t * 'query_type Dns.Rr_map.key query_state
  (** [make_query rng protocol name query_type] is [query, query_state]
      where [query] is the serialized DNS query to send to the name server,
      and [query_state] is the information required to validate the response. *)

  val parse_response : 'query_type Dns.Rr_map.key query_state -> Cstruct.t ->
    ( [ `Data of 'query_type | `Partial
      | `No_data of [`raw] Domain_name.t * Dns.Soa.t
      | `No_domain of [`raw] Domain_name.t * Dns.Soa.t ],
      [`Msg of string]) result
  (** [parse_response query_state response] is the information contained in
      [response] parsed using [query_state] when the query was successful, or
      an [`Msg message] if the [response] did not match the [query_state]
      (or if the query failed).

      In a TCP usage context the [`Partial] means there are more bytes to be
      read in order to parse correctly. This can happen due to short reads or if
      the server (or something along the route) chunks its responses into
      multiple individual packets. In that case you should concatenate
      [response] and the next received data and call this function again.

      In a UDP usage context the [`Partial] means information was lost, due to
      an incomplete packet. *)

end

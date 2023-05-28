open Capnp_rpc_lwt

module Process : sig
  module Out : sig
    type t = Raw.Client.ProcessOut.t Capability.t

    val stdout :
      chunk:string -> t -> (unit, [> `Capnp of Capnp_rpc.Error.t ]) result

    val stderr :
      chunk:string -> t -> (unit, [> `Capnp of Capnp_rpc.Error.t ]) result

    val complete :
      exit_code:int32 ->
      t ->
      (unit, [> `Capnp of Capnp_rpc.Error.t ]) result
  end

  module In : sig
    type t = Raw.Client.ProcessIn.t Capability.t

    val stdin :
      chunk:string -> t -> (unit, [> `Capnp of Capnp_rpc.Error.t ]) result

    val cancel : t -> (unit, [> `Capnp of Capnp_rpc.Error.t ]) result
  end
end

module Agent : sig
  type t = Raw.Client.Agent.t Capability.t

  type command = string * string array

  val exec :
    cmd:command -> t -> (int32, [> `Capnp of Capnp_rpc.Error.t ]) result

  val spawn : pty:bool -> command -> Process.Out.t -> t -> Process.In.t
end

module ClusterMember : sig
  type t = Raw.Client.ClusterMember.t Capability.t

  type hostinfo = {
    os_version : string;
    os_distrib : Osrelease.Distro.t;
    arch : Osrelease.Arch.t;
  }

  val register :
    hostname:string -> callback:Agent.t -> hostinfo:hostinfo -> t -> unit
end

module ClusterUser : sig
  type t = Raw.Client.ClusterUser.t Capability.t

  val find : hostname:string -> t -> Agent.t
end

let run ~fallback:_ fn = Eio_posix.run (fun env -> fn (env :> Eio.Stdenv.t))

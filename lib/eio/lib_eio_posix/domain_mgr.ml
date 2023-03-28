(*
 * Copyright (C) 2023 Thomas Leonard
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

open Eio.Std

[@@@alert "-unstable"]

(* Run an event loop in the current domain, using [fn x] as the root fiber. *)
let run_event_loop ~loc fn x =
  Sched.with_sched @@ fun sched ->
  let open Effect.Deep in
  let extra_effects : _ effect_handler = {
    effc = fun (type a) (e : a Effect.t) : ((a, Sched.exit) continuation -> Sched.exit) option ->
      match e with
      | Eio_unix.Private.Get_monotonic_clock -> Some (fun k -> continue k (Time.mono_clock : Eio.Time.Mono.t))
      | Eio_unix.Private.Socket_of_fd (sw, close_unix, unix_fd) -> Some (fun k ->
          let fd = Fd.of_unix ~sw ~blocking:false ~close_unix unix_fd in
          Unix.set_nonblock unix_fd;
          continue k (Flow.of_fd fd :> Eio_unix.socket)
        )
      | Eio_unix.Private.Socketpair (sw, domain, ty, protocol) -> Some (fun k ->
          match
            let unix_a, unix_b = Unix.socketpair ~cloexec:true domain ty protocol in
            let a = Fd.of_unix ~sw ~blocking:false ~close_unix:true unix_a in
            let b = Fd.of_unix ~sw ~blocking:false ~close_unix:true unix_b in
            Unix.set_nonblock unix_a;
            Unix.set_nonblock unix_b;
            (Flow.of_fd a :> Eio_unix.socket), (Flow.of_fd b :> Eio_unix.socket)
          with
          | r -> continue k r
          | exception Unix.Unix_error (code, name, arg) ->
              discontinue k (Err.wrap code name arg)
        )
      | Eio_unix.Private.Pipe sw -> Some (fun k ->
          match
            let unix_r, unix_w = Unix.pipe ~cloexec:true () in
            let r = Fd.of_unix ~sw ~blocking:false ~close_unix:true unix_r in
            let w = Fd.of_unix ~sw ~blocking:false ~close_unix:true unix_w in
            Unix.set_nonblock unix_r;
            Unix.set_nonblock unix_w;
            let source = (Flow.of_fd r :> <Eio.Flow.source; Eio.Flow.close; Eio_unix.unix_fd>) in
            let sink = (Flow.of_fd w :> <Eio.Flow.sink; Eio.Flow.close; Eio_unix.unix_fd>) in
            (source, sink)
          with
          | r -> continue k r
          | exception Unix.Unix_error (code, name, arg) ->
            discontinue k (Err.wrap code name arg)
        )
      | _ -> None
  }
  in
  Sched.run ~loc ~extra_effects sched fn x

let v ~run_queues = object
  inherit Eio.Domain_manager.t

  method run_raw fn =
    let domain = ref None in
    Eio.Private.Suspend.enter (fun _ctx enqueue ->
        domain := Some (Domain.spawn (fun () -> Fun.protect fn ~finally:(fun () -> enqueue (Ok ()))))
      );
    Domain.join (Option.get !domain)

  method run ?(loc=Eio.Private.Ctf.get_caller ()) fn =
    let domain = ref None in
    Eio.Private.Suspend.enter (fun ctx enqueue ->
        let cancelled, set_cancelled = Promise.create () in
        Eio.Private.Fiber_context.set_cancel_fn ctx (Promise.resolve set_cancelled);
        domain := Some (Domain.spawn (fun () ->
            Fun.protect (run_event_loop ~loc (fun () -> fn ~cancelled))
              ~finally:(fun () -> enqueue (Ok ()))))
      );
    Domain.join (Option.get !domain)

  (* When submitting tasks to run on different domains we need a few things:
      - We need the tasks effect handler to install in an idle domain
      - We need the handle's task queue to push new items onto
      - We need to know how many of the "idle domains" are currently active
        for our 'subsystem'.
         - If we have reach capacity then we can push items to the work queue
           and one of the active domains will pick it up.
         - If we haven't reached capacity then we can spin up a new idle domain
           for our subsystem.

      ... all of this modulo making it domain safe ^^'
  *)
  method submit ?(loc=Eio.Private.Ctf.get_caller ()) (type a) (uid : a Eio.Domain_manager.handle) (fn : unit -> a) : a =
    match Hashtbl.find_opt run_queues (Hmap.Key.hide_type uid) with
    | Some (active, cap) when !active >= cap ->
      Eio.traceln "At capacity, pushing items to work queue.";
      let p, r = Eio.Promise.create () in
      let _handler, queue = Eio.Domain_manager.lookup_handler_exn uid in
      Queue.push (r, fn) queue;
      Eio.Promise.await_exn p
    | None | Some _ as t ->
        let active = match t with 
          | Some (active, _) -> active
          | None ->
            let active = ref 0 in
            (* 3 is an arbitrary number -- we need to be smarter than this when 
               scheduling to ensure no subsystem gets starved. We could potentially
               know statically ahead of time how many 'subsystems' have registered to
               submit things to domains, provided they all register at module initialisation
               time and naively we could do the initial capacities fairly spread amongst
               these subsystems. *)
            Hashtbl.add run_queues (Hmap.Key.hide_type uid) (active, 3);
            active
        in
        let p, r = Eio.Promise.create () in
        let handler, queue = Eio.Domain_manager.lookup_handler_exn uid in
        Queue.push (r, fn) queue;
        (* Each scheduler is a new Eio loop + the subsystems handler. *)
        let scheduler =
          run_event_loop ~loc @@ fun _ ->
          Effect.Deep.match_with (fun () ->
            let rec loop () = match Queue.peek_opt queue with
              | Some _ -> 
                let r, task = Queue.pop queue in
                let v = 
                  try Ok (task ()) with exn -> Error exn 
                in
                Eio.Promise.resolve r v;
                loop ()
              | None -> 
                (* Instead of just leaving immediately we could instead linger
                   a little bit in case some extra work turns up, or block on
                   some condition variable which is broadcast to that will wake
                   us up when the task queue has been modified. *)
                decr active
            in
              loop ()
          ) () handler
        in
        while not (Eio.Idle_domains.try_spawn ~scheduler) do
          Domain.cpu_relax ();
        done;
        incr active;
        Eio.Promise.await_exn p


end

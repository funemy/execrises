(* Divergent computation in STLC+ref but with closure *)
let diverge' =
  fun (f : (unit -> unit) ref) ->
    (f := fun x : unit -> !f (*closure here!*) x); !f ()

(* The goal is to create a divergent computation in STLC+ref without closure *)
let diverge =
  fun (f : (unit -> unit) ref) ->
    f := (fun (g : (unit -> unit) ref) -> fun (x : unit) -> !g x) f (* partial application, which is a kind of closure *); !f ()

(* let us ROCKKKKKk *)
let _ = diverge (ref (fun x -> ()))
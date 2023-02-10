(* Divergent computation in STLC+ref but with closure *)
let diverge'' =
  fun (f : (unit -> unit) ref) ->
    (f := fun x : unit -> !f (*closure here!*) x); !f ()

(* The goal is to create a divergent computation in STLC+ref without closure *)
(* This implementation uses partial application, which is still a kind of closure *)
let diverge' =
  fun (f : (unit -> unit) ref) ->
    f := (fun (g : (unit -> unit) ref) -> fun (x : unit) -> !g x) f (* partial application, which is a kind of closure *);
    !f ()

(* so the sequencing problem can be solve by not doing partial app (seeing a list of parameters as a tuple) *)
(* but the partial application in the lhs of the assignment is still there *)
(* let diverge'_alt =
  fun (f : ((unit -> unit) ref * unit)) ->
    (fun (_, g) -> !g ()) (f := (fun (g , x) : ((unit -> unit) ref * unit) -> !g x) (fst f, snd f), f) *)

type ty1 = ((unit -> unit) ref * ((unit -> unit) ref -> unit -> unit -> unit))
let diverge'_alt =
  fun (f : ty1) ->
    fst f := (snd f) (fst f) ();
    !(fst f) ()

let a1 : (unit -> unit) ref = ref (fun x -> x)
(* let a2 : unit = () *)

let a3 : ((unit -> unit) ref -> unit -> unit -> unit) = fun x y -> fun z (* there is still closure *) -> !x y

(* let us ROCKKKKKk *)
let _ = diverge'_alt (a1, a3)

(* At this moment, I'm fairly convinced we cannot get divergence without closure (including partial app) *)
(* Since we are trying to construct an recursive function, we need to get something of shape Ty (-> Ty)+ *)
(* However, constructing such an arrow type either means partial application or explicitly writing an lambda abstraction and using variables in the outer scope  *)
(* Intuitively, we start with a dummpy function stored in the memory cell and redefine it to make it self-recursive *)
(* self-recursion means function applications in the body, thus reduce the size of the type of the function (from T->T to just T) *)
(* Hence, somewhere in the program we must have exactly one lambda abstraction to grow the size of the type (from T to T->T). *)
(* Moreover, there must be exactly one such lambda abstraction, because otherwise the type of the function changes. *)

let a3 : ((unit -> unit) ref -> unit -> unit) = fun x y -> !x y


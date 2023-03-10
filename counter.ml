module Counter : sig
  type t
  val new' : unit -> t
  val inc : t -> unit
  val get : t -> int
end
= struct
  type t = int ref
  let new' () = ref 0
  let inc r = r := !r + 1
  let get r = !r
end

open Counter;;

(* should get 2 *)
let c = new' () in
  inc c; inc c; get c
;;

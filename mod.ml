module M : sig
  type t
  val a : t
  val f : t -> int
end
= struct
  type t = int
  let a = 0
  let f = succ
end

open M;;

a;;
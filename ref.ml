type int_array = (int -> int) ref

let newarray : unit -> int_array = fun () -> ref (fun n -> 0)

let lookup : int_array -> int -> int = fun a n -> !a n

let update (a : int_array) (i : int) (v : int) : unit =
  let oldf = !a in
  a := fun n -> if i == n then v else oldf n
type st = Mk of int * st

let rec ones = Mk (1, ones)
let rec map f (Mk (n, s)) = Mk (f n, map f s)
let head (Mk (n, s)) = n
let tail (Mk (n, s)) = s

(* below will cause stackoverflow *)
(* let twos = map succ ones *)

type st = Mk of int * st

let rec ones = Mk (1, ones)

let head (Mk (n, s)) = n

let tail (Mk (n, s)) = s
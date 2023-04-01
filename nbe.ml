(* The code is mostly copied from wiki of NbE *)
type ty =
  | TyBasic of string
  | TyArrow of ty * ty
  | TyProd of ty * ty

type tm =
  | Var of string
  | Lam of string * tm
  | App of tm * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm

type sem =
  | LAM of (sem -> sem)
  | PAIR of sem * sem
  | SYN of tm

(* fresh_var : unit -> string *)
let variable_ctr = ref (-1)

let fresh_var () =
  variable_ctr := 1 + !variable_ctr;
  "v" ^ string_of_int !variable_ctr
;;

exception Unreachable

(* reflect is doing one thing and only -- eta-expansion!! *)
(* reflect : ty -> tm -> sem *)
let rec reflect ty t =
  match ty with
  | TyArrow (a, b) -> LAM (fun s' -> reflect b (App (t, reify a s')))
  | TyProd (a, b) -> PAIR (reflect a (Fst t), reflect b (Snd t))
  | TyBasic _ -> SYN t

(* reify : ty -> sem -> tm *)
and reify ty s =
  match ty, s with
  | TyArrow (a, b), LAM s' ->
    let x = fresh_var () in
    Lam (x, reify b (s' (reflect a (Var x))))
  | TyProd (a, b), PAIR (l, r) -> Pair (reify a l, reify b r)
  | TyBasic _, SYN t -> t
  | _ -> raise Unreachable
;;

type ctx =
  | Empty
  | Add of ctx * (string * sem)

exception LookupFailure

(* lookup : ctx -> string -> sem *)
let rec lookup ctx x =
  match ctx with
  | Add (remdr, (y, value)) -> if x = y then value else lookup remdr x
  | Empty -> raise LookupFailure
;;

(* \f -> \x. f x *)
(* meaning : ctx -> tm -> sem *)
let rec meaning ctx t =
  match t with
  | Var x -> lookup ctx x
  | Lam (x, s) -> LAM (fun s' -> meaning (Add (ctx, (x, s'))) s)
  | App (s, t) ->
    (match meaning ctx s with
     | LAM s' -> s' (meaning ctx t)
     | _ -> raise Unreachable)
  | Pair (s, t) -> PAIR (meaning ctx s, meaning ctx t)
  | Fst s ->
    (match meaning ctx s with
     | PAIR (l, r) -> l
     | _ -> raise Unreachable)
  | Snd t ->
    (match meaning ctx t with
     | PAIR (l, r) -> r
     | _ -> raise Unreachable)
;;

let nbe ty t = meaning Empty t |> reify ty

(* t1 = \f -> f *)
(* t1 = t2 : (A->B) -> (A->B)*)
let t1 = Lam ("f", Var "f")
let t2 = Lam ("f", Lam ("x", App (Var "f", Var "x")))
let ty = TyArrow (TyArrow (TyBasic "A", TyBasic "B"), TyArrow (TyBasic "A", TyBasic "B"))
let result1 = nbe ty t1
let result2 = nbe ty t2

(* The `meaning` function is the first pass to convert terms in our language into the
   seamntics domain. There's one caveat in this translation: the conversion of lambda
   bodies is delayed.

   The reason for this delayed evaluation, IMO, is mostly due to performance, so that we
   don't need to normalize function body twice.

   For the rest of the cases (i.e., non-lambda terms): if the term is in introduction
   form, we recursively interpret the sub-terms, and convert the whole term into the
   semantics domain; if the term is in elimination form, then we do beta-reduction.

   One may wonder, what if you are elimination a neutral term? E.g., (fst x).

   Well, `meaning` is supposed to only run on closed terms, so if the term is open, and we
   actually need to reduce (fst x), then the recursive call of `meaning x` will trigger
   the variable lookup, and consequently, raise an exception.

   Ok, so now we've understood how `meaning` work, let's look at `reify`. Intuitively,
   `meaning` reduced a term to its normal form (NOTE: this is imprecise, because the
   lambda body), and `reify` recover this normalized term in its semantics form back to
   the syntax form.

   Unsurprisingly, this `reify` is also a function recurse on its subterm. An interesting
   observation is that we only need to consider much fewer cases in reify, guided by the
   type of the term. This is because we've already done all the beta-reduction, so all
   terms should either be in a neutral form or value form.

   to be continued... *)

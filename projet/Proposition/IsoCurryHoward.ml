type bot = |
type ('a, 'b) et = 'a * 'b
type ('a, 'b) ou = ('a, 'b) Either.t
type ('a, 'b) imp = 'a -> 'b
type 'a non = 'a -> bot

(* Exercice 1 : règles introduction *)
let imp_intro : ('a -> 'b) -> 'a -> 'b = Fun.id
let et_intro : 'a * 'b -> 'a * 'b = Fun.id
let ou_intro_g : 'a -> ('a, 'b) Either.t = fun a -> Left a
let ou_intro_d : 'b -> ('a, 'b) Either.t = fun b -> Right b

(* Exercice 2 : règles d'élimination *)
let bot_elim (bot : bot) : 'a = match bot with _ -> .

let ou_elim : ('a, 'b) Either.t * ('a -> 'c) * ('b -> 'c) -> 'c =
 fun disj ->
  match disj with Left a, fac, _ -> fac a | Right b, fbc, _ -> fbc b

let imp_elim : ('a -> 'b) * 'a -> 'b = fun (f, a) -> f a
let et_elim_g : 'a * 'b -> 'a = fun (a, _) -> a
let et_elim_d : 'a * 'b -> 'b = fun (_, b) -> b

(* Exercice 3 : déduction naturelle *)

(* Exemple : principe de non-contradiction *)
let non_contra : 'a * ('a -> bot) -> bot = fun (a, non_a) -> non_a a
let non_contra2 : ('a, 'a non) et non = fun (a, non_a) -> non_a a

let non_contra' : 'a * ('a -> bot) -> bot =
 fun a_et_non_a -> imp_elim (et_elim_d a_et_non_a, et_elim_g a_et_non_a)

let f1 : 'a -> 'a = fun a -> a

let f2 : ('a non, 'b) ou * 'a -> 'b =
 fun (disj, a) ->
  match disj with Left non_a -> bot_elim (imp_elim (non_a, a)) | Right b -> b

let f3 : ('a, 'b) ou -> ('b, 'a) ou =
 fun disj -> match disj with Left a -> ou_intro_g a | Right b -> ou_intro_d b

let f4 : 'a * 'b -> 'b * 'a = fun _ -> failwith "à faire"
let f5 : 'a * 'b -> ('a, 'b) ou = fun _ -> failwith "à faire"
let f6 : 'a -> 'a non non = fun _ _ -> failwith "à faire"
let f7 : ('a non, 'b) ou -> 'a -> 'b = fun _ _ -> failwith "à faire"
let f8 : ('a * 'b -> 'c) -> 'a -> 'b -> 'c = fun _ _ _ -> failwith "à faire"
let f9 : ('a -> 'b -> 'c) -> 'a * 'b -> 'c = fun _ _ -> failwith "à faire"
let f10 : ('a non, 'b non) ou -> ('a * 'b) non = fun _ _ -> failwith "à faire"
let f11 : 'a non * 'b non -> ('a, 'b) ou non = fun _ _ -> failwith "à faire"
let f12 : 'a -> 'b -> 'a = fun _ _ -> failwith "à faire"

let f13 : ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c =
 fun _ _ _ -> failwith "à faire"

let f14 : ('a -> 'b) -> 'b non -> 'a non = fun _ _ _ -> failwith "à faire"
let f15 : ('a -> 'b non) -> 'b -> 'a non = fun _ _ _ -> failwith "à faire"
let f16 : 'a -> 'a non -> 'b = fun _ _ -> failwith "à faire"

let f17 : 'a * ('b, 'c) ou -> ('a * 'b, 'a * 'c) ou =
 fun _ -> failwith "à faire"

let f18 : ('a * 'b, 'a * 'c) ou -> 'a * ('b, 'c) ou =
 fun _ -> failwith "à faire"

let f19 : ('a, 'b * 'c) ou -> ('a, 'b) ou * ('a, 'c) ou =
 fun _ -> failwith "à faire"

let f20 : ('a, 'b) ou * ('a, 'c) ou -> ('a, 'b * 'c) ou =
 fun (a_ou_b, a_ou_c) ->
  match a_ou_b with
  | Left a -> ou_intro_g a
  | Right b -> (
      match a_ou_c with
      | Left a' -> ou_intro_g a'
      | Right c -> ou_intro_d (et_intro (b, c)))

let f21 : ('a -> 'b) -> ('a * 'b non) non = fun _ _ -> failwith "à faire"
let f22 : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c = fun _ _ _ -> failwith "à faire"
let f23 : 'a non non non -> 'a non = fun _ _ -> failwith "à faire"
let f24 : ('a, 'a non) ou non non = fun _ -> failwith "à faire"
let f25 : ('a, 'b) ou non -> 'a non * 'b non = fun _ -> failwith "à faire"

(* Exercice 4 : déduction naturelle et tiers exclu *)
type 'a tiers_exclu = ('a, 'a non) ou

let g1 : 'a tiers_exclu -> ('a non -> 'b non) -> 'b -> 'a =
 fun _ _ _ -> failwith "à faire"

let g2 : 'a tiers_exclu -> ('a non -> 'b) -> 'b non -> 'a =
 fun _ _ _ -> failwith "à faire"

let g3 : 'a tiers_exclu -> ('a -> 'b, 'b -> 'a) ou = fun _ -> failwith "à faire"

let g4 :
    'a tiers_exclu -> 'b tiers_exclu -> ('a, 'b) et non -> ('a non, 'b non) ou =
 fun _ _ _ -> failwith "à faire"

let g5 : 'a tiers_exclu -> 'a non non -> 'a = fun _ _ -> failwith "à faire"

let g6 : 'a tiers_exclu -> ('a -> 'b) -> ('a non, 'b) ou =
 fun _ _ -> failwith "à faire"

let g7 : 'a tiers_exclu -> ('a -> 'b) tiers_exclu -> (('a -> 'b) -> 'a) -> 'a =
 fun _ _ _ -> failwith "à faire"

let g8 : 'b tiers_exclu -> ('a * 'b non) non -> 'a -> 'b =
 fun _ _ _ -> failwith "à faire"

let g9 : 'a tiers_exclu -> ('a non -> 'b non) -> ('a non -> 'b) -> 'a =
 fun _ _ _ -> failwith "à faire"

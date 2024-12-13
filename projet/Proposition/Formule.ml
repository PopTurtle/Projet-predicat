(** Le module Formule contient les types et définitions de base
    permettant la manipulation des formules de la logique propositionnelle. *)

(** Type des formules de la logique propositionnelle, avec des string comme atomes. *)
type formule =
  | Bot
  | Top
  | Atome of string
  | Imp of (formule * formule)
  | Ou of (formule * formule)
  | Et of (formule * formule)
  | Non of formule

(* ----------------- Exercice 1 : Hauteur ----------------- *)

(** Calcule la hauteur de l'arbre syntaxique d'une formule. *)
let rec hauteur (f : formule) : int =
  match f with
  | Atome _ | Bot | Top -> 1
  | Non f -> 1 + hauteur f
  | Imp (f, g) | Ou (f, g) | Et (f, g) -> 1 + max (hauteur f) (hauteur g)

(* ----------------- Exercice 2 : Représentation en chaîne de caractères ----------------- *)

(** Conversion d'une formule en chaîne de caractères. *)
let rec string_of_formule : formule -> string =
  let conc_op f g op =
    String.concat ""
      [ "("; string_of_formule f; " "; op; " "; string_of_formule g; ")" ]
  in
  function
  | Bot -> "⊥"
  | Top -> "⊤"
  | Atome s -> s
  | Non f -> String.concat "" [ "¬"; string_of_formule f ]
  | Et (f, g) -> conc_op f g "∧"
  | Ou (f, g) -> conc_op f g "∨"
  | Imp (f, g) -> conc_op f g "→"

(* ----------------- Exercice 3 : Conversion depuis une liste ----------------- *)

(** Transforme une liste de formules [[f1; f2; ... ; fl]] en la formule [f1 ∧ f2 ∧ ... ∧ fl] en considérant les éléments suivants :
    Si un des [fi] vaut [Bot], renvoie [Bot].
    Si un des [fi] vaut [Top], il n'apparait pas dans le résultat.
    Si tous les [fi] valent [Top], renvoie [Top]. *)
let conj_of_list (fl : formule list) : formule =
  let acc_f acc v =
    match (acc, v) with
    | Bot, _ | _, Bot -> Bot
    | f, Top | Top, f -> f
    | f, g -> Et (f, g)
  in
  List.fold_left acc_f Top fl

(** Transforme une liste de formules [[f1; f2; ... ; fl]] en la formule [f1 ∨ f2 ∨ ... ∨ fl] en considérant les éléments suivants :
    Si un des [fi] vaut [Top], renvoie [Top].
    Si un des [fi] vaut [Bot], il n'apparait pas dans le résultat.
    Si tous les [fi] valent [Bot], renvoie [Bot]. *)
let disj_of_list (fl : formule list) : formule =
  let acc_f acc v =
    match (acc, v) with
    | Top, _ | _, Top -> Top
    | f, Bot | Bot, f -> f
    | f, g -> Ou (f, g)
  in
  List.fold_left acc_f Bot fl

(** --- Exercice 4 : Fonctions d'évaluation ------- *)

type interpretation = string -> bool
(** Type des interprétations. *)

(** Évalue une formule en fonction d'une interprétation. *)
let eval (inter : interpretation) (f' : formule) : bool =
  let rec aux f =
    match f with
    | Top -> true
    | Bot -> false
    | Atome s -> inter s
    | Non f -> not (aux f)
    | Et (f, g) -> aux f && aux g
    | Ou (f, g) -> aux f || aux g
    | Imp (f, g) -> (not (aux f)) || aux g
  in
  aux f'

(** --- Exercice 5 : Tests de satisfaisabilité ------- *)

(** Transforme une liste de string en une interprétation. *)
let interpretation_of_list (ss : string list) : interpretation = function
  | (s : string) -> List.mem s ss

(** Calcule la liste de toutes les sous-listes d'une liste donnée. *)
let rec all_sublists (l : 'a list) : 'a list list =
  match l with
  | [] -> [ [] ]
  | t :: q ->
      let sl = all_sublists q in
      sl @ List.map (function v -> t :: v) sl

(** Calcule toutes les interprétations pour une liste d'atomes donnée. *)
let all_interpretations (sl : string list) : interpretation list =
  List.map interpretation_of_list (all_sublists sl)

(** Calcule la liste (triée et sans doublon) des atomes d'une formule.*)
let atomes (f' : formule) : string list =
  let rec aux acc f =
    match f with
    | Bot | Top -> acc
    | Atome s -> s :: acc
    | Non f -> aux acc f
    | Et (f, g) | Ou (f, g) | Imp (f, g) -> aux (aux acc g) f
  in
  List.sort_uniq String.compare (aux [] f')

let all_res (f : formule) : bool list =
  let inter = all_interpretations (atomes f) in
  List.map (function i -> eval i f) inter

(** Détermine si une formule est satisfaisable. *)
let est_satisfaisable (f : formule) : bool = List.mem true (all_res f)

(** Renvoie un témoin de la satisfaisabilité d'une formule, s'il en existe. *)
let ex_sat (f : formule) : interpretation option =
  let inter = all_interpretations (atomes f) in
  let rec aux li =
    match li with [] -> None | i :: q -> if eval i f then Some i else aux q
  in
  aux inter

(** Détermine si une formule est une tautologie. *)
let est_tautologie (f : formule) : bool = not (List.mem false (all_res f))

(** Détermine si une formule est une contradiction. *)
let est_contradiction (f : formule) : bool = not (List.mem true (all_res f))

(** Détermine si une formule est contingente. *)
let est_contingente (f : formule) : bool =
  let res = all_res f in
  List.mem true res && List.mem false res

(** ----------------- Exercice 8 : Tables de vérité ----------------- *)

type ligne = string list * bool
(** Type d'une ligne d'une table de vérité. *)

type table = ligne list
(** Type d'une table de vérité. *)

(** Calcule la table de vérité associée à une formule. *)
let table_verite_with (alpha : string list) (f : formule) : table =
  let al = all_sublists (List.sort_uniq String.compare (atomes f @ alpha)) in
  let rec build_lines acc al' : ligne list =
    match al' with
    | [] -> acc
    | t :: q -> build_lines ((t, eval (interpretation_of_list t) f) :: acc) q
  in
  build_lines [] al

let table_of_formule (f : formule) : table = table_verite_with [] f

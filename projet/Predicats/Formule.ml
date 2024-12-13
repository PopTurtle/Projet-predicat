(** Un terme est soit une variable, soit une combinaison d'un symbole de
    fonction et d'une liste de termes. *)
type terme = Var of string | Function of string * terme list

(** Transforme un terme en une chaine de caractères. *)
let rec string_of_terme (t : terme) : string =
  match t with
  | Var s -> s
  | Function (f, ss) ->
      f ^ "(" ^ String.concat ", " (List.map string_of_terme ss) ^ ")"

(** Type des formules quantifiées du calcul des prédicats. *)
type formule =
  | Bot  (** La formule fausse. *)
  | Top  (** La formule vraie. *)
  | Atome of string * terme list
    (* Un symbole de prédicat appliqué sur une liste de termes. *)
  | Non of formule  (** La négation d'une formule. *)
  | Ou of formule * formule  (** La disjonction de deux formules. *)
  | Et of formule * formule  (** La conjonction de deux formules. *)
  | Imp of formule * formule  (** L'implication de deux formules. *)
  | IlExiste of string * formule
      (** La quantification existentielle d'une formule. *)
  | PourTout of string * formule
      (** La quantification universelle d'une formule. *)

(** Transforme une formule en une chaine de caractères. *)
let rec string_of_formule (f : formule) : string =
  let conc_op f g op =
    String.concat ""
      [ "("; string_of_formule f; " "; op; " "; string_of_formule g; ")" ]
  in
  let conc_atome s ts =
    s ^ "(" ^ String.concat ", " (List.map string_of_terme ts) ^ ")"
  in
  match f with
  | Bot -> "⊥"
  | Top -> "⊤"
  | Atome (s, ts) -> conc_atome s ts
  | Non f -> String.concat "" [ "¬"; string_of_formule f ]
  | Et (f, g) -> conc_op f g "∧"
  | Ou (f, g) -> conc_op f g "∨"
  | Imp (f, g) -> conc_op f g "→"
  | IlExiste (s, f) -> "∃" ^ s ^ "(" ^ string_of_formule f ^ ")"
  | PourTout (s, f) -> "∀" ^ s ^ "(" ^ string_of_formule f ^ ")"

module StringSet = Set.Make (String)
(** Module des ensembles de chaines de caractères. *)

(** Renvoie l'ensemble des variables d'un terme. *)
let rec variables (t : terme) : StringSet.t =
  let rec var_of_tl tl =
    match tl with
    | [] -> StringSet.empty
    | t :: q -> StringSet.union (variables t) (var_of_tl q)
  in
  match t with
  | Var v -> StringSet.singleton v
  | Function (_, ts) -> var_of_tl ts

(** Renvoie l'ensemble des variables liées d'une formule. *)
let variables_liees (f : formule) : StringSet.t =
  let rec aux f' ls =
    match f' with
    | Bot | Top -> StringSet.of_list ls
    | Non f -> aux f ls
    | Et (f, g) | Ou (f, g) | Imp (f, g) ->
        StringSet.union (aux f ls) (aux g ls)
    | Atome (_, _) -> StringSet.of_list ls
    | IlExiste (s, f) | PourTout (s, f) -> aux f (s :: ls)
  in
  aux f []

(** Renvoie l'ensemble des variables libres d'une formule. *)
let variables_libres (f : formule) : StringSet.t =
  let rec aux f' =
    match f' with
    | Bot | Top -> StringSet.empty
    | Non f -> aux f
    | Et (f, g) | Ou (f, g) | Imp (f, g) -> StringSet.union (aux f) (aux g)
    | Atome (_, ts) ->
        List.fold_left
          (fun set elt -> StringSet.union set elt)
          StringSet.empty
          (List.map (fun t -> variables t) ts)
    | IlExiste (_, f) | PourTout (_, f) -> aux f
  in
  StringSet.diff (aux f) (variables_liees f)

type 'a interpretation = {
  assoc_fun : string -> 'a list -> 'a option;
  assoc_pred : string -> 'a list -> bool option;
}

(** Une interprétation sur un domaine 'a associe
    - à chaque symbole de fonction une fonction 
      transformant une liste de 'a en 'a option (None s'il y a un problème d'arité)
    - à chaque symbole de prédicat une fonction 
      transformant une liste de 'a en Booléen optionnel (None s'il y a un problème d'arité). *)

type 'a realisation = string -> 'a
(** Une réalisation sur un domaine 'a associe à chaque 
    variable une valeur de type 'a. *)

(** Transforme une liste de 'a option :
    - en une valeur Some [v1; ... vn] si la liste est [Some v1; ...; Some vn]
    - en None si un élément de la liste vaut None. *)
let sequence (ls : 'a option list) : 'a list option =
  let rec aux ls' =
    match ls' with
    | Some [] -> Some []
    | Some (Some elt :: q) -> (
        match aux (Some q) with None -> None | Some q' -> Some (elt :: q'))
    | Some (None :: _) -> None
    | None -> None
  in
  aux (Some ls)

(** Évalue un terme à l'aide d'une interprétation et d'une réalisation.
    Renvoie None si un problème d'arité est rencontré. *)
let rec safe_term_eval (i : 'a interpretation) (r : 'a realisation) (t : terme)
    : 'a option =
  match t with
  | Var x -> Some (r x)
  | Function (f, ts) -> (
      match sequence (List.map (fun t' -> safe_term_eval i r t') ts) with
      | None -> None
      | Some lts -> i.assoc_fun f lts)

(** Foncteur permettant de créer une fonction d'évaluation d'une formule à l'aide d'un type énumérable,
    afin d'énumérer toutes les valeurs lors d'une quantification de variable. *)
module MakeEval (M : Enumerable.Enumerable) = struct
  (** Évalue une formule à l'aide d'une interprétation et d'une réalisation.
      Renvoie None si un problème d'arité est rencontré. *)
  let rec safe_eval (i : M.t interpretation) (r : M.t realisation) (f : formule)
      : bool option =
    let real_edit (r : M.t realisation) (var : string) (value : M.t) :
        M.t realisation =
     fun (v : string) -> if var = v then value else r v
    in
    let op operator v1 v2 =
      match safe_eval i r v1 with
      | None -> None
      | Some f -> (
          match safe_eval i r v2 with
          | None -> None
          | Some g -> Some (operator f g))
    in
    match f with
    | Top -> Some true
    | Bot -> Some false
    | Non f -> (
        match safe_eval i r f with None -> None | Some b -> Some (not b))
    | Et (f, g) -> op ( && ) f g
    | Ou (f, g) -> op ( || ) f g
    | Imp (f, g) -> op (fun a b -> (not a) || b) f g
    | Atome (s, ts) -> (
        let ets = sequence (List.map (safe_term_eval i r) ts) in
        match ets with
        | None -> None
        | Some ets' -> (
            match i.assoc_pred s ets' with None -> None | Some b -> Some b))
    | PourTout (s, f) -> (
        let exec_for elt =
          let r' = real_edit r s elt in
          match safe_eval i r' f with None -> None | Some g -> Some g
        in
        match Seq.uncons M.values with
        | None -> None
        | Some (_, _) ->
            Some
              (Seq.for_all
                 (fun elt ->
                   match exec_for elt with
                   | None -> failwith "impossible"
                   | Some false -> false
                   | Some true -> true)
                 M.values))
    | IlExiste (s, f) -> (
        let exec_for elt =
          let r' = real_edit r s elt in
          match safe_eval i r' f with None -> None | Some g -> Some g
        in
        match Seq.uncons M.values with
        | None -> None
        | Some (_, _) ->
            Some
              (Seq.exists
                 (fun elt ->
                   match exec_for elt with
                   | None -> failwith "impossible"
                   | Some false -> false
                   | Some true -> true)
                 M.values))
end

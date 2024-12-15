open DiagVenn

module Predicate_def = Map.Make (String)
(** Module des Map ayant pour clés des chaînes de caractères *)

module IntSet = Set.Make (Int)
(** Module des ensembles d'entiers *)

(** Renvoie une représentation de l'ensemble d'entiers en chaine de caractère *)
let intset_to_string (iset : IntSet.t) : string =
  if IntSet.is_empty iset then "∅"
  else
    "{"
    ^ String.concat ", " (List.map string_of_int (IntSet.to_list iset))
    ^ "}"

type predicate_def = IntSet.t Predicate_def.t
(** Type synonymes des valeurs de Map ayant pour clés des chaînes de caractères et pour valeur des ensembles d'entiers *)

(** Transforme une Map ayant pour clés des chaines s et pour valeur des ensembles d'entiers ns
      en une liste de couples (chaine s, représentation de l'ensemble ns en chaine) *)
let predicate_def_to_string_couple (p : predicate_def) : (string * string) list
    =
  Predicate_def.fold (fun k v acc -> (k, intset_to_string v) :: acc) p []

(** ens_add_int e n p : ajoute n dans l'ensemble d'entiers associé à la clé e dans la map p *)
let ens_add_int (e : string) (n : int) (p : predicate_def) : predicate_def =
  match Predicate_def.find_opt e p with
  | None -> Predicate_def.add e (IntSet.singleton n) p
  | Some intset -> Predicate_def.add e (IntSet.add n intset) p

(** Renvoie une association predicat -> ensemble d'entiers représentant le diagramme, 
      avec l'entier maximum utilisé, s'il existe *)
let diag_to_predicate_def (d : diagramme) : int option * predicate_def =
  let p, m =
    Diag.fold
      (fun ensset fillv acc ->
        if fillv = Vide then acc
        else
          ( Predicate_set.fold
              (fun str acc' -> ens_add_int str (snd acc + 1) acc')
              ensset (fst acc),
            snd acc + 1 ))
      d (Predicate_def.empty, -1)
  in

  ((if m < 0 then None else Some m), p)

let d1_p : diagramme =
  Diag.of_list
    [
      (Predicate_set.of_list [ "b" ], NonVide);
      (Predicate_set.of_list [ "a"; "b" ], NonVide);
      (Predicate_set.of_list [ "a" ], NonVide);
      (Predicate_set.of_list [ "c" ], Vide);
      (Predicate_set.of_list [], Vide);
    ]

(** Module contenant les informations nécessaires à la création d'une interprétation représentant un diagramme de Venn *)
module type ExempleFromEnum = sig
  type t
  (** Type représentant le domaine d'interprétation *)

  include Enumerable.EnumerableFromInt with type t := t
  (** Valeurs indiquant que le type t est énumérable et est un sous-type des entiers *)

  val i : string -> t -> bool
  (** Fonction indiquant si l'ensemble associé à un prédicat contient une valeur donnée *)

  val preds : predicate_def
  (** Map reliant chaque prédicat à l'ensemble d'entier qui lui est associé, d'une façon équivalente à i *)
end

(** Construit un couple ((M : Module EnumerableFromInt), i: int interpretation) tel que les
      valeurs de M.values correspondent aux zones Non Vide de diag, par la correspondance définie par i *)
let exemple (diag : diagramme) : (module ExempleFromEnum) =
  let n_opt, preds = diag_to_predicate_def diag in

  let n = match n_opt with None -> -1 | Some k -> k in

  let module M = (val Enumerable.enum_from_int n) in
  (module struct
    include M

    let i (x : string) (v : M.t) : bool =
      match Predicate_def.find_opt x preds with
      | None -> false
      | Some set -> IntSet.mem (M.to_int v) set

    let preds = preds
  end)

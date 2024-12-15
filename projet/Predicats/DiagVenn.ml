open Formule_Syllogisme
open Proposition.Formule
(* open Formule_Log_Prop *)

module Predicate_set = Set.Make (String)
(** Module des ensembles de prédicats représentés par des chaines de caractères *)

(** Type des remplissages possibles d'un diagramme de Venn *)
type fill = Vide | NonVide

module Diag = Map.Make (Predicate_set)
(** Module des Maps dont les clés sont des ensembles de chaines de caractères *)

type diagramme = fill Diag.t
(** Type des diagrammes de Venn *)

(** Diagramme de test *)
let d1 : diagramme =
  Diag.of_list
    [
      (Predicate_set.of_list [ "b" ], Vide);
      (Predicate_set.of_list [ "a"; "c" ], NonVide);
      (Predicate_set.of_list [ "a" ], Vide);
      (Predicate_set.of_list [], Vide);
    ]

let string_of_predicate_set (ps : Predicate_set.t) : string =
  if Predicate_set.is_empty ps then "∅"
  else "{" ^ String.concat ", " (Predicate_set.elements ps) ^ "}"

let string_of_fill (f : fill) : string =
  match f with Vide -> "Vide" | NonVide -> "Non Vide"

(** string_of_diag d : conversion d'un diagramme d en une chaine de caractères *)
let string_of_diag (d : diagramme) : string =
  String.concat "\n"
    (Diag.fold
       (fun k v acc ->
         (string_of_predicate_set k ^ " -> " ^ string_of_fill v) :: acc)
       d [])

(** diag_from_formule alpha f : construit le diagramme de Venn associé à la formule f sur
      les prédicats issus de f ou de alpha *)
let diag_from_formule (alpha : string list) (fs : formule_syllogisme) :
    diagramme list =
  let table = table_verite_with alpha in
  match fs with
  | PourTout f ->
      let values =
        List.filter_map
          (fun ligne ->
            match ligne with
            | sl, false -> Some (Predicate_set.of_list sl, Vide)
            | _, true -> None)
          (table f)
      in
      [ Diag.of_list values ]
  | IlExiste f ->
      let values =
        List.filter_map
          (fun ligne ->
            match ligne with
            | sl, true -> Some (Predicate_set.of_list sl)
            | _, false -> None)
          (table f)
      in
      List.map (fun ss -> Diag.singleton ss NonVide) values

(** conj_diag d1 d2 : Calcule la combinaison/conjonction de deux diagrammes, renvoyant None si incompatibilité *)
let conj_diag (d1 : diagramme) (d2 : diagramme) : diagramme option =
  Diag.fold
    (fun k v acc ->
      match acc with
      | None -> None
      | Some d -> (
          match Diag.find_opt k d with
          | None -> Some (Diag.add k v d)
          | Some v' -> if v = v' then Some d else None))
    d2 (Some d1)

(** A SUPPRIMER : Dans les tps cette fonction a été rajoutée.... on l'avait refaite pour les tests mais en mieux*)

(** let conj_diag_list (ds1 : diagramme list) (ds2 : diagramme list) : diagramme list *)

(** Realise toutes les combinaisons possibles à partir des listes de diagrammes *)
let combinaison_of_diag (dss : diagramme list list) : diagramme list =
  match dss with
  | [] -> []
  | t :: q ->
      List.fold_left
        (fun acc d ->
          let ds =
            List.map
              (fun d' -> List.filter_map (fun d'' -> conj_diag d' d'') d)
              acc
          in

          List.sort_uniq compare (List.concat ds))
        t q

(** est_compatible_diag_diag dp dc : teste si le diagramme dp d'une prémisse est compatible
    avec le diagramme dc d'une conclusion *)
let est_compatible_diag_diag (dp : diagramme) (dc : diagramme) : bool =
  Diag.fold
    (fun k v acc ->
      match acc with
      | false -> false
      | _ -> (
          match Diag.find_opt k dp with None -> false | Some v' -> v = v'))
    dc true

(** est_compatible_diag_list dp dcs : teste si un diagramme dp d'une prémisse est compatible
    avec un des diagrammes de la liste dcs,
    diagrammes issus d'une conclusion *)
let est_compatible_diag_list (dp : diagramme) (dcs : diagramme list) : bool =
  List.exists (est_compatible_diag_diag dp) dcs

(** est_compatible_list_list dps dcs : teste si chacun des diagrammes de dps, diagrammes issus de prémisses,
    est compatible avec au moins un des diagrammes de dcs, diagrammes issus d'une conclusion *)
let est_compatible_list_list (dps : diagramme list) (dcs : diagramme list) :
    bool =
  List.for_all ((Fun.flip est_compatible_diag_list) dcs) dps

(** est_compatible_premisses_conc ps c : teste si une liste de prémisses ps est compatible avec une conclusion c *)
let est_compatible_premisses_conc (ps : formule_syllogisme list)
    (c : formule_syllogisme) : bool =
  let alpha = atomes_syllo_list (c :: ps) in
  let diag_c = diag_from_formule alpha c in
  List.for_all
    ((Fun.flip est_compatible_list_list) diag_c)
    (List.map (diag_from_formule alpha) ps)

(** temoin_incompatibilite_premisses_conc_opt ps c : renvoie un diagramme de la combinaison des 
    prémisses ps incompatible avec la conclusion c s'il existe, None sinon *)
let temoin_incompatibilite_premisses_conc_opt (ps : formule_syllogisme list)
    (c : formule_syllogisme) : diagramme option =
  let alpha = atomes_syllo_list (c :: ps) in
  let diag_c = diag_from_formule alpha c in
  let rec test_diag ds =
    match ds with
    | [] -> None
    | t :: q ->
        if est_compatible_diag_list t diag_c then test_diag q else Some t
  in
  test_diag (List.concat (List.map (diag_from_formule alpha) ps))

(** temoins_incompatibilite_premisses_conc ps c : renvoie les diagrammes de la combinaison
    des prémisses ps incompatibles avec la conclusion c *)
let temoins_incompatibilite_premisses_conc (ps : formule_syllogisme list)
    (c : formule_syllogisme) : diagramme list =
  let alpha = atomes_syllo_list (c :: ps) in
  let diag_c = diag_from_formule alpha c in
  let rec test_diag ds =
    match ds with
    | [] -> []
    | t :: q ->
        if est_compatible_diag_list t diag_c then test_diag q
        else t :: test_diag q
  in
  test_diag (List.concat (List.map (diag_from_formule alpha) ps))

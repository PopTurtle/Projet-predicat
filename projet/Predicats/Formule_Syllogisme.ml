open Proposition.Formule

(** Type des formules utilisées pour les syllogismes *)
type formule_syllogisme = PourTout of formule | IlExiste of formule

(** string_of_formule_log_prop_var s f : conversion d'une formule f en chaîne de caractères,
    en les représentant comme des prédicats unaires appliqués sur des 
    occurrences de la variable s. *)
let string_of_formule_log_prop_var (s : string) (f : formule) : string =
  let rec sof (f : formule) : string =
    let conc_op f g op = String.concat "" [ sof f; " "; op; " "; sof g ] in
    match f with
    | Bot -> "⊥"
    | Top -> "⊤"
    | Atome a -> String.concat "" [ a; "("; s; ")" ]
    | Non f -> String.concat "" [ "¬"; sof f ]
    | Et (f, g) -> conc_op f g "∧"
    | Ou (f, g) -> conc_op f g "∨"
    | Imp (f, g) -> conc_op f g "→"
  in
  sof f

(** string_of_formule_syllogisme f : conversion d'une formule f en chaîne de caractères,
    en considérant des prédicats unaires appliqués sur des 
    occurrences de la variable s. *)
let string_of_formule_syllogisme (fs : formule_syllogisme) : string =
  let conc (f : formule) (pre : string) : string =
    String.concat "" [ pre; "x ("; string_of_formule_log_prop_var "x" f; ")" ]
  in
  match fs with PourTout f -> conc f "∀" | IlExiste f -> conc f "∃"

let atomes_syllogisme (fs : formule_syllogisme) : string list =
  match fs with IlExiste f | PourTout f -> atomes f

let atomes_syllo_list (fs : formule_syllogisme list) : string list =
  let atomes = List.map atomes_syllogisme fs in
  List.sort_uniq String.compare (List.concat atomes)

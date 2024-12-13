type formule = Formule.formule
(** Type (synonyme) des formules *)

(** Type des arbres de preuves,
    construit selon les règles de la déduction naturelle.
    Chaque constructeur contient les preuves nécessaires et la formule déduite. *)
type arbre_preuve =
  | Hypo of formule  (** une formule utilisée comme hypothèse *)
  | HypoDechargee of formule
      (** une formule utilisée comme hypothèse déchargée *)
  | ElimImp of arbre_preuve * arbre_preuve * formule
      (** élimination de l'implication (preuve de a → b, preuve de a, formule b)*)
  | ElimDisj of arbre_preuve * arbre_preuve * arbre_preuve * formule
      (** élimination de la disjonction (preuve de a ∨ b, preuve de a → c, preuve de b → c, formule c) *)
  | ElimBot of arbre_preuve * formule
      (** elimination de ⊥ (preuve de ⊥, formule f) *)
  | ElimConjG of arbre_preuve * formule
      (** élimination de la conjonction gauche (preuve de a ∧ b, formule a) *)
  | ElimConjD of arbre_preuve * formule
      (** élimination de la conjonction droite (preuve de a ∧ b, formule b) *)
  | IntroConj of arbre_preuve * arbre_preuve * formule
      (** introduction de la conjonction (preuve de a, preuve de b, formule a ∧ b) *)
  | IntroDisjG of arbre_preuve * formule
      (** introduction de la disjonction gauche (preuve de a, formule a ∨ b) *)
  | IntroDisjD of arbre_preuve * formule
      (** introduction de la disjonction droite (preuve de b, formule a ∨ b) *)
  | IntroImp of arbre_preuve * formule
      (** introduction de l'implication (preuve de b, formule a → b) *)

(* let exemple_ok = ElimConjG (Hypo (Et (Atome "a", Atome "b")), Atome "a")

   let exemple_ko =
     let a = Formule.Atome "a" in
     ElimImp (Hypo a, Hypo a, a) *)

(** Module de manipulation des ensembles de formules *)
module FormuleSet = Set.Make (struct
  type t = formule

  let compare = Stdlib.compare
end)

(* ***** Fonctions utilitaires ***** *)

(** Renvoie les hypothèses (non déchargées) d'une preuve. *)
let rec get_hyp =
  let open FormuleSet in
  function
  | Hypo f -> singleton f
  | HypoDechargee _ -> empty
  | ElimImp (p1, p2, _) | IntroConj (p1, p2, _) ->
      union (get_hyp p1) (get_hyp p2)
  | ElimDisj (p1, p2, p3, _) ->
      union (get_hyp p1) (get_hyp p2) |> union (get_hyp p3)
  | ElimBot (p, _)
  | ElimConjD (p, _)
  | ElimConjG (p, _)
  | IntroDisjD (p, _)
  | IntroDisjG (p, _)
  | IntroImp (p, _) ->
      get_hyp p

(** Renvoie la conclusion d'une preuve. *)
let get_conc = function
  | HypoDechargee f
  | Hypo f
  | ElimImp (_, _, f)
  | ElimDisj (_, _, _, f)
  | ElimBot (_, f)
  | ElimConjD (_, f)
  | ElimConjG (_, f)
  | IntroConj (_, _, f)
  | IntroDisjD (_, f)
  | IntroDisjG (_, f)
  | IntroImp (_, f) ->
      f

(* ***** Règles sans préconditions à vérifier. ***** *)

(** hypo f : Constructeur de l'hypothèse f. *)
let hypo (f : formule) : arbre_preuve = Hypo f

(** intro_conj a b : construit une preuve de a ∧ b à partir de preuves
    de a et de b. *)
let intro_conj (p1 : arbre_preuve) (p2 : arbre_preuve) : arbre_preuve =
  IntroConj (p1, p2, Et (get_conc p1, get_conc p2))

(** intro_disj_d a b : construit une preuve de a ∨ b à partir d'une preuve
        de a. *)
let intro_disj_d (p : arbre_preuve) (f : formule) : arbre_preuve =
  IntroDisjD (p, Ou (get_conc p, f))

(** intro_disj_g b a : construit une preuve de a ∨ b à partir d'une preuve
        de b. *)
let intro_disj_g (p : arbre_preuve) (f : formule) : arbre_preuve =
  IntroDisjG (p, Ou (get_conc p, f))

(* Règles avec préconditions à vérifier. *)

(** elim_imp (a → b) a : construit une preuve de b à partir de preuves de
    a → b et de a. Renvoie None si les paramètres sont incorrects. *)
let elim_imp (pimp : arbre_preuve) (p : arbre_preuve) : arbre_preuve option =
  match get_conc pimp with
  | Imp (a, b) -> if a = get_conc p then Some (ElimImp (pimp, p, b)) else None
  | _ -> None

(** elim_disj (a ∨ b) (a → c) (b → c) : construit une preuve de c à partir de preuves de
    a ∨ b, a → c et b → c. Renvoie None si les paramètres sont incorrects. *)
let elim_disj (pdisj : arbre_preuve) (pia : arbre_preuve) (pib : arbre_preuve) :
    arbre_preuve option =
  match (get_conc pdisj, get_conc pia, get_conc pib) with
  | Ou (a, b), Imp (a', c), Imp (b', c') when a = a' && b = b' && c = c' ->
      Some (ElimDisj (pdisj, pia, pib, c))
  | _ -> None

(** elim_bot ⊥ f : construit une preuve de f à partir d'une preuve de
    ⊥. Renvoie None si le paramètre est incorrect. *)
let elim_bot (pbot : arbre_preuve) (f : formule) : arbre_preuve option =
  match get_conc pbot with Bot -> Some (ElimBot (pbot, f)) | _ -> None

(** elim_conj_d (a ∧ b) : construit une preuve de b à partir d'une preuve de
    a ∧ b. Renvoie None si le paramètre est incorrect. *)
let elim_conj_d (pconj : arbre_preuve) : arbre_preuve option =
  match get_conc pconj with
  | Et (_, b) -> Some (ElimConjD (pconj, b))
  | _ -> None

(** elim_conj_g (a ∧ b) : construit une preuve de a à partir d'une preuve de
    a ∧ b. Renvoie None si le paramètre est incorrect. *)
let elim_conj_g (pconj : arbre_preuve) : arbre_preuve option =
  match get_conc pconj with
  | Et (a, _) -> Some (ElimConjG (pconj, a))
  | _ -> None

(* ***** Règle de l'introduction de l'implication. ***** *)

(** intro_imp f g : construit une preuve de f → g à partir d'une preuve de
    g. Décharge les occurences de f dans la preuve de g.*)
let intro_imp (f : formule) (g : arbre_preuve) : arbre_preuve =
  let rec decharge h =
    match h with
    | HypoDechargee f' -> HypoDechargee f'
    | Hypo f' -> if f' = f then HypoDechargee f' else Hypo f'
    | ElimImp (a, b, f') -> ElimImp (decharge a, decharge b, f')
    | ElimDisj (a, b, c, f') -> ElimDisj (decharge a, decharge b, decharge c, f')
    | ElimBot (a, f') -> ElimBot (decharge a, f')
    | ElimConjD (a, f') -> ElimConjD (decharge a, f')
    | ElimConjG (a, f') -> ElimConjG (decharge a, f')
    | IntroConj (a, b, f') -> IntroConj (decharge a, decharge b, f')
    | IntroDisjD (a, f') -> IntroDisjD (decharge a, f')
    | IntroDisjG (a, f') -> IntroDisjG (decharge a, f')
    | IntroImp (a, f') -> IntroImp (decharge a, f')
  in
  IntroImp (decharge g, Imp (f, get_conc g))

(* ***** Représentation à la Fitch. ***** *)

(** Transforme une liste de compteurs en une chaine. *)
let string_of_counters counters =
  List.rev_map string_of_int counters |> String.concat "."

(** Incrémente le dernier élément d'un compteur. *)
let inc_counter = function
  | c :: cs -> (c + 1) :: cs
  | _ -> failwith "inc_counter : empty counter"

(** fitch_dec dec cs p : créé une représentation en chaine d'une preuve p
    à la Fitch, avec un décalage dec (nb d'espaces) à gauche,
    un compteur courant cs, et renvoie le nouveau compteur. *)
let rec fitch_dec (dec : int) : int list -> arbre_preuve -> string * int list =
  function
  | [] -> failwith "Bad counter"
  | counters -> (
      function
      | Hypo f ->
          let counters' = inc_counter counters in
          ( Printf.sprintf "%*s %s Hypothèse : %s" dec ""
              (string_of_counters counters')
              (Formule.string_of_formule f),
            counters' )
      | HypoDechargee f ->
          let counters' = inc_counter counters in
          ( Printf.sprintf "%*s %s Hypothèse déchargée : %s" dec ""
              (string_of_counters counters')
              (Formule.string_of_formule f),
            counters' )
      | ElimImp (p1, p2, f) ->
          let s1, cs1 = fitch_dec dec counters p1 in
          let s2, cs2 = fitch_dec dec cs1 p2 in
          let counters' = inc_counter cs2 in
          ( Printf.sprintf
              "%s\n%s\n%*s %s Élimination de l'implication(%s, %s) : %s" s1 s2
              dec ""
              (string_of_counters counters')
              (string_of_counters cs1) (string_of_counters cs2)
              (Formule.string_of_formule f),
            counters' )
      | IntroConj (p1, p2, f) ->
          let s1, cs1 = fitch_dec dec counters p1 in
          let s2, cs2 = fitch_dec dec cs1 p2 in
          let counters' = inc_counter cs2 in
          ( Printf.sprintf
              "%s\n%s\n%*s %s Introduction de la conjonction(%s, %s): %s" s1 s2
              dec ""
              (string_of_counters counters')
              (string_of_counters cs1) (string_of_counters cs2)
              (Formule.string_of_formule f),
            counters' )
      | ElimDisj (p1, p2, p3, f) ->
          let s1, cs1 = fitch_dec dec counters p1 in
          let s2, cs2 = fitch_dec dec cs1 p2 in
          let s3, cs3 = fitch_dec dec cs2 p3 in
          let counters' = inc_counter cs3 in
          ( Printf.sprintf
              "%s\n\
               %s\n\
               %s\n\
               %*s %s Élimination de la disjonction(%s, %s, %s) : %s" s1 s2 s3
              dec ""
              (string_of_counters counters')
              (string_of_counters cs1) (string_of_counters cs2)
              (string_of_counters cs3)
              (Formule.string_of_formule f),
            counters' )
      | ElimBot (p, f) ->
          let s, cs = fitch_dec dec counters p in
          let counters' = inc_counter cs in
          ( Printf.sprintf "%s\n%*s %s Élimination de Bot(%s) : %s" s dec ""
              (string_of_counters counters')
              (string_of_counters cs)
              (Formule.string_of_formule f),
            counters' )
      | ElimConjD (p, f) ->
          let s, cs = fitch_dec dec counters p in
          let counters' = inc_counter cs in
          ( Printf.sprintf
              "%s\n%*s %s Élimination de la conjonction droite(%s) : %s" s dec
              ""
              (string_of_counters counters')
              (string_of_counters cs)
              (Formule.string_of_formule f),
            counters' )
      | ElimConjG (p, f) ->
          let s, cs = fitch_dec dec counters p in
          let counters' = inc_counter cs in
          ( Printf.sprintf
              "%s\n%*s %s Élimination de la conjonction gauche(%s) : %s" s dec
              ""
              (string_of_counters counters')
              (string_of_counters cs)
              (Formule.string_of_formule f),
            counters' )
      | IntroDisjD (p, f) ->
          let s, cs = fitch_dec dec counters p in
          let counters' = inc_counter cs in
          ( Printf.sprintf
              "%s\n%*s %s Introduction de la disjonction droite(%s) : %s" s dec
              ""
              (string_of_counters counters')
              (string_of_counters cs)
              (Formule.string_of_formule f),
            counters' )
      | IntroDisjG (p, f) ->
          let s, cs = fitch_dec dec counters p in
          let counters' = inc_counter cs in
          ( Printf.sprintf
              "%s\n%*s %s Introduction de la disjonction gauche(%s) : %s" s dec
              ""
              (string_of_counters counters')
              (string_of_counters cs)
              (Formule.string_of_formule f),
            counters' )
      | IntroImp (p, f) ->
          let counters' = inc_counter counters in
          let s, cs = fitch_dec (dec + 2) (0 :: counters') p in
          ( Printf.sprintf "%s\n%*s %s Introduction de l'implication(%s) : %s" s
              dec ""
              (string_of_counters counters')
              (string_of_counters cs)
              (Formule.string_of_formule f),
            counters' ))

(** Créé une représentation (string) à la Fitch d'une preuve donnée. *)
let fitch p =
  let f = get_conc p and hypos = get_hyp p in
  let s_hyps =
    FormuleSet.elements hypos
    |> List.map Formule.string_of_formule
    |> String.concat ", "
  in
  Printf.sprintf "Preuve: %s ⊢ %s\n%s" s_hyps
    (Formule.string_of_formule f)
    (fst (fitch_dec 0 [ 0 ] p))

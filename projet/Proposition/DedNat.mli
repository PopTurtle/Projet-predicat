module FormuleSet : Set.OrderedType
(** Module de manipulation des ensembles de formules *)

type formule = Formule.formule
(** Type (synonyme) des formules *)

type arbre_preuve
(** Type des arbres de preuves,
    construit selon les règles de la déduction naturelle. *)

(* ***** Fonctions utilitaires ***** *)

val get_hyp : arbre_preuve -> FormuleSet.t
(** Renvoie les hypothèses (non déchargées) d'une preuve. *)

val get_conc : arbre_preuve -> formule
(** Renvoie la conclusion d'une preuve. *)

(* ***** Règles sans préconditions à vérifier. ***** *)

val hypo : formule -> arbre_preuve
(** hypo f : Constructeur de l'hypothèse f. *)

val intro_conj : arbre_preuve -> arbre_preuve -> arbre_preuve
(** intro_conj a b : construit une preuve de a ∧ b à partir de preuves
    de a et de b. *)

val intro_disj_d : arbre_preuve -> Formule.formule -> arbre_preuve
(** intro_disj_d a b : construit une preuve de a ∨ b à partir d'une preuve
        de a. *)

val intro_disj_g : arbre_preuve -> Formule.formule -> arbre_preuve
(** intro_disj_g b a : construit une preuve de a ∨ b à partir d'une preuve
        de b. *)

(* Règles avec préconditions à vérifier. *)

val elim_imp : arbre_preuve -> arbre_preuve -> arbre_preuve option
(** elim_imp (a → b) a : construit une preuve de b à partir de preuves de
    a → b et de a. Renvoie None si les paramètres sont incorrects. *)

val elim_disj :
  arbre_preuve -> arbre_preuve -> arbre_preuve -> arbre_preuve option
(** elim_disj (a ∨ b) (a → c) (b → c) : construit une preuve de c à partir de preuves de
    a ∨ b, a → c et b → c. Renvoie None si les paramètres sont incorrects. *)

val elim_bot : arbre_preuve -> formule -> arbre_preuve option
(** elim_bot ⊥ f : construit une preuve de f à partir d'une preuve de
    ⊥. Renvoie None si le paramètre est incorrect. *)

val elim_conj_d : arbre_preuve -> arbre_preuve option
(** elim_conj_d (a ∧ b) : construit une preuve de b à partir d'une preuve de
    a ∧ b. Renvoie None si le paramètre est incorrect. *)

val elim_conj_g : arbre_preuve -> arbre_preuve option
(** elim_conj_g (a ∧ b) : construit une preuve de a à partir d'une preuve de
    a ∧ b. Renvoie None si le paramètre est incorrect. *)

(* ***** Règle de l'introduction de l'implication. ***** *)

val intro_imp : formule -> arbre_preuve -> arbre_preuve
(** intro_imp f g : construit une preuve de f → g à partir d'une preuve de
    g. Décharge les occurences de f dans la preuve de g.*)

(* ***** Représentation à la Fitch. ***** *)

val fitch : arbre_preuve -> string
(** Créé une représentation (string) à la Fitch d'une preuve donnée. *)

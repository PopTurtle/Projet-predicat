open DedNat
open Formule

(* Opérateurs de promotion de fonctions *)
let ( <$> ) : ('a -> 'b) -> 'a option -> 'b option = Option.map

let ( <*> ) (m_f : ('a -> 'b) option) (m_v : 'a option) : 'b option =
  match (m_f, m_v) with Some f, Some v -> Some (f v) | _ -> None

let ( >>= ) : 'a option -> ('a -> 'b option) -> 'b option = Option.bind

let liftM2 (f : 'a -> 'b -> 'c option) (v1 : 'a option) (v2 : 'b option) :
    'c option =
  f <$> v1 <*> v2 |> Option.join

(* Formules de base *)
let a = Atome "a"
let b = Atome "b"
let c = Atome "c"
let a_et_b = Et (a, b)

(* let exemple_ko =
   let a = Formule.Atome "a" in
   ElimImp (Hypo a, Hypo a, a) *)

(* Preuve : a → b -> c, a → b,  a  ⊢ c *)
let p_a_imp_b_imp_c = hypo (Imp (a, Imp (b, c)))
let p_a_imp_b = hypo (Imp (a, b))
let p_a = hypo a
let p_b = elim_imp p_a_imp_b p_a
let p_b_imp_c = elim_imp p_a_imp_b_imp_c p_a

let p_c_long =
  match (p_b_imp_c, p_b) with Some p1, Some p2 -> elim_imp p1 p2 | _ -> None

let p_c = liftM2 elim_imp p_b_imp_c p_b

(* Preuve : a → b → c, a → b ⊢ a → c *)
let p_a_imp_c = intro_imp a <$> p_c

(* Preuve : a → b → c, a ∧ b ⊢ c *)
let p_a_et_b = hypo (Et (a, b))
let p_a2 = elim_conj_g p_a_et_b
let p_b2 = elim_conj_d p_a_et_b
let p_b_imp_c2 = p_a2 >>= elim_imp p_a_imp_b_imp_c
let p_c2 = liftM2 elim_imp p_b_imp_c2 p_b2

(* Preuve : a → b → c ⊢ a ∧ b → c *)
let p_a_et_b_imp_c = intro_imp a_et_b <$> p_c2

(* Preuve :  ⊢ (a → b → c ) → a ∧ b → c *)
let p_a_imp_b_imp_c_imp_a_et_b_imp_c =
  intro_imp (Imp (a, Imp (b, c))) <$> p_a_et_b_imp_c

(* Fonction d'affichage d'une preuve optionnelle *)
let ( <.> ) f g x = f (g x)
let print_preuve_opt = Option.iter (print_endline <.> fitch)

(* Preuve : a -> a *)
let p_a = hypo a
let p_a_imp_a = intro_imp a p_a

(* Preuve : a -> non non a *)
let p_a = hypo a
let p_a_imp_bot = hypo (Imp (a, Bot))
let p_bot = elim_imp p_a_imp_bot p_a
let p_a_imp_bot_imp_bot = intro_imp (get_conc p_a_imp_bot) <$> p_bot
let p_a_imp_a_imp_bot_imp_bot = intro_imp a <$> p_a_imp_bot_imp_bot

(* Affiche des exemples de preuves *)
let run_exemples () =
  print_preuve_opt p_c;
  print_preuve_opt p_a_imp_c;
  print_preuve_opt p_c2;
  print_preuve_opt p_a_et_b_imp_c;
  print_preuve_opt p_a_imp_b_imp_c_imp_a_et_b_imp_c;

  print_preuve_opt (Some p_a_imp_a);
  print_preuve_opt p_a_imp_a_imp_bot_imp_bot

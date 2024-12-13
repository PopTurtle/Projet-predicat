open Formule

let f1 =
  PourTout
    ( "x",
      Imp
        ( Atome ("<=", [ Var "x"; Var "0" ]),
          Atome (">=", [ Function ("abs", [ Var "x" ]); Var "0" ]) ) )

let rec choose (values : ('a * 'b) list) (choice : 'a) : 'b option =
  match values with
  | [] -> None
  | t :: q -> if fst t = choice then Some (snd t) else choose q choice

(** Créer la realisation dont la valeur par défaut est default *)
let realisation_from (values : (string * 'a) list) (default : 'a) (str : string)
    =
  match choose values str with None -> default | Some r -> r

let assoc_fun_from (funs : (string * ('a list -> 'a option)) list) :
    string -> 'a list -> 'a option =
 fun str args -> match choose funs str with None -> None | Some f -> f args

let assoc_pred_from (funs : (string * ('a list -> bool option)) list) :
    string -> 'a list -> bool option =
 fun str args -> match choose funs str with None -> None | Some f -> f args

let f1_real (str : string) = realisation_from [ ("0", 0) ] 0 str

let f1_inter =
  {
    assoc_fun =
      assoc_fun_from
        [
          ("abs", fun al -> match al with t :: [] -> Some (abs t) | _ -> None);
        ];
    assoc_pred =
      assoc_pred_from
        [
          ("<=", fun al -> match al with [ t; q ] -> Some (t <= q) | _ -> None);
          (">=", fun al -> match al with [ t; q ] -> Some (t >= q) | _ -> None);
        ];
  }

open Formule_Syllogisme
open Proposition.Formule
open DiagVenn

let a = Atome "a"
let b = Atome "b"
let c = Atome "c"
let d = Atome "d"
let p1 = PourTout (Imp (Ou (a, b), c))
let p2 = PourTout (Imp (c, Ou (a, b)))
let p3 = IlExiste a
let p4 = IlExiste (Imp (a, Non b))

let p5 =
  let xor (a, b) = Ou (Et (a, Non b), Et (Non a, b)) in
  PourTout (Imp (xor (a, b), c))

let p6 = PourTout (Imp (Non c, a))
let p7 = IlExiste (Et (Et (a, c), Non b))
let c1 = IlExiste b
let c2 = IlExiste c
let c3 = IlExiste d

(** valeurs de test *)
let p10 = [ p1; p2; p3 ]

let c10 = c1

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

(** test premisses conclusion : teste si chacun des diagrammes de la combinaison
    de la liste prémisses est compatible avec au moins un des diagrammes de conclusion,
    tout en traçant les calculs réalisés et les diagrammes calculés,
    et en affichant tous les contre-exemples le cas échéant. *)
let test (premisses : formule_syllogisme list) (conclusion : formule_syllogisme)
    : unit =
  let alpha = atomes_syllo_list (conclusion :: premisses) in

  print_endline "Prémisses :";
  List.iter print_endline
    (List.map (fun p -> "\t" ^ string_of_formule_syllogisme p) premisses);

  print_endline "Conclusion :";
  print_endline ("\t" ^ string_of_formule_syllogisme conclusion);

  print_endline "Diagrammes de chaque prémisses :";
  List.iteri
    (fun i p ->
      print_endline
        ("\tDiagrammes de la prémisse " ^ string_of_int (i + 1) ^ ":");
      let ds = diag_from_formule alpha p in
      List.iteri
        (fun i d ->
          print_endline
            (("\t\tDiagramme " ^ string_of_int (i + 1) ^ "\n")
            ^ string_of_diag d))
        ds)
    premisses;

  print_endline "Diagrammes de la combinaison :";

  let dss = List.map (fun d -> diag_from_formule alpha d) premisses in
  let combi = combinaison_of_diag dss in
  List.iteri
    (fun i d ->
      print_endline ("\tDiagramme " ^ string_of_int (i + 1) ^ ":");
      print_endline (string_of_diag d))
    combi;

  print_endline "Diagrammes de la conclusion :";

  let diag_conc = diag_from_formule alpha conclusion in
  List.iteri
    (fun i d ->
      print_endline ("\tDiagramme " ^ string_of_int (i + 1) ^ ":");
      print_endline (string_of_diag d))
    diag_conc;

  match temoins_incompatibilite_premisses_conc premisses conclusion with
  | [] -> print_endline "Conclusion compatible avec les diagrammes"
  | q ->
      print_endline
        "Conclusion incompatible avec les diagrammes, contre-exemples:";
      List.iter (fun d -> print_endline (string_of_diag d)) q

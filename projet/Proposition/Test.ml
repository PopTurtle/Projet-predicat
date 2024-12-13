(** Module de Test :
    usage :
      - lancer dans le terminal la commande dune utop
      - ouvrir la bibliothèque : open Proposition ;;
      - ensuite, soit :
        - ouvrir le module : open Test;;
          les définitions deviennent accessibles : f;;
        - soit sélectionner du code et l'envoyer dans le terminal,
          sans oublier d'ajouter ";;"
    NB : pour envoyer du code dans un terminal ouvert, il faut ajouter
      le raccourci :
      - Ctrl+k Ctrl +s : ouverture des raccourcis clavier
      - chercher : terminal.runSelectedText
      - entrer un raccourci (par exemple Ctrl + F6)
    *)

open Formule
open FromString

let f : formule option = form_from_string "x + y -> z"
let f2 : formule option = form_from_string "x -> y -> z"
let f3 : formule option = form_from_string "x * y * z"
let f4 : formule option = form_from_string "x + y * z"
let f5 : formule = Option.get (form_from_string "a * b + c -> ~ d")
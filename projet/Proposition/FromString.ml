open Formule

(** Transforme une chaine de caractères en une formule :
    - les atomes sont des chaines de caractères écrites sur ['a' - 'z']
    - les opérateurs sont +, *, ~, ->
    - Bot et Top sont représentés par 0 et 1
    - les parenthèses permettent de modifier la priorité
    - les espaces sont autorisés.
    
    Par exemple,
      form_from_string "a + b" renvoie Some (Ou(Atome "a", Atome "b"))
      form_from_string "+a5" renvoie None
      *)
let form_from_string (str : string) : formule option =
  try Some (Parser.f Lexer.string_form (Lexing.from_string str))
  with _ -> None

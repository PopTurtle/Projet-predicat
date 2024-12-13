{
  open Parser
}

(*Regex*)
let atome = ['a'-'z']+
let top = '1'
let bot = '0'
let non = '~'
let ou = '+'|'|'
let et = '*'|'&'
let imp = "->" 
let paro = '('
let parf = ')'

rule string_form = parse 
    | top       {TOP}
    | bot       {BOT}
    | atome     {ATOME (Lexing.lexeme lexbuf)}
    | ou        {OU}
    | et        {ET}
    | non       {NON}
    | imp       {IMP}
    | paro      {PARO}
    | parf      {PARF}
    | eof       {EOF}
    | ' '       {string_form lexbuf}
%{
%}

%token PARO
%token PARF
%token <string> ATOME
%token OU
%token ET
%token IMP
%token BOT
%token TOP
%token NON
%token EOF
%right IMP

%left OU
%left ET
%left NON

%start <Formule.formule> f

%%

f : e = form; EOF { e }

form :
    | BOT                        {Formule.Bot}
    | TOP                        {Top}
    | PARO f1 = form; PARF       {f1}
    | x = ATOME                  {Atome x}
    | f1 = form; OU; f2 = form   {Ou(f1, f2)}
    | f1 = form; ET; f2 = form   {Et(f1, f2)}
    | f1 = form; IMP ; f2 = form {Formule.Imp(f1, f2)}
    | NON f1=form;               {Formule.Non f1}
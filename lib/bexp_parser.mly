%token <string> PROP_VAR
%token LEFT_PAREN
%token RIGHT_PAREN
%token AND
%token OR
%token NOT
%token EOF

%start <Bexp.uc_formula> single_exp 

%type <Bexp.uc_formula> bexp


%left OR
%left AND
%nonassoc NOT

%%

single_exp: b=bexp; EOF { b }
    

bexp:
    | v = PROP_VAR { Bexp.Var v }
    | NOT; e = bexp { Bexp.Not e }
    | LEFT_PAREN; e = bexp; RIGHT_PAREN { e }
    | e1 = bexp; AND; e2 = bexp {Bexp.And (e1, e2) }
    | e1 = bexp; OR; e2 = bexp {Bexp.Or (e1, e2) }

%token <string> PROP_VAR
%token LEFT_PAREN
%token RIGHT_PAREN
%token COMMA
%token EQUAL
%token AND
%token OR
%token NOT
%token EOF


%start <EUF.uc_formula> single_exp 

%type <EUF.uc_formula> bexp


%left OR
%left AND
%nonassoc NOT
%type <EUF.FuncExpr.t>  atom

%%

single_exp: b=bexp; EOF { b }

atom:  
    | v = PROP_VAR { EUF.FuncExpr.Var v }
    | nm = PROP_VAR; LEFT_PAREN; vl=separated_list(COMMA, atom); RIGHT_PAREN {
       EUF.FuncExpr.App{name=nm; args=vl}
    }

eq_clause:
    | a1=atom; EQUAL; a2=atom { EUF.Atom (EUF.EqCons.Eq (a1, a2)) }
bexp:
    | a=eq_clause { a }
    | NOT; e = bexp { EUF.Not e }
    | LEFT_PAREN; e = bexp; RIGHT_PAREN { e }
    | e1 = bexp; AND; e2 = bexp {EUF.And (e1, e2) }
    | e1 = bexp; OR; e2 = bexp {EUF.Or (e1, e2) }

open Simple_verif


module S = DPLL.SolverState(CCString)

let () = 
  Printexc.record_backtrace true;;
  let tgt_args = Bos.OS.Arg.(parse ~pos:string ()) in
  let to_parse = List.hd tgt_args in 
    let nnf_form =  ((Bexp_parser.single_exp Bexp_lexer.read (Lexing.from_string to_parse)) |> Bexp.rewrite_to_nnf) in
      nnf_form |> Bexp.show_nnf_formula |> print_endline;
    let cnf_form = Bexp.rewrite_to_cnf_clauses nnf_form in 
      cnf_form |> Bexp.show_cnf_formula |> print_endline;
      match S.solve_inject cnf_form with 
        |`Unsat -> print_endline "Unsat!"
        | `Sat st -> print_endline ("Sat! \n " ^ S.M.show st.model)
    



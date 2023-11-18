open Simple_verif




let () = 
  let tgt_args = Bos.OS.Arg.(parse ~pos:string ()) in
  let to_parse = List.hd tgt_args in 
    Bexp.show_nnf_formula ((Bexp_parser.single_exp Bexp_lexer.read (Lexing.from_string to_parse)) |> Bexp.rewrite_to_nnf) |> print_endline



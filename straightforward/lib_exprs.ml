open Parser_lib

let prio expr table =
  let len = Array.length table in
  let rec helper level =
    if level >= len then expr
    else
      let xs = table.(level) in
      return (fun h tl -> List.fold_left (fun acc (op, r) -> op acc r) h tl)
      <*> helper (level + 1)
      <*> many
            (choice
               (List.map
                  (fun (op, f) ->
                    op *> helper (level + 1) >>= fun r -> return (f, r))
                  xs))
  in
  helper 0

module Expr = struct
  type bin_op = Plus | Dash | Asterisk | Slash
  [@@deriving show { with_path = false }, variants]

  type expr = Const of int | Binop of bin_op * expr * expr
  [@@deriving show { with_path = false }, variants]

  let expr_small = digit >>| const

  let expr =
    prio expr_small
      [|
        [ (ws *> char '+' <* ws, binop plus); (char '-', binop dash) ];
        [
          (ws *> char '*' <* ws, binop asterisk);
          (ws *> char '/' <* ws, binop slash);
        ];
      |]

  let%expect_test _ =
    test expr pp_expr "asdf";
    [%expect {| Error: '' |}]

  let%expect_test _ =
    test expr pp_expr "1+2";
    [%expect {| Binop (Plus, Const (1), Const (2)) |}]

  let%expect_test _ =
    test expr pp_expr "1+2*3";
    [%expect
      {| Binop (Plus, Const (1), Binop (Asterisk, Const (2), Const (3))) |}]

  open Format

  let rec pretty ppf = function
    | Const n -> fprintf ppf "%d" n
    | Binop (Plus, l, r) -> fprintf ppf "%a+%a" pretty l pretty r
    | Binop (Dash, l, r) -> fprintf ppf "%a-%a" pretty l pretty r
    | Binop (Asterisk, l, r) -> fprintf ppf "%a*%a" pretty l pretty r
    | Binop (Slash, l, r) -> fprintf ppf "%a/%a" pretty l pretty r

  let%expect_test _ =
    test expr pretty "1+2*3";
    [%expect {| 1+2*3 |}]

  let%expect_test _ =
    test expr pretty "0+0*0";
    [%expect {| 0+0*0 |}]

  let%expect_test _ =
    let input =
      String.init 900001 (fun n -> if n mod 2 <> 0 then '*' else '1')
    in
    (* print_endline input;  *)
    test expr (fun ppf _ -> Format.fprintf ppf "parsable") input;
    [%expect {| parsable |}]
end

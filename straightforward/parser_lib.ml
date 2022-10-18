(* Библиотека парсер-комбинаторов от печки *)
type input = char list
type 'a parse_result = Failed | Parsed of 'a * input
type 'a parser = input -> 'a parse_result

let pp_parse_result f ppf = function
  | Failed -> Format.fprintf ppf "fail"
  | Parsed (x, _) -> Format.fprintf ppf "Parsed (%a,_)" f x

(* ***************** Простой парсер 1 ********************* *)
let fail _ = Failed
let return x : _ parser = fun s -> Parsed (x, s)

let char c : _ parser = function
  | h :: tl when c = h -> return c tl
  | _ -> Failed

let%test _ = char 'a' [ 'a'; 'b' ] = return 'a' [ 'b' ]
let%test _ = char 'b' [ 'a'; 'b' ] = Failed

let satisfy cond : _ parser = function
  | h :: tl when cond h -> return h tl
  | _ -> Failed

let char c = satisfy (Char.equal c)

let digit_c =
  let is_digit ch =
    let c = Char.code ch in
    Char.code '0' <= c && c <= Char.code '9'
  in
  satisfy is_digit

let%test _ = digit_c [ '0' ] = return '0' []
let%test _ = digit_c [ 'a' ] = Failed

(* ****************** Простой парсер 2 ********************************** *)
(* произносится bind, или 'a затем' *)
let ( >>= ) : 'a 'b. 'a parser -> ('a -> 'b parser) -> 'b parser =
 fun p f s -> match p s with Failed -> Failed | Parsed (h, tl) -> f h tl

(* ******************** Простые комбинаторы ***************************** *)
let ( *> ) : 'a 'b. 'a parser -> 'b parser -> 'b parser =
 fun p1 p2 -> p1 >>= fun _ -> p2

let%test _ =
  let p1 = char 'a' *> char 'b' in
  p1 [ 'a'; 'b' ] = return 'b' []

let ( <* ) : _ parser -> _ parser -> _ parser =
 fun p1 p2 ->
  p1 >>= fun h ->
  p2 >>= fun _ -> return h

let%test _ =
  let p2 = char 'a' <* char 'b' in
  p2 [ 'a'; 'b' ] = return 'a' []

let digit = digit_c >>= fun c -> return (Char.code c - Char.code '0')

let%test _ = digit [ '5' ] = return 5 []

(* *************************************************************** *)
let ( >>| ) x f s =
  match x s with Failed -> Failed | Parsed (x, tl) -> Parsed (f x, tl)

let ( <*> ) f x input =
  match f input with
  | Failed -> Failed
  | Parsed (f, tl) -> (
      match x tl with Failed -> Failed | Parsed (x, tl) -> Parsed (f x, tl))

let ( let* ) = ( >>= )

let ( let+ ) p f input =
  match p input with Failed -> Failed | Parsed (x, tl) -> Parsed (f x, tl)

let ( and+ ) f1 f2 input =
  match f1 input with
  | Failed -> Failed
  | Parsed (l, input) -> (
      match f2 input with
      | Failed -> Failed
      | Parsed (r, rest) -> Parsed ((l, r), rest))

(* *************************************************************** *)
let many : 'a parser -> 'a list parser =
 fun p ->
  let rec helper s =
    match p s with
    | Failed -> return [] s
    | Parsed (x, tl) -> (helper >>= fun xs -> return (x :: xs)) tl
  in
  helper

let%test _ =
  let p = many (char 'a') in
  let input = [ 'b'; 'a'; 'b' ] in
  Parsed ([], input) = p input

let%test _ =
  let p = many (char 'b') in
  Parsed ([ 'b'; 'b' ], [ 'a' ]) = p [ 'b'; 'b'; 'a' ]

let many1 p : _ list parser =
  p >>= fun x ->
  many p >>= fun xs -> return (x :: xs)

let%test _ =
  let p = many1 (char 'b') in
  Parsed ([ 'b'; 'b' ], [ 'a' ]) = p [ 'b'; 'b'; 'a' ]

let%test _ =
  let p = many1 (char 'a') in
  Failed = p [ 'b'; 'a'; 'b' ]

(* ************** Alternatives  ********************************** *)
let ( <|> ) : 'a parser -> 'a parser -> 'a parser =
 fun p1 p2 s -> match p1 s with Failed -> p2 s | ok -> ok

let a_or_b = char 'a' <|> char 'b'

let%test _ = a_or_b [ 'a' ] = return 'a' []
let%test _ = a_or_b [ 'b' ] = return 'b' []
let%test _ = a_or_b [ 'c' ] = Failed

let choice = function [] -> fail | h :: tl -> List.fold_left ( <|> ) h tl

module Arithmetic1 = struct
  type expr = Const of int | Plus of expr * expr [@@deriving show]

  (* <expr> -- это <digit> + <expr> или <digit>
  *)

  let parser =
    let const = digit >>= fun d -> return (Const d) in
    let rec p s =
      (const
      >>= (fun l -> char '+' *> p >>= fun r -> return (Plus (l, r)))
      <|> const)
        s
    in
    p

  let%test _ =
    let input = [ '5'; '+'; '6'; '+'; '9' ] in
    let rez = parser input in
    (* Format.printf "%a\n%!" (pp_parse_result pp_expr) rez; *)
    rez = return (Plus (Const 5, Plus (Const 6, Const 9))) []

  let parser =
    let const = digit >>= fun d -> return (Const d) in
    let rec p s =
      (const
      >>= (fun l -> char '+' *> p >>= fun r -> return (Plus (l, r)))
      <|> const)
        s
    in
    p
end

(* ********** Parsing of arithmetic BAD ******************************** *)
module Arithmetic2 = struct
  type expr = Const of int | Plus of expr * expr

  (* <expr> -- это <expr> + <digit>  или <digit>
     Левая рекурсия стреляет в ногу
  *)
  let parser =
    let const = digit >>= fun d -> return (Const d) in
    let rec p s =
      ( p >>= fun l ->
        char '+' >>= fun _ ->
        const >>= fun r -> return (Plus (l, r)) <|> const )
        s
    in
    p

  let%test _ =
    try
      let (_ : bool) =
        parser [ '1'; '+'; '2' ] = return (Plus (Const 1, Const 2)) []
      in
      false
    with Stack_overflow -> true
end

(* ********** Parsing of arithmetic GOOD ******************************* *)
(* let ints_list : _ parser =
     digit >>= fun h ->
     many (satisfy (Char.equal '+') *> digit) >>= fun tl -> return (h :: tl)

   let%test _ = ints_list [ '1'; '+'; '2'; '+'; '3' ] = return [ 1; 2; 3 ] []

   let%test _ =
     ints_list [ '1'; '+'; '2'; '+'; '+'; '3' ] = return [ 1; 2 ] [ '+'; '+'; '3' ]

   let ints_sum =
     let next = satisfy (Char.equal '+') *> digit in
     let rec helper acc s =
       match next s with
       | Failed -> return acc s
       | Parsed (n, tl) -> helper (acc + n) tl
     in
     digit >>= helper

   let%test _ = ints_sum [ '1'; '+'; '2'; '+'; '9' ] = return 12 []

   let%test _ =
     ints_sum [ '1'; '+'; '2'; '+'; '+'; '9' ] = return 3 [ '+'; '+'; '9' ] *)

(* ************ Parsing with parenthesis *********************************** *)

module Arithmetic3 = struct
  type expr = Const of int | Plus of expr * expr [@@deriving show]

  (* <expr> -- это
      либо (<expr>)
      либо <digit> и n>=0 раз + <expr>
      либо <digit>
  *)

  let choice xs = List.fold_left ( <|> ) (fun _ -> Failed) xs
  let parens p = char '(' *> p <* char ')'

  let parser =
    let const = digit >>= fun d -> return (Const d) in
    let rec p s =
      choice
        [
          parens p;
          ( const >>= fun h ->
            many (char '+' *> p) >>= fun tl ->
            return (List.fold_left (fun acc r -> Plus (acc, r)) h tl) );
        ]
        s
    in
    p

  let%test _ =
    let input = [ '('; '5'; '+'; '6'; '+'; '9'; ')' ] in
    let rez = parser input in
    (* Format.printf "%a\n%!" (pp_parse_result pp_expr) rez; *)
    rez = return (Plus (Const 5, Plus (Const 6, Const 9))) []

  let%test _ =
    let input = [ '('; '5'; '+'; '('; '6'; '+'; '9'; ')'; ')' ] in
    let rez = parser input in
    (* Format.printf "%a\n%!" (pp_parse_result pp_expr) rez; *)
    rez = return (Plus (Const 5, Plus (Const 6, Const 9))) []
end

module Arithmetic4 = struct
  type expr = Const of int | Plus of expr * expr | Asterisk of expr * expr
  [@@deriving show]

  (* <expr> -- это неформально (!!)
      либо (<expr>)
      либо <expr> + <expr>
      либо <expr> * <expr>
      либо <digit>
  *)

  let choice xs = List.fold_left ( <|> ) (fun _ -> Failed) xs

  let parens p =
    char '(' >>= fun _ ->
    p >>= fun x ->
    char ')' >>= fun _ -> return x

  let parser =
    let const = digit >>= fun d -> return (Const d) in
    let rec product s =
      choice
        [
          parens sum;
          ( const >>= fun h ->
            many (char '*' >>= fun _ -> product) >>= fun tl ->
            return (List.fold_left (fun acc r -> Asterisk (acc, r)) h tl) );
        ]
        s
    and sum s =
      choice
        [
          parens sum;
          ( product >>= fun h ->
            many (char '+' >>= fun _ -> product) >>= fun tl ->
            return (List.fold_left (fun acc r -> Plus (acc, r)) h tl) );
        ]
        s
    in
    sum

  let%test _ =
    let input = [ '5'; '+'; '6'; '*'; '9' ] in
    let rez = parser input in
    rez = return (Plus (Const 5, Asterisk (Const 6, Const 9))) []

  let%test _ =
    let input = [ '5'; '*'; '6'; '+'; '9' ] in
    let rez = parser input in
    rez = return (Plus (Asterisk (Const 5, Const 6), Const 9)) []
end

module _ (Parser : sig
  type 'a parse_result

  (* type 'a t *)
  type 'a t = char list -> 'a parse_result

  val char : char -> char t
  val digit : int t
  val ( <|> ) : 'a t -> 'a t -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
  val return : 'a -> 'a t
  val many : 'a t -> 'a list t
  (* val fail : string -> 'a t *)
end) =
struct
  open Parser

  type expr = Const of int | Plus of expr * expr | Asterisk of expr * expr
  [@@deriving show]

  (* <expr> -- это неформально (!!)
      либо (<expr>)
      либо <expr> + <expr>
      либо <expr> * <expr>
      либо <digit>
  *)

  let choice2 = ( <|> )

  let parens p =
    char '(' >>= fun _ ->
    p >>= fun x ->
    char ')' >>= fun _ -> return x

  let parser : expr t =
    let const = digit >>= fun d -> return (Const d) in
    let rec product s =
      choice2 (parens sum)
        ( const >>= fun h ->
          many (char '*' >>= fun _ -> product) >>= fun tl ->
          return (List.fold_left (fun acc r -> Asterisk (acc, r)) h tl) )
        s
    and sum s =
      choice2 (parens sum)
        ( product >>= fun h ->
          many (char '+' >>= fun _ -> product) >>= fun tl ->
          return (List.fold_left (fun acc r -> Plus (acc, r)) h tl) )
        s
    in
    sum

  let%test _ =
    let input = [ '5'; '+'; '6'; '*'; '9' ] in
    let rez = parser input in
    rez = return (Plus (Const 5, Asterisk (Const 6, Const 9))) []

  let%test _ =
    let input = [ '5'; '*'; '6'; '+'; '9' ] in
    let rez = parser input in
    rez = return (Plus (Asterisk (Const 5, Const 6), Const 9)) []
end

(* ********************************** The End ********************************* *)

(* Бывают разные варианты как объявить input
   - char list
   - int * string
   - int * char Seq.t
   - с поддержкой юникода
   - графы

   Результат парсинга тоже бывает разный. Например, можно добавить конструктор NeedMoreInput.

   Или можно возвращать пустой список, если не удалось распарсить, или несколько ответов, если
   можно распарсить более чем 1м способом

     type 'a parse_result = ('a * input) list
*)

let rec take_while : (char -> bool) -> unit parser =
 fun f input ->
  match input with
  | h :: tl when f h -> take_while f tl
  | _ -> Parsed ((), input)

let ws = take_while (function ' ' | '\t' | '\n' | '\r' -> true | _ -> false)

let parse_string p str =
  let input = List.init (String.length str) (fun n -> str.[n]) in
  match p input with
  | Failed -> Result.error ""
  | Parsed (_, _ :: _) -> Result.error ": end_of_input "
  | Parsed (x, []) -> Result.ok x

let test parser pp input =
  let rez = parse_string (parser <* ws) input in
  match rez with
  | Result.Ok v -> Format.printf "%a\n%!" pp v
  | Result.Error e -> Format.printf "Error: '%s'\n" e

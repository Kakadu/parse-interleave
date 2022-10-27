(* Parsers with interleaving *)

module LL = struct
  type 'a t = 'a Zlist.t

  let nil : 'a t = lazy Zlist.Nil
  let return : 'a. 'a -> 'a t = fun x -> lazy (Zlist.Cons (x, nil))
  let map = Zlist.map
  let fold_left = Zlist.fold_left
  let hd = Zlist.head
  let tl = Zlist.tail
  let concat = Zlist.concat
  let cons : 'a. 'a -> 'a t -> 'a t = fun h tl -> lazy (Zlist.Cons (h, tl))
  let snoc : 'a. 'a -> 'a t -> 'a t = fun h tl -> concat tl (return h)

  let take : int -> 'a t -> 'a list =
   fun n xs ->
    let rec helper acc n = function
      | (lazy Zlist.Nil) -> List.rev acc
      | _ when n <= 0 -> List.rev acc
      | (lazy (Zlist.Cons (h, tl))) -> helper (h :: acc) (n - 1) tl
    in
    helper [] n xs

  let disj =
    let rec helper l r =
      match l with
      | (lazy Zlist.Nil) -> r
      | (lazy (Zlist.Cons (h, tl))) -> cons h (helper r tl)
    in
    helper

  let interleave = disj

  let rec bind : 'a 'b. 'a t -> ('a -> 'b t) -> 'b t =
   fun x f ->
    match hd x with
    | None -> nil
    | Some h -> ( match Zlist.tail x with tl -> disj (f h) (bind tl f))

  let ( >>= ) = bind
end

type input = char list

type 'a parse_result =
  | Parsed of ('a * input) LL.t
  | Delay of 'a parse_result Lazy.t

type 'a parser = input -> 'a parse_result

let pp_parse_result f ppf = function
  | Parsed xs when Zlist.head xs = None -> Format.fprintf ppf "Failed"
  | Parsed ps ->
      Format.fprintf ppf "@[Parsed @[";
      Zlist.iter (fun (r, _) -> Format.fprintf ppf "@[%a@]" f r) ps;
      Format.fprintf ppf "@]@]"
  | Delay _ -> Format.fprintf ppf "Delay"

let rec is_result_fail = function
  | Delay d -> is_result_fail (Lazy.force d)
  | Parsed zs when Zlist.head zs = None -> true
  | _ -> false

(* ***************** Простой парсер 1 ********************* *)
let fail _ = Parsed LL.nil
let return x : _ parser = fun s -> Parsed (LL.return (x, s))

let ( >>| ) : 'a 'b. 'a parser -> ('a -> 'b) -> 'b parser =
 fun x f s ->
  let rec helper = function
    | Parsed zs -> Parsed (LL.map (fun (x, tl) -> (f x, tl)) zs)
    | Delay foo -> Delay (lazy (helper (Lazy.force foo)))
  in
  helper (x s)

let rec ( ++ ) l r =
  match (l, r) with
  | Parsed xs, Parsed ys -> Parsed (LL.interleave xs ys)
  | Delay (lazy l), r -> r ++ l
  | l, Delay (lazy r) -> l ++ r

let ( >>= ) : 'a 'b. 'a parser -> ('a -> 'b parser) -> 'b parser =
 fun p f s ->
  let on_parsed zs =
    let (zs : _ parse_result LL.t) =
      LL.map
        (fun (h, tl) ->
          let rez = f h tl in
          rez)
        zs
    in

    LL.fold_left ( ++ ) (Parsed (lazy Zlist.Nil)) zs
  in
  match p s with
  | Parsed zs -> on_parsed zs
  | Delay foo ->
      let rec helper p =
        match Lazy.force p with
        | Delay q -> Delay (lazy (helper q))
        | Parsed zs -> on_parsed zs
      in
      helper foo

let take_results : int -> _ parse_result LL.t -> _ list =
  let rec join : 'a. 'a parse_result LL.t -> 'a LL.t = function
    | (lazy (Zlist.Cons (Delay d, tl))) -> join (LL.snoc (Lazy.force d) tl)
    | (lazy (Cons (Parsed xs, tl))) -> LL.concat (join tl) (LL.map fst xs)
    | (lazy Nil) -> LL.nil
  in

  fun n xs -> LL.take n (join xs)

let char c : _ parser = function
  | h :: tl when c = h -> return c tl
  | _ -> fail ""

let%test _ = char 'a' [ 'a'; 'b' ] = return 'a' [ 'b' ]
let%test _ = char 'b' [ 'a'; 'b' ] = fail ""

let satisfy cond : _ parser = function
  | h :: tl when cond h -> return h tl
  | _ -> fail "satisfy"

let char c = satisfy (Char.equal c)

let digit_c =
  let is_digit ch =
    let c = Char.code ch in
    Char.code '0' <= c && c <= Char.code '9'
  in
  satisfy is_digit

let%test _ = digit_c [ '0' ] = return '0' []
let%test _ = is_result_fail (digit_c [ 'a' ])

(* ****************** Простой парсер 2 ********************************** *)

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

let ( <*> ) : 'a 'b. ('a -> 'b) parser -> 'a parser -> 'b parser =
 fun pf parg input ->
  let rec helper rez1 =
    match rez1 with
    | Delay d -> Delay (lazy (helper (Lazy.force d)))
    | Parsed fs ->
        let rezs =
          Zlist.map
            (fun (f, tl) ->
              let rec helper2 = function
                | Delay d -> Delay (lazy (helper2 (Lazy.force d)))
                | Parsed arg_rezs ->
                    Parsed (Zlist.map (fun (arg, tl) -> (f arg, tl)) arg_rezs)
              in
              helper2 (parg tl))
            fs
        in
        Zlist.fold_left ( ++ ) (Parsed (lazy Zlist.Nil)) rezs
  in

  helper (pf input)

let ( let* ) = ( >>= )
let ( let+ ) = ( >>| )
(*
(* TODO: later *)
let ( and+ ) : 'a 'b. 'a parser -> 'b parser -> ('a * 'b) parser =
 fun f1 f2 input ->
  let rec helper1 = function
    | Delay d -> Delay (lazy (helper1 (Lazy.force d)))
    | Failed -> Failed
    | Parsed (l, tl) ->
        let rec helper2 = function
          | Delay d -> Delay (lazy (helper2 (Lazy.force d)))
          | Failed -> Failed
          | Parsed (r, rest) -> Parsed ((l, r), rest)
        in

        helper2 (f2 tl)
  in

  helper1 (f1 input)
*)
(* *************************************************************** *)

let option : 'a. 'a parser -> 'a -> 'a parser =
 fun p default s ->
  match p s with
  | Delay d -> Delay (lazy (Lazy.force d))
  | Parsed zs when None = Zlist.head zs ->
      Parsed (lazy Zlist.(Cons ((default, s), lazy Nil)))
  | Parsed _ as r -> r

let rec many : 'a. 'a parser -> 'a list parser =
 fun p ->
  let* h = option (p >>| Option.some) None in
  match h with
  | None -> return []
  | Some h -> fun s -> Delay (lazy ((many p >>= fun tl -> return (h :: tl)) s))

let%test _ =
  let p = many (char 'a') in
  let input = [ 'b'; 'a'; 'b' ] in
  Parsed ([], input) = p input

let%test _ =
  let p = many (char 'b') in
  match force_result (p [ 'b'; 'b'; 'a' ]) with
  | Parsed ([ 'b'; 'b' ], [ 'a' ]) -> true
  | _ -> false

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
let ( <|> ) : ?pp:_ -> 'a parser -> 'a parser -> 'a parser =
 fun ?pp p1 p2 s ->
  let rec helper l r =
    match (l, r) with
    | Failed, r -> r
    | Delay d, r -> helper r (Lazy.force d)
    | (Parsed _ as x), _ ->
        Format.printf "Disjunction finished. %S\n%!"
          (match pp with Some pp -> Format.asprintf "%a" pp x | None -> "");
        x
  in
  helper (Delay (lazy (p1 s))) (Delay (lazy (p2 s)))

let a_or_b = char 'a' <|> char 'b'

let%test _ = a_or_b [ 'a' ] = return 'a' []
let%test _ = a_or_b [ 'b' ] = return 'b' []
let%test _ = a_or_b [ 'c' ] = Failed

let choice = function [] -> fail | h :: tl -> List.fold_left ( <|> ) h tl
let rec fix p s = p (fix p) s

let%test "left recursion 1" =
  let p =
    fix (fun self ->
        ( <|> )
          ~pp:(pp_parse_result (Format.pp_print_list Format.pp_print_int))
          (return (fun xs x -> xs @ [ x ])
          <*> (fun s -> Delay (lazy (self s)))
          <*> char '+' *> digit)
          ( digit >>| fun x ->
            Format.printf "Char %d parsed\n%!" x;
            [ x ] ))
  in
  match force_result (p [ '1'; '+'; '2'; '+'; '3' ]) with
  | Parsed ([ 1; 2; 3 ], []) -> true
  | _ -> false

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
  let rec helper = function
    | Failed -> Result.error ""
    | Parsed (_, _ :: _) -> Result.error ": end_of_input "
    | Parsed (x, []) -> Result.ok x
    | Delay d -> helper (Lazy.force d)
  in
  helper (p input)

let test parser pp input =
  let rez = parse_string (parser <* ws) input in
  match rez with
  | Result.Ok v -> Format.printf "%a\n%!" pp v
  | Result.Error e -> Format.printf "Error: '%s'\n" e

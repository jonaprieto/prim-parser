open Angstrom

let data_dir = "/Users/jonaprieto/research/prim-parser/bench-data/"

let is_digit c = c >= '0' && c <= '9'
let is_alnum c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || is_digit c
let is_ws c = c = ' ' || c = '\n' || c = '\t' || c = '\r'

let nat = take_while1 is_digit >>| int_of_string
let ws = skip_while is_ws

(* integers: sum of comma-separated nats *)
let p_ints = sep_by1 (char ',') nat >>| List.fold_left ( + ) 0

(* sexp: atom count.  atom | '(' ws S (ws S)* ws ')' *)
let p_sexp =
  fix (fun s ->
    (take_while1 is_alnum *> return 1)
    <|> (char '(' *> ws *> s >>= fun first ->
         many (ws *> s) >>= fun rest ->
         ws *> char ')' *> return (first + List.fold_left ( + ) 0 rest)))

(* csv: total cell count *)
let p_row = sep_by1 (char ',') nat >>| List.length
let p_csv = sep_by1 (char '\n') p_row >>| List.fold_left ( + ) 0

(* json: flat [nat,nat,...] -> 1 *)
let p_json =
  char '[' *> ws *> sep_by (char ',' *> ws) nat *> ws *> char ']' *> return 1

(* lambda: node count in `\v. body | v` *)
let p_lam =
  fix (fun l ->
    (char '\\' *> ws *> take_while1 is_alnum *> ws *> char '.' *> ws *> l
       >>| fun n -> n + 1)
    <|> (take_while1 is_alnum *> ws *> return 1))

(* words: count space-separated alnum tokens *)
let p_words =
  take_while1 is_alnum *> many (char ' ' *> take_while1 is_alnum)
    >>| fun xs -> 1 + List.length xs

(* brackets: nesting depth of `nat | '[' B ']'` *)
let p_br =
  fix (fun b ->
    (nat *> return 0) <|> (char '[' *> b <* char ']' >>| fun d -> d + 1))

(* netstring: LEN:DATA, — needs monadic bind (DATA length depends on parsed LEN) *)
let p_net =
  let one = nat >>= fun n -> char ':' *> take n *> char ',' *> return 1 in
  many1 one >>| List.fold_left ( + ) 0

(* full RFC-JSON: node count. dispatch number|string|keyword|array|object *)
let is_num_ch c = is_digit c || c = '-' || c = '+' || c = '.' || c = 'e' || c = 'E'
let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
let p_jsonv =
  fix (fun v ->
    let jnum = take_while1 is_num_ch *> return 1 in
    let jstr = char '"' *> skip_while (fun c -> c <> '"') *> char '"' *> return 1 in
    let jkw  = take_while1 is_alpha *> return 1 in
    let jarr = char '[' *> ws *> (sep_by (char ',') v >>| fun xs -> 1 + List.fold_left ( + ) 0 xs)
               <* ws <* char ']' in
    let pair = ws *> char '"' *> skip_while (fun c -> c <> '"') *> char '"' *> ws *> char ':' *> v in
    let jobj = char '{' *> ws *> (sep_by (char ',') pair >>| fun xs -> 1 + List.fold_left ( + ) 0 xs)
               <* ws <* char '}' in
    ws *> (jnum <|> jstr <|> jkw <|> jarr <|> jobj))

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic; s

let run p input =
  match parse_string ~consume:Consume.All p input with Ok v -> v | Error _ -> -1

let bench name p =
  let input = read_file (data_dir ^ name ^ ".txt") in
  let v = run p input in
  if v < 0 then Printf.printf "  %-8s: PARSE FAIL\n%!" name
  else begin
    let inner = 20 and reps = 50 in
    let best = ref infinity in
    for _ = 1 to reps do
      let t0 = Unix.gettimeofday () in
      for _ = 1 to inner do ignore (Sys.opaque_identity (run p input)) done;
      let t1 = Unix.gettimeofday () in
      let dt = (t1 -. t0) *. 1000. /. float_of_int inner in
      if dt < !best then best := dt
    done;
    Printf.printf "  %-8s: %.3f ms (chk %d)\n%!" name !best v
  end

let () =
  print_endline "angstrom (OCaml ocamlopt), same input files:";
  bench "integers" p_ints;
  bench "sexp"     p_sexp;
  bench "csv"      p_csv;
  bench "json"     p_json;
  bench "lambda"   p_lam;
  bench "words"    p_words;
  bench "brackets" p_br;
  bench "net"      p_net;
  (* industrial: real 2.3MB canada.json *)
  let p_json = p_jsonv <* ws in
  let input = read_file (data_dir ^ "canada.json") in
  (match parse_string ~consume:Consume.Prefix p_jsonv input with
   | Ok n -> Printf.printf "  [prefix-parse ok, nodes %d]\n%!" n
   | Error e -> Printf.printf "  [prefix FAIL: %s]\n%!" e);
  let v = run p_json input in
  let best = ref infinity in
  for _ = 1 to 20 do
    let t0 = Unix.gettimeofday () in
    for _ = 1 to 3 do ignore (Sys.opaque_identity (run p_json input)) done;
    let t1 = Unix.gettimeofday () in
    let dt = (t1 -. t0) *. 1000. /. 3. in
    if dt < !best then best := dt
  done;
  Printf.printf "  canada.json: %.3f ms (nodes %d)\n%!" !best v

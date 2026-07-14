open Angstrom
let is_digit c = c>='0'&&c<='9'
let is_num_ch c = is_digit c || c='-'||c='+'||c='.'||c='e'||c='E'
let is_alpha c = (c>='a'&&c<='z')||(c>='A'&&c<='Z')
let ws = skip_while (fun c -> c=' '||c='\n'||c='\t'||c='\r')
let p = fix (fun v ->
  let jnum = take_while1 is_num_ch *> return 1 in
  let jstr = char '"' *> skip_while (fun c -> c<>'"') *> char '"' *> return 1 in
  let jkw = take_while1 is_alpha *> return 1 in
  let jarr = char '[' *> ws *> (sep_by (char ',') v >>| fun xs -> 1 + List.fold_left (+) 0 xs) <* ws <* char ']' in
  let pr = ws *> char '"' *> skip_while (fun c -> c<>'"') *> char '"' *> ws *> char ':' *> v in
  let jobj = char '{' *> ws *> (sep_by (char ',') pr >>| fun xs -> 1 + List.fold_left (+) 0 xs) <* ws <* char '}' in
  ws *> (jnum <|> jstr <|> jkw <|> jarr <|> jobj))
let () =
  let ic = open_in_bin "bench-data/canada.json" in
  let n = in_channel_length ic in let s = really_input_string ic n in close_in ic;
  match parse_string ~consume:Consume.Prefix p s with
  | Ok v -> Printf.printf "%d\n" v | Error _ -> print_endline "-1"

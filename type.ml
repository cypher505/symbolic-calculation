type tname = string
type tenv = (tname * float) list

(* ============================================================== *)
(*                           analyse lexical                      *)
(* ============================================================== *)

type token = 
| INT of int  (* entier littéral *)
| NAME of string (* un nom, par exemple: 
                    +, pi, x, yy, z_43, cos, tan, pow
                    etc. *)
| OPEN  (* parenthèse ouvrante *)
| CLOSE (* parenthèse fermante *)

let lexer (s:string) : token list =
  let rec aux acc i = 
    if i < String.length s then
    (match s.[i] with
    | '(' -> aux (OPEN::acc) (i+1)
    | ')' -> aux (CLOSE::acc) (i+1)
    | ' ' | '\t' | '\n' -> aux acc (i+1)
    | _ -> let x,j = 
             let rec loop j = 
               if j >= String.length s then String.sub s i (j-i),(j+1) else
               match s.[j] with
               | '(' | ')' | ' ' | '\t' | '\n' -> String.sub s i (j-i),j
               | _ -> loop (j+1)
             in loop i
           in
           let token = (match int_of_string_opt x with
                        | None -> NAME x
                        | Some n -> INT n)
           in
             aux (token::acc) j)
    else acc
  in List.rev (aux [] 0)

(* ============================================================== *)
(* Pour tester soi même, automatiquement, les fonctions           *)
(*  [eval], [derive] et [simpl] définies dans la suite du projet. *)
(* ============================================================== *)

type assertion = 
| Eval of tenv * string * float
| Derive of tname * string * string
| Simpl of string * string

(* [assert_eval env s v] vérifie que [eval env (of_string s) = v].
   [assert_derive x s s'] vérifie que [derive x (of_string s) = (of_string s')].
   [assert_derive s s'] vérifie que [simpl (of_string s) = (of_string s')].
 *)

let assert_eval (env:tenv) (s:string) (v:float) : assertion =
  Eval (env,s,v)

let assert_derive (x:tname) (s:string) (s':string) : assertion =
  Derive(x,s,s')

let assert_simpl (s:string) (s':string) : assertion =
  Simpl(s,s')
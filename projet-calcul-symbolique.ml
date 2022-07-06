(* ============================================================== *)
(*              définition du type des expressions                *)
(* ============================================================== *)

type exp = 
  |VAR of string 
  |N of int
  |MONOP of string * exp 
  |BINOP of string * exp * exp;;
  
let integer (n:int) : exp = N (n);;

let name (x:tname) : exp = VAR (x) ;;

let rec apply (op:tname) (args:exp list) =
  match op,args with 
  | str,[] -> N(0) 
  | str,[x1;x2] -> BINOP(str,x1,x2)
  | str,[e1] -> MONOP(str,e1) 
  | str,x1::l -> BINOP(str,x1,apply op l)

(* ============================================================== *)
(*                           analyse syntaxique                   *)
(* ============================================================== *)

let of_string (s : string) : 'a =
  (* analyse syntaxique d'une suite de lexèmes (tokens)
     implémentant la grammaire suivante où ε désigne une suite vide :

      r ::= ε
         | ) r
         | ( x r
         | n r
         | x r

Cette analyse permet de reconnaître des expressions 
  pré-fixées telle (+ (/ x (- 2)) 3).
  *)
  let rec parse tokens =
    match tokens with
    | [] -> 
      (* s'il n'y a plus rien à analyser, l'expression à été reconnue *)
        None,[]
    | INT n :: r ->
        (* si le premier lexème (token) rencontré est un entier littéral,
           alors on transforme cet entier en une expression (de type exp)
           pui on la renvoie ainsi que le reste [r] de la séquence de lexèmes 
           à analyser. *)
        Some(integer n),r
    | NAME x :: r ->
        (* si le premier lexème (token) rencontré est un nom (par exemple "+" 
           ou "y") alors on transforme ce nom en une expression (de type exp)
           puis on la renvoie ainsi que le reste [r] de la séquence de lexèmes 
           à analyser. *)
        Some(name x),r
    | CLOSE::r ->
      (* si on rencontre une parenthèse fermante, 
         la sous-expression à analyser se termine (None)
         et il reste à analyser le reste [r] de la séquence de lexèmes 
         à analyser. *)
        None,r
    | OPEN :: NAME op :: r -> 
      (* si on rencontre une parenthèse ouvrante suivie d'un nom,
         alors on est en train d'analyser une sous-expression
         de la forme (op e1 e2 ... en). On analyse donc le reste
         "e1 e2 ... en)" *)
        let rec parse_list acc tokens =
        (* Pour analyser les expressions arguments e1 e2 ... en,
           on utilise ici une récursion terminale avec un accumulateur
           (construisant une liste en ordre inverse) puis on inverse 
           l'ordre des éléments de cette liste avec [List.rev].
           On renvoie cette liste avec le reste [r] de la séquence 
           de lexèmes à analyser. *)
          match parse tokens with
          | None,r -> List.rev acc,r
          | Some e,r -> parse_list (e::acc) r 
        in            
        let es,r' = parse_list [] r in
        Some(apply op es),r'
  in

  (* on utilise ici [lexer s] pour obtenir une suite de lexèmes à partir 
     d'une chaîne de caractères [s] représantant une expression bien formée,
     puis la fonction [parse] analyse cette suite pour reconnaître cette suite
     de lexème et ainsi construire l'arbre de syntaxe abstraite de l'expression. 
  *)
  match parse (lexer s) with
  | Some e,[] -> e
  | _,_::_ -> failwith ("syntax error: "^s)

(* ============================================================== *)
(*                  évaluation des expressions                    *)
(* ============================================================== *)

let rec trouve_val l s = if s = "pi" then Float.pi else match l with
    |[] -> failwith "trouve_val not found"
           
    |(n,v)::xs -> if n = s then v else trouve_val xs s ;;

let rec eval (env:tenv) (e:exp) : float = 
  match e with 
  |VAR(x) -> trouve_val env x
  |N(x) -> float_of_int x
  |MONOP(str,e) -> (match str,e with 
      |"-",e -> 0.-.( eval env e)
      |"+",e -> 0.+.( eval env e)
      |"*",e -> 1.*.( eval env e)
      |"/",e -> 1./.( eval env e)
      |"sin",e -> sin ( eval env e)
      |"cos",e ->  cos ( eval env e)
      |"tan",e -> tan ( eval env e)
      |"sqrt",e -> Float.sqrt ( eval env e)
      |"e",e -> Float.exp ( eval env e)
      |"ln",e -> Float.log10 ( eval env e)
      | _ -> failwith ("operation not found"^str))
  |BINOP(s,e1,e2) ->  (
      match s with 
      |"+" -> (eval env e1)+.(eval env e2)
      |"-" -> (eval env e1)-.(eval env e2)
      |"*" -> (eval env e1)*.(eval env e2)
      |"/" -> (eval env e1)/.(eval env e2)
      |"pow" -> (eval env e1)**(eval env e2)
      |_ -> failwith ("expression not recognized"^s) )
    
              
              

(* ============================================================== *)
(*             dérivation symbolique des expressions              *)
(* ============================================================== *)

let rec derive (x:tname) (e:exp) : exp =match e with 
  |N(a) -> N(0)
  |VAR(a) -> if (a = x) then N(1) else N(0) 
  |MONOP(str,e1) ->
      (match str with 
       |"-" -> MONOP("-",(derive x e1))
       |"sin" -> BINOP("*",(derive x e1),MONOP("cos",e1))
       |"cos" -> MONOP("-",BINOP("*",(derive x e1),MONOP("sin",e1)))
       |"tan" -> BINOP("*",(derive x e1),BINOP("+",N(1),BINOP("pow",MONOP("tan",e1),N(2))))
       |_ -> failwith ("DERIVE MONO"))
  |BINOP(str,e1,e2) -> (match str with
      |"+" -> BINOP("+",(derive x e1),(derive x e2))
      |"-" -> BINOP("-",(derive x e1),(derive x e2))
      |"*" -> BINOP("+",BINOP("*", (derive x e1),e2),BINOP("*", (derive x e2),e1))
      |"/" -> BINOP("/",BINOP("-",BINOP("*",(derive x e1),e2),BINOP("*",(derive x e2),e1)),BINOP("pow",e2,N(2))) 
      |"pow" -> let N(a)=e2 in  BINOP("*",BINOP("*",e2,(derive x e1)),BINOP("pow",e1,N(a-1))) 
      |_-> failwith ("DERIVE") ) ;;

(*eval [("x",0.);("z", 3.)] ( derive ("x") (BINOP("*",VAR("x"),VAR("z"))) );;*)
(* ============================================================== *)
(*                   affichage des expressions                    *)
(* ============================================================== *)
let rec comp e1 e2 =
  match e1,e2 with 
  |N(a),N(b) -> a=b
  |VAR(a),VAR(b) -> String.equal a b = true
  |MONOP(str1,t1),MONOP(str2,t2) -> (String.equal str1 str2)&& (comp t1 t2)
  |BINOP(str1,t1,t2),BINOP(str2,tt1,tt2) -> (String.equal str1 str2)&&( (comp t1 tt1))&&(comp t2 tt2)
  |_-> false;;

let rec to_string (e:exp) : string = 
  match e with 
  |N(a) -> string_of_int a 
  |VAR(a) -> a 
  |MONOP(str,e1) -> "("^str^" "^(to_string e1)^")"
  |BINOP(str,e1,e2) -> "("^str^" "^(to_string e1)^" "^(to_string e2)^")";;


let rec pgcd n m = 
  if n > m then pgcd m n
  else if n = 0 then m
  else let r = m mod n in
    pgcd r n;;
(* ============================================================== *)
(*       simplification et factorisation des expressions          *)
(* ============================================================== *)

let rec simpl (e:exp) : exp = 
  match  e with 
  |N(a) -> N(a)
  |VAR(x) -> VAR(x)
  |MONOP(str, e1)-> (let e1=simpl e1 in match str with  
    |"cos" ->  (match e1 with 
        |VAR("pi") -> N(-1)
        |N(0)->N(1)
        |BINOP("*",N(a),VAR("pi"))-> N(int_of_float((-1.)**float_of_int(a)))
        |_->(MONOP("cos",simpl e1))  
      ) 
    |"sin" -> (match e1 with 
        |VAR("pi") -> N(0)
        |N(0)->N(0)
        |BINOP("*",N(a),VAR("pi"))-> N(0)
        |_->(MONOP("sin",simpl e1)) 
      ) 
    |"ln" -> (match e1 with 
        | N(1) -> N(0)
        | _ -> MONOP("ln",simpl e1))
    |"e" -> (match e1 with 
        |N(0) -> N(1)
        | _ -> MONOP("e",simpl e1))
    |"sqrt" -> (match e1 with 
        | N(1) -> N(1) 
        | _ -> MONOP("sqrt", e1))
    |"tan" -> MONOP("tan", e1) 
    |"-"->    
        (match (simpl e1) with 
         |N(a)-> N(-1*a) 
         |MONOP("-",e2) ->  
             (match simpl e2 with 
              |MONOP("-",t1) -> simpl t1 
              |BINOP("-",t1,t2) ->  (BINOP("-",simpl t2,simpl t1) )
              |BINOP("*",N(b),t1) -> ( BINOP("*",N(-1*b),simpl t1))
              |BINOP("*",t1,N(b)) -> ( BINOP("*",N(-1*b),simpl t1)) 
              |t1-> MONOP("-", t1) 
             )
             
         |_-> failwith "simpl MONOP2")
    |_-> failwith ("simpl MONOP3"^str)) 
  |BINOP(str,e1,e2) -> 
      (match str with 
       |"+" -> (match simpl e1,simpl e2 with 
           |MONOP("ln",a),MONOP("ln",b) -> MONOP("ln", BINOP("*",a,b))
           |N(0),t1 -> simpl t1
           |t1,N(0) -> simpl t1
           |N(a),N(b) -> N(a+b) 
           |BINOP("*",N(n),t1),N(m) -> 
               let k= pgcd (abs n) (abs m) in if k>1 then BINOP("*",N(k),BINOP("+",BINOP("*",N(n/k),e1),N(m/k)))
               else t1 
           |N(a),t1 ->  (BINOP("+",simpl t1,N(a))) 
           |t1,N(a) ->  (BINOP("+",simpl t1,N(a)))
           |t1,t2 ->if comp t1 t2 = true then  BINOP("*",N(2),simpl t2) else BINOP("+",t1,t2)
           |_->failwith "simpl ADITION" 
         ) 
                           

                           
          
       
       |"-" -> (match simpl e1,simpl e2 with 
           |MONOP("ln",a),MONOP("ln",b) -> MONOP("ln", BINOP("/", a,b))
           |N(0),t1 ->  (MONOP("-",t1))
           |t1,N(0) ->  t1
           |N(a),N(b) -> N(a-b) 
           |BINOP("*",N(n), e),N(a) ->  let k = pgcd (abs n) (abs a)  and e =(simpl e ) and t1=BINOP("*",N(n), e) in
               if k > 1 then ((BINOP("*", N(k), BINOP("-", BINOP("*", N(n/k), e),N(a/k) ))))
               else (BINOP("-", t1,N(a)))
                    
           |N(a),BINOP("*",N(n), e) ->   let k = pgcd (abs n) (abs a)and e =(simpl e ) and t1=BINOP("*",N(n), e) in 
               if k > 1 then ( (BINOP("*", N(k), BINOP("-" , BINOP("*", N(n/k), e),N(a/k)))))
               else (BINOP("-",N(a),t1))
                    
           |t1,MONOP("-",t2) ->  (BINOP("+",simpl t1,simpl t2)) 
           |t1,t2 -> if comp t1 t2 = true then  N(0) else BINOP("-",t1,t2)
           |_->failwith "simpl SUBSTRACT"
                   
                           
                           
         )
                           
                           
       
       |"*" -> (match (simpl e1),(simpl e2) with
           |MONOP("e",a),MONOP("e",b) -> MONOP("e", BINOP("+", a,b))
           |MONOP("sqrt",a),MONOP("sqrt", b) -> MONOP("sqrt", BINOP("*", a, b)) 
           |N(a),N(b) -> N(a*b) 
           |N(1),t1 -> simpl t1
           |t1,N(1) -> simpl t1
           |_,N(0) -> N(0)
           |N(0),_ -> N(0)
           |t1,BINOP("/",t2,t3) -> BINOP("/",BINOP("*",t1,t2),t3) 
           |t1,N(a) -> BINOP("*",N(a),t1)
           |N(n),BINOP("*",N(m),t1) ->   (BINOP("*",N(n*m),simpl t1)) 
           |t1,t2 -> if (comp t1 t2 )=true then   (BINOP("pow",simpl t1,N(2))) else (
               (match t1,t2 with 
                |BINOP("/", e1,e2),e3 -> BINOP("/",e2,BINOP("*",e1,e3))
                |t1,(BINOP("pow",t3,N(n)))  when ((comp t3 t1)=true) ->  (BINOP("pow",simpl t1,N(n+1)) ) 
                |t1,t2 -> BINOP("*",t1,t2)                         (*|(BINOP("pow",t3,N(n))),t2  when ((comp t3 t2)=true) ->  (BINOP("pow",simpl t2,N(n+1)) )*)
                | _-> failwith "simpl MULTIPLY"  ))                                            
  
         )
       |"/" -> (match simpl e1,simpl e2 with 
           |MONOP("e",a),MONOP("e",b) -> MONOP("e", BINOP("-", a,b));
           | MONOP("sqrt",a),MONOP("sqrt",b) -> MONOP("sqrt", BINOP("/", a, b))
           |t1,N(1) ->  t1 
           |N(0),_ -> N(0) 
           |N(a),N(b) ->  (let k = (pgcd (abs a) (abs b)) in (if k > 1 then  ( simpl (BINOP("/", N(a/k),N(b/k) )))else BINOP("/",N(a),N(b))))
           |t1,BINOP("/",t2,t3) -> BINOP("/",BINOP("*", t1,simpl t2),simpl t3)
           |BINOP("/",t1,t2),t3 -> BINOP("/",simpl t1,BINOP("*",simpl t2, t3))
           |t1,t2 -> if (comp t1 t2 )=true then N(1) else BINOP("/",t1,t2)
           |_->failwith "simpl DIVISE"
                       
           
                           
         )
       |"pow" -> (match simpl e1, simpl e2 with 
           |MONOP("ln",a),N(b) -> BINOP("*",N(b),MONOP("ln",a))
           |t1,N(1) ->  t1 
           |N(0),N(a) -> N(0)
           |N(1),N(a) -> N(1)
           |_,N(0) -> N(1) 
           |t1,t2 -> BINOP("pow",t1,t2)
           |_-> failwith "simpl pow"
                        
                        
         ) 
       |_-> failwith " simple"
         
      )            
      
(* ============================================================== *)
(*                            ajout de tests                      *)
(* ============================================================== *) 

        (*let assertions : assertion list = []*)

let assertions = 
  [ assert_eval [("x",4.)] "(+ x 1)" 5. ;
    assert_eval [("x",4.)] "(+ x 2)" 6. ;
    assert_eval [("x",4.);("y",10.)] "(* (/ y 2) (+ x 2)" 30. ;
    
    assert_derive "y" "(+ y 2)" "(+ 1 0)" ;
    assert_derive "y" "(* y 2)" " (+ (* 1 2) (* 0 y)) " ;
    
    assert_derive "y" "( tan (* y 2) )" "(* (+ (* 1 2) (* 0 y)) (+ 1 (pow (tan (* y 2)) 2)))" ;
    assert_simpl "(* (+ (* 1 2) (* 0 y)) (+ 1 (pow (tan (* y 2)) 2)))" "(* 2 (+ (pow (tan (* 2 y)) 2) 1))" ;
    
    assert_simpl "(+ x 0)" "x" ; 
    assert_simpl "(+ x (* 2 (/ 10 2)))" "(+ x 10)" ]

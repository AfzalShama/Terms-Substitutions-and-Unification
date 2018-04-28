
(* Finite symbols can also be defined *)
(* type symbol = Abs| Not | Plus | Minus | Multiply | Divide | Mod | Exponent | And | Or | Implies | Equal | Great | Less | GreatEq | LessEq | Proj ;;  *)

(* Symbol data-type is defined. It is a string *)
type symbol = string ;; 

(* Variable data-type is defined. It is alpha-numeric string *)
type variable = string ;;

(* Term data-type is defined *)
type term = V of variable | Node of symbol * (term list) ;;

type signature = (symbol * int) list ;;

(* Checks if duplicate of symbol exists in given list *)
let rec occurs (x:symbol) (l:signature) = match l with 
					  [] -> false
					| (y,n)::xs -> if (String.equal x y) then true else (occurs x xs) ;;

(* Gives arity of a symbol *)
let rec arity (x:symbol) (l:signature) = match l with
					  [] -> -1
					| ((y,n)::xs) -> if (String.equal x y) then n else arity x xs ;;

(* Given a signature as a list of (symbol,arity) pairs, checks if it is valid *)
let rec check_sig (l:signature) = match l with 
					  [] -> true 
					| ((s,n)::xs) -> if n<0 then false else (if (occurs s xs) then false else (check_sig xs)) ;;

(* Helper Function *)
let doAnd x y = x && y;;

(* Given a signature and a term, checks if the term is well-formed *)
let rec wfterm (s:signature) (t:term) = match t with
					  V(_) -> true
					| Node(sym,l) -> if (arity sym s != List.length l) then false else (List.fold_right doAnd (List.map (wfterm s) l) true) ;;

(* Helper Function *)
let greater x y = if (x>y) then x else y ;;

(* Gives Height of a Term *)
let rec height (t:term) = match t with
					  V(_) -> 0
					| Node(s,l) -> 1 + (List.fold_right greater (List.map height l) 0) ;;

(* Helper Function *)
let add x y = x + y ;;

(* Gives size i.e., number of nodes in a term*)
let rec size (t:term) = match t with
					  V(_) -> 0
					| Node(s,l) -> 1 + (List.fold_right add (List.map size l) 0) ;;

(* Helper Function *)
let rec union l1 l2 = match l1 with
					  [] -> l2
					| x::xs -> if List.mem x l2 then union xs l2 else union xs (x::l2) ;;

(* Gives set of variables of a term *)
let rec vars (t:term) = match t with
					  V(x) -> [x] 
					| Node(s,l) -> List.fold_right union (List.map vars l) [] ;;



(* SUBSTITUTIONS ****************************** *)

(* Define Substitution *)
type subs = (variable * term) list ;;

(* Substitute a variable in a term *)
let rec subst_var (z:term) (x:variable) (t:term) :term = match t with 
						  	  V y -> if String.equal x y then z else t
						  	| Node(sym,[]) -> t
							| Node(sym, l) -> Node(sym, List.map (subst_var z x) l) ;;

(* Apply substitution of all variables in a term *)
let subst (s:subs) (t:term) :term = List.fold_right (fun (x,u) -> subst_var u x) s t ;;

(* Helper Function *)
let rec present x = function
    | V y -> x = y
    | Node (_, lst) -> List.exists (present x) lst ;;


(* Composition of Substitutions *)
let composition s1 s2 =
   let rec aux s1 s2 s = match (s1,s2) with
      | ([],[])   -> s
      |    (l1, [])  -> l1 @ s
      | ([], l2)  -> l2 @ s
      | (((v1, t1) :: tl1), ((v2, t2) :: tl2)) -> if present v2 t1 then (v1, subst_var t1 v2 t2)::s else (aux tl1 tl2 ([(v1, t1)] @ [(v2, t2)] @ s)) in
       											  aux s1 s2 [];;




(* Most General Unifier **************************** *)

(* Defined an exception conveying, that mgu doesn't exist *)
exception NOT_UNIFIABLE of string ;;

(* Most general unifier for terms t1 and t2, given a substitution *)
let rec mgu_s (t1:term) (t2:term) (s:subs) :subs = if (List.length (vars t1))==0 && (List.length (vars t2))==0 then
							 						(if (t1==t2) then s else raise (NOT_UNIFIABLE "Constants mistmatch"))
							 				     else
											 		match (t1,t2) with 
														  (V x, V y) -> if (String.equal x y) then s else (x,t2)::s
														| (V x, _) -> if (List.mem x (vars t2)) then raise(NOT_UNIFIABLE "Term1 is variable of Term2")
																					   			else (x,t2)::s
														| (_, V y) -> if (List.mem y (vars t1)) then raise(NOT_UNIFIABLE "Term2 is variable of Term1")
																					   			else (y,t1)::s
														| (Node(sym1,l1), Node(sym2,l2)) -> if (String.equal sym1 sym2)==false then raise(NOT_UNIFIABLE "Symbols mismatch")
																							else if (List.length l1 != List.length l2) then raise(NOT_UNIFIABLE "Arities of Terms mismatch")
																							else 
																							unify l1 l2 s
														| _ -> raise(NOT_UNIFIABLE "Invalid expression")

and unify ls1 ls2 s2 = match ls1,ls2 with
							  ([],[]) -> s2
							| (e1::xs,e2::ys) -> let s_new = (mgu_s e1 e2 s2) in (unify (List.map (subst s_new) xs) (List.map (subst s_new) ys) s_new) ;;

(* Given two terms, outputs the mgu *)
let mgu (t1:term) (t2:term) = mgu_s t1 t2 [];;


(*


(* TESTING ****************************** *)

(* Signatures------------- *)

let sign1:signature = [("Abs",1);("Add",2);("Multiply",2);("Minus",2);("Divide",2)] ;;

(* Negative arity *)
let sign2:signature = [("Abs",1);("Add",2);("Multiply",-2);("Minus",2);("Divide",2)] ;;

(* Duplicate Symbol *)
let sign3:signature = [("Abs",1);("Add",2);("Multiply",2);("Add",2);("Divide",2)] ;;

let c1 = check_sig sign1 ;;
let c2 = check_sig sign2 ;;
let c3 = check_sig sign3 ;;


(* Terms ----------------- *)

let t1 = Node("Multiply", [Node("Add",[V("x");V("v1")]);V("z")]);;
let t2 = Node("Abs", [Node("Minus", [Node("Divide",[V("q");V("x")]);t1])]);;

(* Wrong Arity *)
let t3 = Node("Multiply", [Node("Add",[V("x")]);V("z")]);;

(* Unknown Symbol *)
let t4 = Node("Multiply", [Node("Hello",[V("x");V("y")]);V("z")]);;

let wf1 = wfterm sign1 t1 ;;
let wf2 = wfterm sign1 t2 ;;
let wf3 = wfterm sign1 t3 ;;
let wf4 = wfterm sign1 t4 ;;


(* Height, Size and Vars ------- *)
let h1 = height t1 ;;
let h2 = height t2 ;;

let s1 = size t1 ;;
let s2 = size t2 ;;

let vars1 = vars t1 ;;
let vars2 = vars t2 ;;

(* Substitutions -------- *)

let t5 = Node("Abs",[V("v6")]) ;;
let t6 = Node("Add", [V("v1");V("v2")]) ;;
let t7 = Node("Add",[V("v3");V("v4")]) ;;
let t8 = Node("Add", [V("v5");t1]) ;;

let subs1 = [("v1",t1); ("v2",t2)] ;;
let subst1 = subst subs1 t6;;

let m1 = mgu t5 t6 ;;
let m2 = mgu t6 t7 ;;
let m3 = mgu t6 t8 ;;

*)
(* 1 *)

type tvar = string;;	(* type *)
type var = string;; 	(* term *)

(* 1.1 *)

type ty =				(* simple type *)
	| Tvar of tvar
	| Imp of ty * ty
	
	| Prod of ty * ty 		(* 1.8 *)

	| T						(* 1.9 *)
	
	| Coprod of ty * ty	 	(* 1.10 *)
	
	| F;; 					(* 1.11 *)

(* 1.2 *)

type tm =				(* λ-terms à la Church *)
	| Var of var
	| App of tm * tm
	| Abs of var * ty * tm

	| Pair of tm * tm
	| Proj1 of tm
	| Proj2 of tm
	
	| Union1 of ty * tm
	| Union2 of ty * tm
	
	| Truth
	| Absurd of ty * tm
	
	| Case of tm * tm * tm;;

(* 1.3 *)

let rec string_of_ty ty = match ty with
	| Tvar x 			->	x
	| Imp (a, b)		->	"(" ^ (string_of_ty a) ^ " => " ^ (string_of_ty b) ^ ")"
	
	| Prod (a, b)		-> "("^(string_of_ty a)^"/\\"^(string_of_ty b) ^ ")"
	
	| T					-> "⊤"
	
	| Coprod (a, b)		->  "("^(string_of_ty a)^"\\/"^(string_of_ty b) ^ ")"

	| F					-> "⊥";;

let rec string_of_tm tm = match tm with
	| Var x				-> x
	| App (t, u)		-> "(" ^ (string_of_tm t) ^ " " ^ (string_of_tm u) ^ ")"
	| Abs (x, a, t)		-> "(fun (" ^ x ^ " : " ^ (string_of_ty a) ^ " -> " ^ (string_of_tm t) ^ ")"
	
	| Pair (a, b)		-> "<" ^ (string_of_tm a) ^ "," ^(string_of_tm b) ^ ">"
	| Proj1 t			-> "π₁(" ^ (string_of_tm t) ^ ")"
	| Proj2 t			-> "π₂(" ^ (string_of_tm t) ^ ")"

	| Union1 (a, t)		-> "ι₁" ^ "(" ^ (string_of_ty a) ^ ")(" ^ (string_of_tm t) ^ ")"
	| Union2 (a, t)		-> "ι₂" ^ "(" ^ (string_of_ty a) ^ ")(" ^ (string_of_tm t) ^ ")"

	| Truth				-> "<>"
	| Absurd (a, t)		-> "case_" ^ "(" ^ (string_of_ty a) ^ ")" ^ "(" ^ (string_of_tm t) ^ ")"
	
	| Case (t, u, v)	-> "case(" ^ (string_of_tm t)  ^ "," ^ (string_of_tm u)^ "," ^ (string_of_tm v) ^ ")";;

let ex1 = string_of_ty (Imp (Imp (Tvar "A", Tvar "B"),Imp (Tvar "A", Tvar "C")));;

let ex2 = string_of_tm (Abs ("f", Imp (Tvar "A", Tvar "B"),Abs ("x", Tvar "A", App (Var "f", Var "x"))));;


(* 1.4 *)

type context = (string * ty) list;;

exception Type_error;;

(* 1.6 *)

let rec infer_type ctx tm = match tm with
	| Var x				-> (try List.assoc x ctx with Not_found -> raise Type_error)
	| App (t, u) 		-> (
		match infer_type ctx t with
		| Imp (a, b) when infer_type ctx u = a	-> b
		| _										-> raise Type_error
		)
	| Abs(x, a, t)		-> Imp (a , infer_type ((x, a) :: ctx) t)
	
	| Pair (a, b)		-> Prod (infer_type ctx a, infer_type ctx b)
	| Proj1 t			-> (
		match infer_type ctx t with
		| Prod (x, _)	-> x
		| _				-> raise Type_error
		)
	| Proj2 t			-> (
		match infer_type ctx t with
		| Prod (_, x) 	-> x
		| _				-> raise Type_error
     	)

	| Truth				-> T     
	| Union1 (a, b)		-> Coprod (infer_type ctx b,a)
	| Union2 (a, b)		-> Coprod (a,infer_type ctx b)
	| Case (t, u, v)	-> (
		match infer_type ctx t with
    	| Coprod (a, b)	->
			let z = (
				match infer_type ctx u with
				| Imp (c, d) when c = a	-> d
				| _						-> raise Type_error
         	) in
        	let z1 = (
				match infer_type ctx v with
				| Imp (c, d) when c = b -> d
				| _						-> raise Type_error
        	) in
         	if z = z1 then z else raise Type_error
		| _				-> raise Type_error
		)
	| Absurd (a,t)		-> check_type ctx t F; a
and check_type ctx tm ty =
	if infer_type ctx tm = ty then () else raise Type_error;;

let ex3 = check_type [] (Abs ( "x",Tvar "A", Var "x")) (Imp(Tvar "A",Tvar "A"));;

let ex4 = check_type [] (Abs ( "x",Tvar "A", Var "x")) (Imp(Tvar "B",Tvar "B"));;

let ex5 = check_type [] (Var "x") (Tvar "A");;


(* 1.12 *)

(* Start parser.ml *)

let () = Printexc.record_backtrace true;;

exception Parse_error;;

let must_kwd s k = match Stream.next s with Genlex.Kwd k' when k' = k -> () | _ -> raise Parse_error;;

let peek_kwd s k = match Stream.peek s with
	Some (Genlex.Kwd k') when k' = k -> let _ = Stream.next s in true | _ -> false;;
	
let stream_is_empty s =
	try Stream.empty s; true with Stream.Failure -> false;;

let ident s = match Stream.next s with
	| Genlex.Ident x	-> x
	| _					-> raise Parse_error;;

let lexer = Genlex.make_lexer ["("; ")"; "=>"; "/\\"; "\\/"; "fun"; "->"; ","; ":"; "fst"; "snd"; "T"; "left"; "right"; "not"; "case"; "of"; "|"; "absurd"; "_";"nat"];;

let ty_of_tk s =
	let rec ty () = arr ()
	and arr () =
		let a = prod () in
		if peek_kwd s "=>" then Imp (a, arr ()) else a
	and prod () =
		let a = sum () in
		if peek_kwd s "/\\" then Prod (a, prod ()) else a
	and sum () =
		let a = base () in
		if peek_kwd s "\\/" then Coprod (a, sum ()) else a
	and base () =
		match Stream.next s with
		| Genlex.Ident x	-> Tvar x
		| Genlex.Kwd "("	->
			let a = ty () in must_kwd s ")"; a
		| Genlex.Kwd "T"	-> T
		| Genlex.Kwd "_" 	-> F
		| Genlex.Kwd "not"	->
			let a = base () in Imp (a, F)
		| _ 				-> raise Parse_error
	in
	ty ();;

let tm_of_tk s =
	let noapp = List.map (fun k -> Some (Genlex.Kwd k)) [")"; ","; "case"; "fun"; "of"; "->"; "|"] in
	let ty () = ty_of_tk s in
	let rec tm () = app ()
	and app () =
		let t = ref (abs ()) in
		while not (stream_is_empty s) && not (List.mem (Stream.peek s) noapp) do
			t := App (!t, abs ())
		done;
		!t
	and abs () =
		if peek_kwd s "fun" then
		(
			must_kwd s "(";
			let x = ident s in
			must_kwd s ":";
			let a = ty () in
			must_kwd s ")";
			must_kwd s "->";
			let t = tm () in
			Abs (x, a, t)
		)
		else if peek_kwd s "case" then
		(
			let t = tm () in
			must_kwd s "of";
			let _ = ident s in
			must_kwd s "->";
			let u = tm () in
			must_kwd s "|";
			let _ = ident s in
			must_kwd s "->";
			let v = tm () in
			Case (t, u, v)
		)
		else
			base ()
	and base () = match Stream.next s with
		| Genlex.Ident x 		-> Var x
		| Genlex.Kwd "(" 		->
			if peek_kwd s ")" then Truth
			else
				let t = tm () in
				if peek_kwd s "," then
					let u = tm () in
					must_kwd s ")";
					Pair (t, u)
				else
					(
					must_kwd s ")";
					t
					)
		| Genlex.Kwd "fst" 		->
			must_kwd s "(";
			let t = tm () in
			must_kwd s ")";
			Proj1 t
		| Genlex.Kwd "snd" 		->
			must_kwd s "(";
			let t = tm () in
			must_kwd s ")";
			Proj2 t
		| Genlex.Kwd "left" 	->
			must_kwd s "(";
			let t = tm () in
			must_kwd s ",";
			let b = ty () in
			must_kwd s ")";
			Union1  (b,t)
		| Genlex.Kwd "right" 	->
			must_kwd s "(";
			let a = ty () in
			must_kwd s ",";
			let t = tm () in
			must_kwd s ")";
			Union2 (a, t)
		| Genlex.Kwd "absurd"	->
			must_kwd s "(";
			let t = tm () in
			must_kwd s ",";
			let a = ty () in
			must_kwd s ")";
			Absurd (a, t)
		| _						-> raise Parse_error
	in tm ();;

let ty_of_string a = ty_of_tk (lexer (Stream.of_string a));;

let tm_of_string t = tm_of_tk (lexer (Stream.of_string t));;

(* End parser.ml *)

let () =
	let l = [
		"A => B";
      	"A /\\ B";
      	"T";
      	"A \\/ B";
      	"_";
      	"not A"
	]
	in
	List.iter (fun s -> Printf.printf "the parsing of %S is %s\n%!" s (string_of_ty (ty_of_string s))) l;;

let () =
	let l = [
		"t u";
      	"fun (x : A) -> t";
      	"(t , u)";
      	"fst(t)";
      	"snd(t)";
      	"()";
      	"case t of x -> u | y -> v";
      	"left(t,B)";
      	"right(A,t)";
      	"absurd(t,A)"
	] in
	List.iter (fun s -> Printf.printf "the parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))) l;;

(* 2 *)


(* 2.1 *)

let rec string_of_ctx ctx =
	match ctx with
	| [] 			-> ""
	| [(x, a)] 		-> x ^ " : " ^(string_of_ty a)
	| (x, a) :: l	-> (string_of_ctx l) ^ " , " ^ x ^ " : " ^ (string_of_ty a);;

let () =
	let x = [("x", Imp(Tvar "A", Tvar "B"));("y", Prod (Tvar "A", Tvar "B"));("Z", Tvar "T")] in
	print_endline (string_of_ctx x);;

(* 2.2 *)

type sequent = context * ty;;

let string_of_seq seq =
	(string_of_ctx (fst seq)) ^ " |- " ^ (string_of_ty (snd seq));;

(* Start proving.ml *)

let rec prove env a =
	print_endline (string_of_seq (env,a));
	print_string "? "; flush_all ();
	let error e = print_endline e; prove env a in
	let cmd, arg =
		let cmd = input_line stdin in
		let n = try String.index cmd ' ' with Not_found -> String.length cmd in
		let c = String.sub cmd 0 n in
		let a = String.sub cmd n (String.length cmd - n) in
		let a = String.trim a in
		c, a in
	match cmd with
	| "intro"	-> (
		match a with
		| Imp (a, b)	->
			if arg = "" then error "Please provide an argument for intro."
			else
				let x = arg in
				let t = prove ((x,a)::env) b in
				Abs (x, a, t)
		| Prod (t1,t2)	->																					(* 2.7 *)
			if arg = "" then
				let a1 = prove env t1 in
				let a2 = prove env t2 in
            Pair (a1,a2)
			else error "wrong intro command for conjunction"
		| T				-> Truth																			(* 2.8 *)
		| _				-> error "Don't know how to introduce this."
		)

	| "fst"		->																							(* 2.7 *)
		if arg = "" then error "Please provide an argument for fst." else (
			match (List.assoc arg env) with
			| Prod (x, y) when x = a	-> Proj1 (Var arg)
			| _							-> error "Don't know how to fst this."
			)

	| "snd"		->																							(* 2.7 *)
		if arg = "" then error "Please provide an argument for snd." else (
			match (List.assoc arg env) with
			| Prod (x, y) when y = a	-> Proj2 (Var arg)
			| _							-> error "Don't know how to snd this."
			)   


	| "exact"	-> let t = tm_of_string arg in
		if infer_type env t <> a then error "Not the right type." else t

	| "elim"	->																							(* 2.4 *)
		if arg = "" then error "Please provide an argument for elim." else (
			match (List.assoc arg env) with
			| Imp (u, v)			-> if v = a then let t = prove env u in App (Var arg, t)
										else error "Don't know how to eliminate this."
			| Coprod (u, v)			-> let x1 = prove ((arg, u) :: env) a in  					(* 2.9 *)
										let x2 = prove ((arg, v) :: env) a in
										Case (Var arg, Abs(arg, u, x1), Abs(arg, v, x2))
			| F 					-> Absurd (a,Var arg) 												(* 2.10 *)
			| _ 					-> error "Don't know how to eliminate this."
			)

	| "cut"		->																							(* 2.6 *)
		if arg = "" then error "Please provide an argument for cut"
		else
			let t = ty_of_string arg in
			let c = prove env (Imp(t, a)) in
			let d = prove env t in
		App(c,d)

	| "left" 	->																							(* 2.9 *)
		if arg <> "" then error "wrong command of left." else (
			match a with
			| Coprod (c, d)	-> let x = prove env c in Union1(d, x)
			| _					-> error "Don't know how to left this."
			)

	| "right" 	->																							(* 2.9 *)
		if arg <> "" then error "wrong command of right." else (
			match a with
			| Coprod (c, d)	-> let x = prove env d in Union2(c,x)
			| _ 					-> error "Don't know how to right this."
			)

	| cmd		-> error ("Unknown command: " ^ cmd);;

let () =
	print_endline "Please enter the formula to prove:";
	let a = input_line stdin in
	let a = ty_of_string a in
	print_endline "Let's prove it.";
	let t = prove [] a in
	print_endline "done.";
	print_endline "Proof term is";
	print_endline (string_of_tm t);
	print_string  "Typechecking... "; flush_all ();
	assert (infer_type [] t = a);
	print_endline "ok.";;

(* End proving.ml *)

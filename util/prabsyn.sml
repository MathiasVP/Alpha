structure PrintAbsyn:
	sig
		val asString: Absyn.decl -> string
		val print: Absyn.decl list -> unit
	end =
struct

structure A = Absyn;
structure S = Symbol;

fun formatList f sep [] = ""
  | formatList f sep lst =
	let
		val s = List.foldl (fn(elem, acum) => acum ^ sep ^ f elem) "" lst;
		val n = String.size sep;
	in
		String.substring (s, n, String.size s - n)
	end;
	
fun indent 0 = ""
  | indent n = " " ^ indent (n-1);

fun declToString (A.VarDecl {var, ty, exp, pos}) =
		let
			val tyStr = case ty of
				SOME ty => tyToString ty
				| NONE => "NONE";
			val expStr = case exp of
				SOME exp => expToString 0 exp
				| NONE => "NONE";
		in
			"VarDecl(" ^ S.name var ^ ", " ^ tyStr ^ ", " ^ expStr ^ ")"
		end
  | declToString (A.FunctionDecl {name, formals, returnTy, body, pos}) =
		"FunctionDecl(" ^ S.name name ^
			", [" ^ formatList declToString ", " formals ^ "], " ^
			(case returnTy of
				SOME ty => tyToString ty ^ ",\n"
			  | NONE => "") ^
			statToString 1 body ^ "\n" ^
		")"
  | declToString (A.InterfaceDecl {name, extends, body, pos}) =
	let
		fun funHeaderToString {name, formals, returnTy, pos} =
			S.name name ^ ", " ^
			"[" ^ formatList declToString ", " formals ^ "]"
	in
		"InterfaceDecl(" ^ S.name name ^
			", " ^
				(case extends of
					SOME sym => S.name sym
				  | _ => "")
			^ ", [" ^ formatList funHeaderToString ",\n" body ^ "]" ^
		")"
	end
  | declToString (A.ClassDecl {name, extends, implements, body, pos}) =
	let
		fun bodyElementToString (encaps, decl) =
			let
				val acc = case encaps of
					A.PRIVATE => "private"
				  | A.PROTECTED => "protected"
				  | A.PUBLIC => "public"
			in
				acc ^ ", " ^ declToString decl
			end
	in
		"ClassDecl(" ^ S.name name ^
			", " ^ 
				(case extends of
					SOME sym => S.name sym
				  | NONE => "")
			^ ", [" ^ formatList S.name ", " implements ^ "]" ^
			", [" ^ formatList bodyElementToString ",\n" body ^ "]" ^
		")"
	end

and statToString n (A.VarDeclStat {var, ty, exp, pos}) =
	let
		val tyStr = case ty of
			SOME ty => tyToString ty
			| NONE => "NONE";
		val expStr = case exp of
			NONE => "NONE"
		  | SOME exp => expToString n exp
	in
		indent n ^ "VarDeclStat(" ^ S.name var ^ ", " ^ tyStr ^ ", " ^ expStr ^ ")"
	end
  | statToString n (A.ExpStat exp) =
		let
			val expStr = case exp of
				SOME exp => expToString n exp
			  | NONE => "NONE";
		in
			indent n ^ "ExpStat(" ^ expStr ^ ")"
		end
  |	statToString n (A.CompoundStat stats) =
		indent n ^ "CompoundStat([\n" ^
		formatList (statToString (n+1)) ",\n" stats ^ "\n" ^
		indent n ^ "])"
  |	statToString n (A.SelectionStat {test, ifBody, elseBody, pos}) =
		let
			val elseStr = case elseBody of
				SOME elseBody => statToString (n+1) elseBody
			  | NONE => "NONE"
		in
			indent n ^ "SelectionStat(" ^ expToString n test ^ ",\n" ^
			statToString (n+1) ifBody ^ ",\n" ^
			indent n ^ elseStr ^ ")"
		end
  |	statToString n (A.ReturnStat (exp, pos)) =
		let
			val expStr = case exp of
				SOME exp => expToString n exp
			  | NONE => "NONE";
		in
			indent n ^ "ReturnStat(" ^ expStr ^ ")"
		end
  |	statToString n (A.BreakStat pos) =
		indent n ^ "BreakStat"
  |	statToString n (A.IterationStat {init, test, incr, body, pos}) =
		let
			val initStr = case init of
				NONE => "NONE"
			  | SOME (A.Decl x) => declToString (A.VarDecl x)
			  | SOME (A.Exp exp) => expToString n exp;
			 
			val testStr = case test of
				NONE => "NONE"
			  | SOME exp => expToString n exp;
			
			val incrStr = case incr of
				NONE => "NONE"
			  | SOME exp => expToString n exp;
		in
			indent n ^ "IterationStat(" ^
				initStr ^ ", " ^
				testStr ^ ", " ^
				incrStr ^ ",\n" ^
				statToString (n+1) body ^ "\n" ^
				indent n ^ ")"
		end

and expToString n (A.VarExp var) = "VarExp(" ^ varToString n var ^ ")"
  | expToString n (A.IntExp m) = "IntExp(" ^ Int.toString m ^ ")"
  | expToString n (A.StringExp s) = "StringExp(" ^ s ^ ")"
  | expToString n (A.CharExp s) = "CharExp(" ^ s ^ ")"
  | expToString n (A.FloatExp f) = "FloatExp" ^ Real.toString f ^ ")"
  | expToString n (A.BoolExp b) = "BoolExp(" ^ Bool.toString b ^ ")"
  | expToString n A.ThisExp = "ThisExp"
  | expToString n (A.UnOpExp {exp, oper, pos}) =
		"UnOpExp(" ^ expToString n exp ^ ", " ^
			operToString oper ^
		")"
  |	expToString n (A.BinOpExp {left, oper, right, pos}) =
		"BinOpExp(" ^ expToString n left ^ ", " ^
			operToString oper ^ ", " ^
			expToString n right ^
		")"
  |	expToString n (A.LambdaExp {formals, returnTy, body, pos}) =
		"LambdaExp(" ^
			formatList declToString ", " formals ^ ", " ^
			tyToString returnTy ^ ",\n" ^
			statToString (n+1) body ^ "\n" ^
			indent n ^ ")"
  |	expToString n (A.CallOrConsExp {func, args, pos}) =
		"CallOrConsExp(" ^ expToString n func ^ ", " ^ formatList (expToString n) ", " args ^ ")"
  |	expToString n (A.AssignExp {var, exp, pos}) =
		"AssignExp(" ^ varToString n var ^ ", " ^ expToString n exp ^ ")"
  | expToString n (A.PostfixOpExp {exp, oper, pos}) =
		"PostfixOpExp(" ^ expToString n exp ^ ", " ^ operToString oper ^ ")"
  | expToString n (A.PrefixOpExp {exp, oper, pos}) =
		"PrefixOpExp(" ^ expToString n exp ^ ", " ^ operToString oper ^ ")"
  | expToString n (A.ArrayExp {ty, exp, ...}) =
		"ArrayExp(" ^ tyToString ty ^ ", " ^ expToString n exp ^ ")" 
		
and varToString n (A.SimpleVar (sym, _)) =
		"SimpleVar (" ^ S.name sym ^ ")"
  | varToString n (A.SubscriptVar (var, exp, _)) =
		"SubscriptVar(" ^ expToString n var ^ ", " ^ expToString n exp ^ ")"
  | varToString n (A.FieldVar (exp, sym, _)) =
		"FieldVar(" ^ expToString n exp ^ ", " ^ S.name sym ^ ")"
		
and operToString A.PlusOp = "Plus"
  |	operToString A.MinusOp = "Minus"
  | operToString A.TimesOp = "Times"
  | operToString A.DivideOp = "Divide"
  | operToString A.AndOp = "And"
  | operToString A.OrOp = "Or"
  | operToString A.EqOp = "Eq"
  | operToString A.NeqOp = "Neq"
  | operToString A.LtOp = "Lt"
  | operToString A.LeOp = "Le"
  | operToString A.GtOp = "Gt"
  | operToString A.GeOp = "Ge"
  | operToString A.BangOp = "Bang"
  | operToString A.UminusOp = "Uminus"
	
and tyToString (A.NameTy (sym, pos)) = S.name sym
  | tyToString (A.FunTy {formalTys, returnTy, pos}) =
		"FunTy([" ^ (formatList tyToString ", " formalTys) ^ "]" ^ tyToString returnTy ^ ")"
  | tyToString (A.ArrayTy ty) = "ArrayTy(" ^ tyToString ty ^ ")"

fun asString decl =
	declToString decl;

fun print decls =
	List.app (TextIO.print o declToString) decls;
	
end;
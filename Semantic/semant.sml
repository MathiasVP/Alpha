signature SEMANT =
sig
  val transProg: Absyn.decl list -> Translate.frag list
end

structure Semant :> SEMANT =
struct

structure S = Symbol
structure A = Absyn
structure E = Env
structure Ty = Types
structure PT = PrintTypes
structure PO = PrintOperators
structure Tr = Translate

val err = ErrorMsg.error
fun errorExp venv = {env = venv, ty = Ty.ERROR, ir = (Tr.emptyEx, [])}

fun transProg absyn =
    let
		fun visitTopLevel (decl, {env = (venv, tenv), ir = (ir, _)}) =
			let
				val {env = (venv', tenv'), ir = (ir', _)} =
					transDecl venv tenv E.initLevel NONE NONE
					(fn (sym, _) => (Tr.allocGlobal E.initLevel sym true, E.Public, NONE)) decl
			in
				{env = (venv', tenv'), ir = (Tr.seq2IR [ir, ir'], [])}
			end
			
		val {env = (venv, _), ir = (initIR, _)} = List.foldl visitTopLevel
			{env = (Env.baseVenv, Env.baseTenv), ir = (Tr.emptyEx, [])} absyn
			
		val level = Tr.newLevel {
			parent = E.initLevel,
			name = Temp.topLabel,
			formals = 0
		}

		val callMain = case S.look (venv, S.symbol "main") of
			SOME (E.FunEntry {label, ...}) =>
				Tr.entryCall2IR (label, [])
		  | _ =>
			(err 0 "Entry function 'main' not defined"; Tr.emptyNx)
		
		val _ = Tr.initEntryExit {level = level, body = Tr.seq2IR [initIR, Tr.entryCall2IR ((Temp.namedLabel "__init"), []), callMain]};
    in
		Tr.getResult ()
    end
	
and equalTypes Ty.ERROR _ = true
  | equalTypes _ Ty.ERROR = true
  | equalTypes t1 t2 = t1 = t2

(* Verify that the second encapsulation is at least as strong as the first *)
and encapsAtLeast A.PUBLIC _ = true
  | encapsAtLeast A.PROTECTED A.PROTECTED = true
  |	encapsAtLeast A.PROTECTED A.PRIVATE = true
  | encapsAtLeast A.PRIVATE A.PRIVATE = true
  | encapsAtLeast _ _ = false

(*	True if the first argument is a subtype of the second
	The subtyping rules in Alpha are as follows:
	t1 is a subtype of t2 (we write t1 <= t2) iff one of these rules apply
	(1) t1 = t2
	(2) t2 is an interface and t1 is a class that implements this interface
	(3) t1 and t2 are classes and t1 extends t2
	(4) t1 and t2 are interfaces and t1 extends t2
	(5) There exists a type t such that: t1 <= t and t <= t2
	
	Note that this <= relation is anti-symmetric,
	ie. if t1 <= t2 and t2 <= t1 then t1 = t2
*)
and subtype t1 t2 =
	if equalTypes t1 t2 then
		true
	else
		case (t1, t2) of
			(Ty.CLASS {implements, extends, ...}, Ty.INTERFACE {...}) =>
				List.exists (fn t => subtype t t2) implements
				orelse
				(case extends of
					SOME t => subtype t t2
				  | NONE => false)
		  | (Ty.CLASS {extends, ...}, Ty.CLASS {...}) =>
				(case extends of
					SOME t => subtype t t2
				  | NONE => false)
		  | (Ty.INTERFACE {extends, ...}, Ty.INTERFACE {...}) =>
				(case extends of
					SOME t => subtype t t2
				  | NONE => false)
		  | (_, _) => false
		  
and validateVisbility vis class sym pos =
	case (vis, class) of
		(E.Private ty, SOME {ty = classTy, ...}) =>
		if not (equalTypes ty classTy) then
			err pos ("Error: " ^ S.name sym ^ " cannot be accessed from outside class " ^ PT.asString ty)
		else ()
	  | (E.Private ty, NONE) =>
		err pos ("Error: " ^ S.name sym ^ " cannot be accessed from outside class " ^ PT.asString ty)
	  | (E.Protected ty, SOME {ty = classTy, ...}) =>
		if not (subtype classTy ty) then
			err pos ("Error: " ^ S.name sym ^ " can only be accessed by subclasses of " ^ PT.asString ty)
		else ()
	  | (E.Protected ty, NONE) =>
		err pos ("Error: " ^ S.name sym ^ " can only be accessed by subclasses of " ^ PT.asString ty)
	  | (E.Public, _) => ()
	  
and fields venv (Ty.CLASS {name, extends, implements}) =
	let
		val (methods, variables, tyOffsets, vtableLabel) = case S.look (venv, name) of
			SOME (E.ClassEntry {methods, variables, tyOffsets, vtableLabel, ...}) =>
				(methods, variables, tyOffsets, SOME vtableLabel)
		  | _ => raise Fail "Unexpected missing class entry in variable environment"
	in
		(List.map #2 methods, variables, tyOffsets, vtableLabel)
	end
  | fields venv (Ty.INTERFACE {name, ...}) =
	let
		val entries = case S.look (venv, name) of
			SOME (E.InterfaceEntry {entries}) => entries
		  | _ => raise Fail "Unexpected missing interface entry in variable environment"
	in
		(List.map #2 entries, [], [], NONE)
	end
  | fields venv _ = ([], [], [], NONE)
  
and	compareFormals [] [] n pos name = true
  | compareFormals (f1::formals1) (f2::formals2) n pos name =
	let
		val resTail = compareFormals formals1 formals2 (n+1) pos name
	in
		if subtype f1 f2 then resTail
		else false before
			(err pos ("Error: Formal parameter mismatch for parameter " ^
				Int.toString n ^ ". Expected: " ^
				PT.asString f1 ^ ", but got " ^
				PT.asString f2))
	end
  | compareFormals formals1 [] n pos name = false before (err pos ("Error: Too many formal parameters for function " ^ name))
  | compareFormals [] formals2 n pos name = false before (err pos ("Error: Too few formal parameters for function " ^ name))
  
and typeOfDecl tenv (A.VarDecl {var, ty = SOME ty, exp, pos}) =
		transTy tenv ty
  | typeOfDecl tenv (A.VarDecl {var, ty = NONE, exp, pos}) =
		raise Fail "Calling typeOfDecl on NONE"
  | typeOfDecl tenv (A.FunctionDecl {name, formals, returnTy, body, pos}) =
		(case returnTy of
			SOME ty => Ty.FUNCTION (List.map (typeOfDecl tenv) formals, transTy tenv ty)
		  | NONE => raise Fail "Expected SOME A.Ty")
  | typeOfDecl tenv (A.InterfaceDecl {name, extends, body, pos}) =
		let
			val extends' =
				case extends of
					SOME e =>
					(
						case S.look (tenv, e) of
							NONE => (err pos ("Error: Undefined type '" ^ S.name e ^ "'"); SOME Ty.ERROR)
						  | SOME ty => SOME ty
					)
				  | NONE => NONE
		in
			Ty.INTERFACE { name = name
						 , extends = extends'}
		end
  | typeOfDecl tenv (A.ClassDecl {name, extends, implements, body, pos}) =
	let
		val extends' = case extends of
			SOME e =>
			(
				case S.look (tenv, e) of
					NONE =>
						(err pos ("Error: Undefined type " ^ S.name e); SOME Ty.ERROR)
				  | SOME (Ty.INTERFACE _) =>
					(err pos ("Error: Class " ^ S.name name ^
						" cannot extend interface " ^ S.name e); SOME Ty.ERROR)
				  | SOME (c as Ty.CLASS _) => SOME c
				  | SOME ty =>
					(err pos ("Error: Class " ^ S.name name ^
						" cannot extend type " ^ PT.asString ty); SOME Ty.ERROR)
			)
		  | NONE => NONE
				
		val implements' = List.foldl (fn (i, is) =>
			case S.look (tenv, i) of
				NONE =>
					(err pos ("Error: Undefined type " ^ S.name i); is)
			  | SOME (i' as Ty.INTERFACE _) => i'::is
			  | SOME ty =>
				(err pos ("Error: Class " ^ S.name name ^
					" cannot implement type " ^ PT.asString ty ^
					". An interface-type is required"); is)
		) [] implements
	in
		Ty.CLASS { name = name
				 , extends = extends'
				 , implements = implements'}
	end

and transTy tenv (A.NameTy (sym, pos)) =
	(case (S.look (tenv, sym)) of
		NONE => (err pos ("Undefined type: " ^ (S.name sym)); Ty.ERROR)
	  | SOME t => t)
  | transTy tenv (A.FunTy {formalTys, returnTy, pos}) =
		Ty.FUNCTION (List.map (transTy tenv) formalTys, transTy tenv returnTy)
  | transTy tenv (A.ArrayTy ty) =
		Ty.ARRAY (transTy tenv ty)
		
and checkIdentifier venv level sym pos =
	let
		fun redeclError () =
			err pos ("Error: Redeclaration of identifier " ^ S.name sym)
		fun invalidError () =
			err pos ("Error: Invalid identifier " ^ S.name sym)
	in
		case S.look (venv, sym) of
			NONE => ()
		  | SOME (E.VarEntry {level = level', ...}) =>
			if level = level' then redeclError () else ()
		  | SOME (E.FunEntry {level = level', ...}) =>
			if level = level' then redeclError () else ()
		  | SOME _ => invalidError ()
	end
		
and transDecl venv tenv level func class builder (A.VarDecl {var, ty = NONE, exp = SOME exp, pos}) =
	let
		val _ = checkIdentifier venv level var pos
		val {env = venv', ty, ir = (expInitIR, expIRs)} = transExp venv tenv level func class exp
		val (access, vis, gcAccess) = builder (var, ty)
		val entry = E.VarEntry {access = access, level = level, ty = ty, vis = vis, gcAccess = gcAccess}
		val assignIR = Tr.assign2IR (Tr.simpleVar access, expIRs, ty, fields venv' ty)
	in
		{env = (S.enter (venv', var, entry), tenv), ir = (expInitIR, [assignIR])}
	end
  | transDecl venv tenv level func class builder (A.VarDecl {var, ty = SOME ty, exp = NONE, pos}) =
	let
		val _ = checkIdentifier venv level var pos
		val ty' = transTy tenv ty;
		val (access, vis, gcAccess) = builder (var, ty')
		val entry = E.VarEntry {access = access, level = level, ty = ty', vis = vis, gcAccess = gcAccess}
	in
		{env = (S.enter(venv, var, entry), tenv), ir = (Tr.emptyEx, [])}
	end
		
  | transDecl venv tenv level func class builder (A.VarDecl {var, ty = SOME ty, exp = SOME exp, pos}) =
	let
		val _ = checkIdentifier venv level var pos
		val ty' = transTy tenv ty
		val {env = venv', ty = expTy, ir = (expInitIR, expIRs)} = transExp venv tenv level func class exp
		val (access, vis, gcAccess) = builder (var, ty')
		val entry = case (ty', expTy) of
			(Ty.ERROR, _) => E.VarEntry {access = access, level = level, ty = Ty.ERROR, vis = vis, gcAccess = gcAccess}
		  | (_, Ty.ERROR) => E.VarEntry {access = access, level = level, ty = Ty.ERROR, vis = vis, gcAccess = gcAccess}
		  | (t, t') =>
			if subtype t' t then
				E.VarEntry {access = access, level = level, ty = t, vis = vis, gcAccess = gcAccess}
			else
				(err pos ("Type mismatch: Cannot assign expression of type "
				 ^ PT.asString t' ^ " to variable of type " ^ PT.asString t);
				 E.VarEntry {access = access, level = level, ty = Ty.ERROR, vis = vis, gcAccess = gcAccess})
		val assignIR = Tr.assign2IR (Tr.simpleVar access, expIRs, ty', fields venv' expTy)
	in
		{env = (S.enter(venv', var, entry), tenv), ir = (expInitIR, [assignIR])}
	end
  | transDecl venv tenv level func class builder (A.VarDecl {var, ty = NONE, exp = NONE, pos}) =
	let
		val _ = raise Fail "A.VarDecl without type or init expression"
	in
		{env = (venv, tenv), ir = (Tr.emptyEx, [])}
	end
  | transDecl venv tenv level func class builder (funcDecl as (A.FunctionDecl {name, formals, returnTy, body, pos})) =
	let
		(* If there is no return type it's a constructor, so just
		   put an arbitraty type for consistency. Void seemed natural *)
		val returnTy' = case returnTy of
			SOME ty => transTy tenv ty
		  | NONE => Ty.VOID
		(* Calculate types of formal params and the space required *)
		val (tys, formalsSize) = List.foldl (fn (f, (tys, size)) =>
			let
				val ty = typeOfDecl tenv f
			in
				(tys @ [ty], size + Tr.sizeOfTy ty)
			end
		) ([], 0) formals
			
		val formalsSize' =
			if Tr.sizeOfTy returnTy' > 4 then
			formalsSize + 4
			else formalsSize
			
		val (label, level', access, entry) =
			let
				fun newEntry () =
					let
						val label = Tr.newLabel (S.name name)
						val level' = Tr.newLevel {
							parent = level,
							name = label,
							formals = formalsSize'
						}
						val access = Tr.allocGlobal level name false
						val entry = E.FunEntry {
							formals = tys,
							result = returnTy',
							label = label,
							level = level',
							access = access,
							vis = E.Public
						}
					in
						(label, level', access, entry)
					end
			in
				case S.look (venv, name) of
					NONE => newEntry ()
				  | SOME (entry as E.FunEntry {label, level, access, ...}) =>
					(label, level, access, entry)
				  | SOME (E.ClassEntry {constructors, ...}) =>
					(* This function is a constructor.
					   Find the correct entry based on the formal param list *)
					(case List.find (fn entry =>
						case entry of
							E.FunEntry {formals = formals', ...} =>
							(List.all (fn (formal1, formal2) =>
								formal1 = formal2
							) (ListPair.zipEq (tys, formals'))
							handle UnequalLengths => false)
						  | _ => false
					 ) constructors of
						SOME (entry as E.FunEntry {label, level, access, ...}) =>
						(label, level, access, entry)
					  | _ => raise Fail "Expected SOME FunEntry")
				  | _ => raise Fail ("Expected SOME FunEntry or NONE for entry " ^ S.name name)
				end
			
		fun enterParam (decl, (venv, nr)) =
			let
				(* No IR will be generated since the params cannot be default constructed *)
				val {env = (venv', tenv'), ir = _} =
					transDecl venv tenv level' func class (fn (_, ty) =>
						(Tr.accessOfFormal level' nr true (Tr.sizeOfTy ty), E.Public, NONE)
					) decl
			in
				(venv', nr+1)
			end
		
		(* Insert formal params + the new function into our venv.
		   We can add either 1 or 2 arguments to the function. The first extra argument
		   is the ptr to the environment that the function captures,
		   which is a null ptr for functions that are not lambdas.
		   Furtheremore we add 1 additinoal argument for transferring
		   return values whose size is > 4 bytes since we
		   can't return such a value in a register.*)
		val (venv', _) = List.foldl enterParam (venv, if Tr.sizeOfTy returnTy' > 4 then 2 else 1) formals
		val venv'' = S.enter(venv', name, entry)
			
		val func' = {
			ty = (case returnTy of
				NONE => Ty.FUNCTION (tys, Ty.VOID)
			  | SOME ty => typeOfDecl tenv funcDecl),
			captures = ref [] : (Tr.access * Tr.access * Ty.ty) list ref
		}
		val {ir = bodyIR, ...} = transStat venv'' tenv level' (SOME func') NONE class body
	in
		Tr.funEntryExit {level = level', body = bodyIR};
		{env = (S.enter(venv, name, entry), tenv), ir = (Tr.emptyEx, [])}
	end
   | transDecl venv tenv level func class builder (i as A.InterfaceDecl {name, extends, body, pos}) =
	(case S.look (tenv, name) of
		NONE =>
		let
			val interfaceTy = typeOfDecl tenv i
			val tenv' = S.enter (tenv, name, interfaceTy);
			
			(* Create the list of methods for E.InterfaceEntry in the environment *)
			val (vTableSize, entries) = List.foldl (fn ({name, formals, returnTy, pos}, (vtableOffset, entries)) =>
				let
					val label = Tr.newLabel (S.name name)
					val (tys, formalsSize) = List.foldl (fn (f, (tys, size)) =>
						let
							val ty = typeOfDecl tenv' f
						in
							(tys @ [ty], size + Tr.sizeOfTy ty)
						end
					) ([], 0) formals
					
					val level' = Tr.newLevel {
						parent = level,
						name = label,
						formals = formalsSize
					}
				in
					(vtableOffset + 4,
						entries @ [(name, { formals = tys,
								 result = transTy tenv' returnTy,
								 label = label,
								 level = level',
								 access = Tr.allocVtableEntry level vtableOffset true,
								 vis = E.Public})]
					)
				end
			) (0, []) body
			
			val venv' = S.enter (venv, name, E.InterfaceEntry {entries = entries})
			
			fun findMethods (SOME (Ty.INTERFACE {name = name', extends})) =
				let
					val elements =
						case S.look (venv', name') of
							SOME (E.InterfaceEntry {entries, ...}) => entries
						  | NONE => (err pos ("Error: Interface '" ^ S.name name' ^ "' was not declared"); [])
						  | _ => raise Fail "Expected SOME InterfaceEntry or NONE"
				in
					findMethods extends @ elements
				end
			  | findMethods (SOME Ty.ERROR) = []
			  | findMethods (SOME ty) =
				(err pos ("Error: Expected interface-type, but received " ^
					(PT.asString ty)); [])
			  | findMethods NONE = []
			
			val _ = List.foldl (fn (m as (name', _), methods) =>
				if List.exists (fn (name'', _) =>
					S.name name' = S.name name'') methods then
					(err pos ("Error: Function '" ^ S.name name' ^ "'" ^
							" in interface '" ^ S.name name ^ "'" ^
							" has already been declared");
						m::methods)
				else m::methods
			) [] (findMethods (SOME interfaceTy))
		in
			{env = (venv', tenv'), ir = (Tr.emptyEx, [])}
		end
	  | _ =>
		(err pos ("Error: " ^ S.name name ^ " has already been defined");
		 {env = (venv, tenv), ir = (Tr.emptyEx, [])}))
	  | transDecl venv tenv level func class builder (c as A.ClassDecl {name, extends, implements, body, pos}) =
		(case S.look (tenv, name) of
			NONE =>
			let
				val (classTy as Ty.CLASS { name = _, extends, implements}) =
					typeOfDecl tenv c
				val tenvClass = S.enter(tenv, name, classTy)
				val classLevel = Tr.newLevel {
					parent = level,
					name = name,
					formals = 0
				}
				val class' = SOME {
					ty = classTy,
					name = name
				}
				
				(* Create lists of members and methods *)
				val (vars, funcs) = List.partition (fn (encaps, elem) =>
					case elem of
						A.VarDecl _ => true
					  | A.FunctionDecl _ => false
					  | _ => raise Fail "Unexpected declaration in class"
				) body
				
				fun findInherited (Ty.CLASS {name, extends, ...}) =
					let
						val (methods, variables, tyOffsets) = case S.look(venv, name) of
							SOME (E.ClassEntry {methods, variables, tyOffsets, ...}) =>
							(methods, variables, tyOffsets)
						  | _ => ([], [], [])
					in
						case extends of
							SOME e =>
							let val (m, v, talist) = findInherited e
							in (methods @ m, variables @ v, tyOffsets @ talist)
							end
						  | NONE => (methods, variables, tyOffsets)
					end
				  | findInherited _ =
					raise Fail "findInherited called on object of non-class type"
					
				val (inheritedFuncs, inheritedVars, inheritedTyOffsetList) = findInherited classTy
				
				(* Allocate a vptr for the class *)
				val _ = Tr.allocMember classLevel 4
				
				(* If this is the top of a inheritence hierachy we place a forwardee object, which is used during
				   GC'ing. This way every class object gets a forwardee object. *)
				val forwardee = case extends of
					NONE => SOME (S.intSymbol (), E.VarEntry {
						access = Tr.allocMember classLevel 4,
						level = level,
						ty = classTy,
						vis = E.Public,
						gcAccess = NONE
					})
				  | SOME _ => NONE
				
				(* Insert base vars into environment *)
				val venvVars = List.foldl (fn ((sym, entry), venv) =>
					case entry of
						E.VarEntry {level, ty, vis, ...} =>
							let
								val access = Tr.allocMember classLevel (Tr.sizeOfTy ty)
							in
								S.enter (venv, sym, E.VarEntry {access = access, level = level, ty = ty, vis = vis, gcAccess = NONE})
							end
					  | _ => raise Fail "Expected variable entry"
				) venv inheritedVars
				
				(* Find all interface methods that should be implemented *)
				fun findInterfaceFuncs (Ty.INTERFACE {name = iname, extends}) =
					let
						val elements =
							case S.look (venvVars, iname) of
								SOME (E.InterfaceEntry {entries, ...}) => entries
							  | NONE => (err pos ("Error: Interface '" ^
											S.name iname ^ "' was undeclared");
										[])
							  | _ => raise Fail "Expected SOME InterfaceEntry or NONE"
					in
						case extends of
							NONE => elements
						  | SOME e => elements @ findInterfaceFuncs e
					end
				  | findInterfaceFuncs _ =
					raise Fail "findInterfaceFuncs called on non-interface type"
					
				val interfaceFuncs = List.map findInterfaceFuncs implements
				
				(* Insert vars into environment *)
				val (venvVars, tenvVars) = List.foldl (fn ((encaps, elem), (venv, tenv)) =>
					case elem of
						(var as A.VarDecl {...}) =>
							let	val {env = (venv', tenv'), ir = _} =
									transDecl venv tenv classLevel func class'
									(fn (_, ty) =>
										let
											val acc = Tr.allocMember classLevel (Tr.sizeOfTy ty)
											val vis = case encaps of
												A.PRIVATE => E.Private classTy
											  | A.PROTECTED => E.Protected classTy
											  | A.PUBLIC => E.Public
										in
											(acc, vis, NONE)
										end
									) var
							in
								(venv', tenv')
							end
					  | _ => raise Fail "Expected variable declaration"
				) (venvVars, tenvClass) vars
				
				(* Create functions that determine if an A.FunctionDecl
				   is an overwritten function or an interface implementation *)
				val (isOverwritten, isInterface) = let
					fun makeList lst =
						List.mapPartial (fn (encaps, decl) =>
							case decl of
								A.FunctionDecl {name, ...} =>
									(case List.find (fn (sym, _) => S.name name = S.name sym) lst of
										SOME (sym, {access, ...}) => SOME (sym, access)
									| NONE => NONE)
							| _ => NONE
						) funcs
					val overwritten = makeList inheritedFuncs
					val interface = makeList (List.concat interfaceFuncs)
					
					fun makeFun lst = fn decl =>
						case decl of
							A.FunctionDecl {name, ...} =>
							List.find (fn (sym, _) => S.name name = S.name sym) lst
						| _ => raise Fail "Expected A.FunctionDecl"
				in
					(makeFun overwritten, makeFun interface)
				end
				
				val (overwrittenFuncs, newFuncs, newInterfaceFuncs) =
				let
					val isOverwritten' = Option.isSome o isOverwritten o #2
					val isInterface' = Option.isSome o isInterface o #2
					
					val overwrittenFuncs = List.filter isOverwritten' funcs
					val newFuncs = List.filter (fn decl =>
						not (isInterface' decl) andalso not (isOverwritten' decl)
					) funcs
					val newInterfaceFuncs' = List.filter (fn decl =>
						isInterface' decl andalso not (isOverwritten' decl)
					) funcs
					
					(* Define the iota function from APL *)
					fun iota 0 = []
					  | iota n = 1::(map increment (iota (n-1)))
					and increment n = n+1;
					(* Sort a list of pairs based on the 2nd element *)
					val sort = ListMergeSort.sort (fn ((_, n), (_, m)) => n > m)
					val newInterfaceFuncs =
						List.map (fn (ty, ifuncs) =>
							let
								(* ifuncs' = [(1, fun1), (2, fun2), ..., (N, funN)] *)
								val ifuncs' = ListPair.zip (ifuncs, iota (List.length ifuncs))
								val decls = List.foldl (fn ((encaps, decl), decls) =>
									case decl of
										A.FunctionDecl {name, ...} =>
											(case List.find (fn ((sym, _), n) => S.name sym = S.name name) ifuncs' of
												SOME (_, n) => ((encaps, decl), n) :: decls
											  | NONE => decls)
									| _ => raise Fail "Expected A.FunctionDecl"
								) [] newInterfaceFuncs'
							in
							(* Sort the decls such that the order is the same as in the interface decl *)
							(ty, #1 (ListPair.unzip (sort decls)))
							end
						) (ListPair.zipEq (implements, interfaceFuncs))
				in
					(overwrittenFuncs, newFuncs, newInterfaceFuncs)
				end
								
				fun sub x y [] = []
				  | sub x y ((z as (z', _))::zs) =
					if x = S.name z' then y::zs
					else z::(sub x y zs)
				
				val inheritedFuncs = List.foldl (fn ((encaps, decl), funcs) =>
					case decl of
						A.FunctionDecl {name = name', formals, returnTy, pos, ...} =>
						let
							(* If no return type is specified it's a constructor *)
							val (returnTy', isCons) = case returnTy of
								SOME ty => (transTy tenvVars ty, false)
							  | NONE =>
								if S.name name' = S.name name then
									(classTy, true)
								else
									(Ty.ERROR, false) before
									err pos ("Constructor cannot have name " ^
										S.name name ^ ", expected " ^ S.name name')
							
							val label = Tr.newLabel (S.name name')
							val (tys, formalsSize) = List.foldl (fn (f, (tys, size)) =>
								let val ty = typeOfDecl tenvVars f
								in (tys @ [ty], size + Tr.sizeOfTy ty)
								end
							) ([], 0) formals
							val level' = Tr.newLevel {
								parent = level,
								name = label,
								formals = formalsSize
							}
							
							val _ = case List.find (fn (sym, _) => S.name sym = S.name name') inheritedFuncs of
								SOME (_, {formals = formals', result = returnTy, vis, ...}) =>
								let val encaps' = case vis of
												E.Private _ => A.PRIVATE
											  | E.Protected _ => A.PROTECTED
											  | E.Public => A.PUBLIC
								in
									if encapsAtLeast encaps encaps' then ()
									else err pos ("Error: Cannot reduce visibility of " ^
										"inherited function " ^ S.name name' ^ " in class " ^
										S.name name);
										compareFormals tys formals' 1 pos (S.name name');
										if subtype returnTy' returnTy then ()
										else err pos ("Error: Expected return type is: " ^
													PT.asString returnTy ^
													", but was: " ^
													PT.asString returnTy')
								end
							  | NONE => ()
							
							(* By construction we know it's an overwritten func *)
							val (_, acc) = Option.valOf (isOverwritten decl)
							val entry = {
								formals = tys,
								result = returnTy',
								label = label,
								level = level',
								access = acc,
								vis = case encaps of
									A.PRIVATE => E.Private classTy
								  | A.PROTECTED => E.Protected classTy
								  | A.PUBLIC => E.Public
							}
						in
							sub (S.name name') (name', entry) funcs
						end
					  | _ => raise Fail "Expected A.FunctionDecl"
				) inheritedFuncs overwrittenFuncs
				
				val (offset, functions, constructors) =
					List.foldl (fn ((encaps, decl), (offset, functions, constructors)) =>
					case decl of
						A.FunctionDecl {name = name', formals, returnTy, pos, ...} => 
						let
							val (returnTy', isCons) = case returnTy of
								SOME ty => (transTy tenvVars ty, false)
							  | NONE =>
								if S.name name' = S.name name then
									(classTy, true)
								else
									(Ty.ERROR, false) before
									err pos ("Constructor cannot have name " ^
									S.name name ^ ", expected " ^ S.name name')
									
							val label = Tr.newLabel (S.name name')
							val (tys, formalsSize) = List.foldl (fn (f, (tys, size)) =>
								let val ty = typeOfDecl tenvVars f
								in (tys @ [ty], size + Tr.sizeOfTy ty)
								end
							) ([], 0) formals
							val level' = Tr.newLevel {
								parent = level,
								name = label,
								formals = formalsSize
							}
							
							val entry = {
								formals = tys,
								result = returnTy',
								label = label,
								level = level',
								access = Tr.allocVtableEntry level' offset false,
								vis = case encaps of
									A.PRIVATE => E.Private classTy
								  | A.PROTECTED => E.Protected classTy
								  | A.PUBLIC => E.Public
							 }
						in
							if isCons then
								(offset, functions, constructors @ [E.FunEntry entry])
							else
								(offset + 4, functions @ [(name', entry)], constructors)
						end
					  | _ => raise Fail "Expected A.FunctionDecl"
					(* Add 4 bytes of offset since we also have a forwarding function *)
					) (4 * (1 + List.length inheritedFuncs), inheritedFuncs, []) newFuncs
				
				val (_, functions, tyOffsets) = List.foldl (fn ((ty, decls), (offset, functions, tyOffsets)) =>
					let
						val tyOffsets' = (ty, offset) :: tyOffsets
						val (offset', functions') = List.foldl (fn ((encaps, decl), (offset, functions)) =>
							case decl of
								A.FunctionDecl {name = name', formals, returnTy, pos, ...} => 
								let
									(* Interface function cannot be a constructor. So valOf is safe *)
									val returnTy' = transTy tenvVars (Option.valOf returnTy)
									val label = Tr.newLabel (S.name name')
									val (tys, formalsSize) = List.foldl (fn (f, (tys, size)) =>
										let val ty = typeOfDecl tenvVars f
										in (tys @ [ty], size + Tr.sizeOfTy ty)
										end
									) ([], 0) formals
									val level' = Tr.newLevel {
										parent = level,
										name = label,
										formals = formalsSize
									}
									
									(* Verify:
										- Function is implemented as public.
										- The parameter types are all subtypes of the ones specified in the interface
										- The return type is a subtype of the one specified in the interface
									*)
									val _ = (if encapsAtLeast encaps A.PUBLIC then ()
											 else err pos ("Error: Method " ^ S.name name' ^
												" in class " ^ S.name name ^
												" must have access specifier: 'public'");
											 case List.find (fn (sym, _) => S.name sym = S.name name') (List.concat interfaceFuncs) of
												SOME (_, {formals = formals', result = returnTy, ...}) =>
												(compareFormals formals' tys 1 pos (S.name name');
												 if subtype returnTy' returnTy then ()
												 else err pos ("Error: Expected return type is: " ^
													PT.asString returnTy ^
													", but was: " ^
													PT.asString returnTy'))
											  | NONE => raise Fail "Interface entry not found")
									
									val entry = {
										formals = tys,
										result = returnTy',
										label = label,
										level = level',
										access = Tr.allocVtableEntry level' offset false,
										vis = case encaps of
											A.PRIVATE => E.Private classTy
										  | A.PROTECTED => E.Protected classTy
										  | A.PUBLIC => E.Public
									}
								in
									(offset + 4, functions @ [(name', entry)])
								end
							  | _ => raise Fail "Expected A.FunctionDecl"
						) (offset, functions) decls
					in
						(offset', functions', tyOffsets')
					end
				) (offset, functions, inheritedTyOffsetList) newInterfaceFuncs
				
				val variables = inheritedVars @ (List.map (fn (_, decl) =>
						case decl of
							A.VarDecl {var, ...} => 
								(case S.look (venvVars, var) of
									SOME (entry as E.VarEntry {...}) => (var, entry)
								  | _ => raise Fail "Expected VarEntry")
						  | _ => raise Fail "Expected VarDecl"
					) vars)
				val variables = case forwardee of
					SOME v => v :: variables
				  | NONE => variables
					
				val variables' = List.map (fn (_, entry) =>
					case entry of
						E.VarEntry {ty, access, ...} => (ty, access)
					  | _ => raise Fail "Expected E.VarEntry"
				) variables
				
				(* Create vtable fragment *)
				val vtableLabel = Tr.table2IR (PT.asString classTy)
					((Tr.forwardClassObj2IR E.initLevel (PrintTypes.asString classTy) variables') :: (List.map (#label o #2) functions))
				
				val classEntry = E.ClassEntry {
					methods = functions,
					tyOffsets = tyOffsets,
					constructors = constructors,
					variables = variables,
					vtableLabel = vtableLabel
				}
				
				val venvMethods = List.foldl (fn ((name, entry), venv) =>
					S.enter (venv, name, E.FunEntry entry)
				) venvVars functions
				val venvClass = S.enter (venvMethods, name, classEntry)
			in
				List.app (fn (_, fundecl) =>
					(* Note: transDecl on a FunctionDecl returns no IR code and we have already folded the environments *)
					ignore (transDecl venvClass tenvVars classLevel func class' builder fundecl)
				) funcs;
				
				(* Enter the class entry into the environment *)
				{env = (S.enter (venv, name, classEntry), tenvClass), ir = (Tr.emptyEx, []) }
			end
		  | _ => (err pos ("Error: " ^ S.name name ^ " has already been defined");
		 {env = (venv, tenv), ir = (Tr.emptyEx, [])}))
   
and transVar venv tenv level func class (A.SimpleVar (sym, pos)) =
	(case S.look(venv, sym) of
		NONE => (err pos ("Error: Undefined identifier '" ^ S.name sym ^ "'");
			errorExp venv)
	  | SOME (E.VarEntry {ty = t, access = access as (level', _), vis = vis, ...}) =>
			let
				fun isGlobalVar (level', _) =
					level' = E.initLevel
					
				(* Very (very very!) ugly way of checking if an access
				   is belonging to a class object or not! *)
				fun isMemberVar access' =
					(ignore (Tr.memberInClass Tr.emptyEx access');
					 true
					) handle Fail _ => false
						
				fun isCapturedVar (access as (level', _)) =
					not (isGlobalVar access) andalso level <> level'
				
				val ir =
					if isGlobalVar access then
						Tr.simpleVar access
					else if isMemberVar access then
						Tr.simpleVar access
					else if isCapturedVar access then
						let
							(* Find list of capturing variables for current function *)
							val captures = case func of
								NONE =>
									raise Fail "Missing capture list for capturing lambda"
							  | SOME {captures, ...} => captures
						in
							(* Check if we already have this variable captured.
							   If not then update the capture list*)
							case List.find (fn (keyAcc, _, _) => keyAcc = access) (!captures) of
								NONE =>
									let
										val valAcc = Tr.allocMember level (Tr.sizeOfTy t)
									in
										captures := (!captures) @ [(access, valAcc, t)];
										Tr.simpleVar valAcc
									end
							  | SOME (_, valAcc, _) => Tr.simpleVar valAcc
						end
					else
						Tr.simpleVar access
			in
				validateVisbility vis class sym pos;
				{env = venv, ty = t, ir = (Tr.emptyEx, ir)}
			end
	  | SOME (E.FunEntry {formals, result, label, ...}) =>
		{env = venv, ty = Ty.FUNCTION(formals, result), ir = (Tr.emptyEx, Tr.fun2IR label)}
	  | SOME (E.ClassEntry _) =>
		((err pos ("Error: Invalid identifier name '" ^ S.name sym ^ "'"));
		 errorExp venv)
	  | SOME (E.InterfaceEntry _) =>
		((err pos ("Error: Invalid identifier name '" ^ S.name sym ^ "'"));
		 errorExp venv))
  | transVar venv tenv level func class (A.SubscriptVar (var, exp, pos)) =
	let
		val (venv', varTy, varInitIR, varIR) =
			case transExp venv tenv level func class var of
				{env = venv', ty, ir = (varInitIR, [varIR])} => (venv', ty, varInitIR, varIR)
			  | _ => raise Fail "Only 1 expression was expected"
		val (venv', expTy, expInitIR, expIR) =
			case transExp venv' tenv level func class exp of
				{env = venv', ty = expTy, ir = (expInitIR, [expIR])} => (venv', expTy, expInitIR, expIR)
			  | _ => raise Fail "Only 1 expression was expected"
	in
		case (varTy, expTy) of
			(Ty.ERROR, _) => errorExp venv'
		  | (_, Ty.ERROR) => errorExp venv'
		  | (Ty.ARRAY ty, Ty.INT) =>
			let
				val (subInitIR, subExpIRs) = Tr.subscript2IR (varIR, expIR, Tr.sizeOfTy ty)
			in
				{env = venv', ty = ty, ir = (Tr.seq2IR [varInitIR, expInitIR, subInitIR], subExpIRs)}
			end
		  | (Ty.STRING, Ty.INT) =>
			let
				val subExpIR = Tr.stringSubscript2IR (varIR, expIR)
			in
				{env = venv', ty = Ty.CHAR, ir = (Tr.seq2IR [varInitIR, expInitIR], [subExpIR])}
			end
		  | (varTy, expTy) =>
			(err pos ("Type mismatch: Expected type [T] or string, but was " ^
				PT.asString varTy);
			 err pos ("Type mismatch: Expected " ^
				"index expression to be of type int, but was " ^
				PT.asString expTy);
			 errorExp venv')
	end
  | transVar venv tenv level func class (A.FieldVar (exp, sym, pos)) =
	let
		val {env = venv', ty = expTy, ir = (expInitIR, expIR)} = transExp venv tenv level func class exp
		
		fun name (Ty.CLASS {name, ...}) = name
		  | name (Ty.INTERFACE {name, ...}) = name
		  | name _ = raise Fail "Expected class or interface"
		
		fun extends (Ty.CLASS {extends, ...}) = extends
		  | extends (Ty.INTERFACE {extends, ...}) = extends
		  | extends _ = raise Fail "Expected class or interface"
		  
		fun implements (Ty.CLASS {implements, ...}) = implements
		  | implements (Ty.INTERFACE _) = []
		  | implements _ = raise Fail "Expected class or interface"
		
		fun findField ty =
			let
				fun onEntry (methods, variables) =
					case (List.find (fn (name, entry) => name = sym) (methods @ variables), expIR) of
						(NONE, _) => NONE
					  | (SOME (_, E.VarEntry {ty, access, vis, ...}), _) =>
						SOME (ty, access, vis, [])
					  | (SOME (_, E.FunEntry {formals, result, access, vis, ...}), [exp]) =>
						SOME (Ty.FUNCTION (formals, result), access, vis, [exp])
					  | _ => raise Fail "Unexpected entry"
			in
				(case S.look (venv', name ty) of
					SOME (E.ClassEntry {methods, variables, ...}) => onEntry (List.map (fn (s, m) => (s, E.FunEntry m)) methods, variables)
				  | SOME (E.InterfaceEntry {entries}) => onEntry (List.map (fn (s, m) => (s, E.FunEntry m)) entries, [])
				  | _ => raise Fail "Expected ClassEntry")
			end
	in
		case findField expTy of
			NONE => (err pos ("Error: " ^
							S.name sym ^
							" is not a member of class '" ^ PT.asString expTy ^ "'");
							errorExp venv')
		  | SOME (ty, access, vis, possibleEnv) =>
			let
				(* Since exp has type Class we know that
				   there's only 1 element in the list *)
				val base = List.hd expIR
			in
				validateVisbility vis class sym pos;
				{env = venv', ty = ty, ir = (expInitIR, Tr.memberInClass base access @ possibleEnv)}
			end
	end
		
and transExp venv tenv level func class (A.VarExp var) =
		transVar venv tenv level func class var
 |  transExp venv tenv level func class (A.IntExp n) = {env = venv, ty = Ty.INT, ir = (Tr.emptyEx, [Tr.int2IR n])}
 |  transExp venv tenv level func class (A.StringExp s) = {env = venv, ty = Ty.STRING, ir = (Tr.emptyEx, [Tr.string2IR s])}
 |  transExp venv tenv level func class (A.CharExp s) = {env = venv, ty = Ty.CHAR, ir = (Tr.emptyEx, [Tr.char2IR s])}
 |  transExp venv tenv level func class (A.FloatExp r) = {env = venv, ty = Ty.FLOAT, ir = (Tr.emptyEx, [Tr.float2IR r])}
 |  transExp venv tenv level func class (A.BoolExp b) = {env = venv, ty = Ty.BOOL, ir = (Tr.emptyEx, [Tr.bool2IR b])}
 |  transExp venv tenv level func (SOME {ty = classTy, name = className}) A.ThisExp = {env = venv, ty = classTy, ir = (Tr.emptyEx, Tr.this2IR level)}
 |  transExp venv tenv level func class (A.UnOpExp {exp, oper = A.BangOp, pos}) =
		let
			val (venv', ty, initIR, expIR) =
				case transExp venv tenv level func class exp of
					{env = venv', ty, ir = (initIR, [expIR])} => (venv', ty, initIR, expIR)
				  | _ => raise Fail "Only 1 expression was expected"
			val ty' = case ty of
					Ty.ERROR => Ty.ERROR
				  | Ty.BOOL => Ty.BOOL
				  | t => (err pos ("Error: Cannot apply unary operator ! to expression of type "
					^ PT.asString t);
						Ty.ERROR)
		in
			{env = venv', ty = ty', ir = (initIR, [Tr.not expIR])}
		end
 |  transExp venv tenv level func class (A.UnOpExp {exp, oper = A.UminusOp, pos}) =
		let
			val (venv', ty, initIR, expIR) =
				case transExp venv tenv level func class exp of
					{env = venv', ty, ir = (initIR, [expIR])} => (venv', ty, initIR, expIR)
				  | _ => raise Fail "Only 1 expression was expected"
		in
			case ty of
				Ty.ERROR => errorExp venv'
			  | Ty.INT => {env = venv', ty = Ty.INT, ir = (initIR, [Tr.intNeg expIR])}
			  | Ty.FLOAT => {env = venv', ty = Ty.FLOAT, ir = (initIR, [Tr.floatNeg expIR])}
			  | t => (err pos ("Error: Cannot apply unary operator - to expression of type "
					^ PT.asString t); errorExp venv')
		end
 |  transExp venv tenv level func class (A.UnOpExp {exp, oper = _, pos}) =
		raise Fail "Unexpected operation for expression A.UnOpExp"
 |  transExp venv tenv level func class (A.BinOpExp {left, oper, right, pos}) =
	let
		(* Types.ty -> A.oper * Types.ty * Tr.exp *)
		fun opsForType Ty.INT =
			[(A.PlusOp, Ty.INT, Tr.binIntOp2IR A.PlusOp),
			(A.MinusOp, Ty.INT, Tr.binIntOp2IR A.MinusOp),
			(A.TimesOp, Ty.INT, Tr.binIntOp2IR A.TimesOp),
			(A.DivideOp, Ty.INT, Tr.binIntOp2IR A.DivideOp),
			(A.EqOp, Ty.BOOL, Tr.binIntOp2IR A.EqOp),
			(A.NeqOp, Ty.BOOL, Tr.binIntOp2IR A.NeqOp),
			(A.LtOp, Ty.BOOL, Tr.binIntOp2IR A.LtOp),
			(A.LeOp, Ty.BOOL, Tr.binIntOp2IR A.LeOp),
			(A.GtOp, Ty.BOOL, Tr.binIntOp2IR A.GtOp),
			(A.GeOp, Ty.BOOL, Tr.binIntOp2IR A.GeOp)]
		 | opsForType Ty.STRING =
			[(A.PlusOp, Ty.STRING, Tr.stringOp2IR A.PlusOp),
			(A.EqOp, Ty.BOOL, Tr.stringOp2IR A.EqOp),
			(A.NeqOp, Ty.BOOL, Tr.stringOp2IR A.NeqOp)]
		 | opsForType Ty.FLOAT =
			[(A.PlusOp, Ty.FLOAT, Tr.binRealOp2IR A.PlusOp),
			(A.MinusOp, Ty.FLOAT, Tr.binRealOp2IR A.MinusOp),
			(A.TimesOp, Ty.FLOAT, Tr.binRealOp2IR A.TimesOp),
			(A.DivideOp, Ty.FLOAT, Tr.binRealOp2IR A.DivideOp),
			(A.EqOp, Ty.BOOL, Tr.binRealOp2IR A.EqOp),
			(A.NeqOp, Ty.BOOL, Tr.binRealOp2IR A.NeqOp),
			(A.LtOp, Ty.BOOL, Tr.binRealOp2IR A.LtOp),
			(A.LeOp, Ty.BOOL, Tr.binRealOp2IR A.LeOp),
			(A.GtOp, Ty.BOOL, Tr.binRealOp2IR A.GtOp),
			(A.GeOp, Ty.BOOL, Tr.binRealOp2IR A.GeOp)]
		 | opsForType Ty.BOOL =
			[(A.EqOp, Ty.BOOL, Tr.binIntOp2IR A.EqOp),
			(A.NeqOp, Ty.BOOL, Tr.binIntOp2IR A.NeqOp),
			(A.AndOp, Ty.BOOL, Tr.binIntOp2IR A.AndOp),
			(A.OrOp, Ty.BOOL, Tr.binIntOp2IR A.OrOp)]
		 | opsForType (Ty.FUNCTION (_, _)) =
			[(A.EqOp, Ty.BOOL, Tr.binIntOp2IR A.EqOp),
			(A.NeqOp, Ty.BOOL, Tr.binIntOp2IR A.NeqOp)]
		 | opsForType _ = []; (* VOID has no allowed operations and ERROR
								 has already been dealt with*)
		val {env = venv', ty = leftTy, ir = (leftInitIR, leftExpIR)} =
			transExp venv tenv level func class left
		val {env = venv', ty = rightTy, ir = (rightInitIR, rightExpIR)} =
			transExp venv' tenv level func class right
		val operation = List.find (fn (oper', resTy, subtree) => oper' = oper) (opsForType leftTy)
		
		val result =
			case (leftTy, rightTy) of
				(Ty.ERROR, _) => errorExp venv'
			  | (_, Ty.ERROR) => errorExp venv'
			  | (leftTy, rightTy) =>
				if equalTypes leftTy rightTy then
					case operation of
						NONE => (err pos ("Error: Cannot apply operator "
							^ PO.asString oper ^ " to operands of type "
							^ PT.asString leftTy);
							errorExp venv')
					  | SOME (oper, resTy, subtree) =>
						{env = venv', 
						 ty = resTy,
						 ir = (Tr.seq2IR [leftInitIR, rightInitIR],
							   [subtree (leftExpIR, rightExpIR)])}
				else
					(err pos ("Type mismatch: Expected type equality of operands for operator "
							^ PO.asString oper ^  " (" ^ PT.asString leftTy ^ " and "
							^ PT.asString rightTy ^ " was given)");
					 errorExp venv')
	in
		result
	end
 |  transExp venv tenv level func class (A.LambdaExp {formals, returnTy, body, pos}) =
		let
			val returnTy' = transTy tenv returnTy
			val (tys, formalsSize) = List.foldl (fn (f, (tys, size)) =>
				let
					val ty = typeOfDecl tenv f
				in
					(tys @ [ty], size + Tr.sizeOfTy ty)
				end
			) ([], 0) formals
			
			val formalsSize' =
				if Tr.sizeOfTy returnTy' > 4 then
					formalsSize + 4
				else formalsSize
			
			val funTy = Ty.FUNCTION (tys, returnTy')
			val captures = ref nil : (Tr.access * Tr.access * Ty.ty) list ref
			val func' = {
				ty = funTy,
				captures = captures
			}
			
			val label = Tr.newLabel "lambda"
			val level' = Tr.newLevel {
				parent = level,
				name = label,
				formals = formalsSize'
			}
			(* Reserve space for forwardee pointer and forwarding function *)
			val forwardee = Tr.allocMember level' 4
			val forwarder = Tr.allocMember level' 4
			
			fun enterParam (decl, (venv, nr)) =
				let
					val {env = (venv', tenv'), ir = _} =
						transDecl venv tenv level' func class (fn (_, ty) =>
							(Tr.accessOfFormal level' nr true (Tr.sizeOfTy ty), E.Public, NONE)
						) decl
				in
					(venv', nr+1)
				end
				
			val (venv', _) = List.foldl enterParam (venv, 1) formals
			val {ir = bodyIR, ...} = transStat venv' tenv level' (SOME func') NONE class body
			val _ = Tr.funEntryExit {level = level', body = bodyIR}
			val (lambdaIR, r1, r2) = Tr.initLambda (level, label, !captures, forwardee, forwarder)
		in
			{env = venv, ty = funTy, ir = (lambdaIR, [r1, r2])}
		end
 |  transExp venv tenv level func class (A.CallOrConsExp {func = funcExp, args, pos}) =
		let
			val (venv', argsTys, argsIRs) = List.foldl (fn (exp, (venv, tyList, irList)) =>
				let
					val {env = venv', ty, ir = (initIR, ir)} = transExp venv tenv level func class exp
				in
					(venv', tyList @ [ty], irList @ [(initIR, ir)])
				end) (venv, [], []) args
			val (argsInitIRs, argsExpIRs) = ListPair.unzip argsIRs
			
			(* GC stuff: Create gc handler routine and push it on the gc
						 handler stack so it is executed in case of a gc. *)
			val gcHandlerPush =
			let
			(* Find all roots reachable from this level that should be copied *)
			val roots = List.mapPartial (fn (_, entry) =>
				case entry of
					E.VarEntry {gcAccess = SOME access, level = level', ty, ...} =>
						if level = level' then SOME (ty, access)
						else NONE
				  | _ => NONE
				) (Symbol.entries venv')
			in
				Tr.pushGCHandler2IR level roots
			end
			(* More GC stuff: We find all pointers that are currently in scope
							  such that we can spill these onto the stack.
							  This is needed so the gc handlers can update the
							  pointer so it points to the correct object after a
							  cheney move *)
			val pointers =
				List.mapPartial (fn (_, entry) =>
					case entry of
						E.VarEntry {access, ty, gcAccess = SOME gcAccess, ...} =>
						(case ty of
							Ty.FUNCTION _ =>
							let
								(* Only fetch the environment pointer *)
								val (level, access') = access
								val envAcc = case access' of
									[_, envAcc] => envAcc
								  | _ => raise Fail "Expected expression of size 2"
							in
								SOME (gcAccess, (level, [envAcc]))
							end
						  | Ty.CLASS _ => SOME (gcAccess, access)
						  | Ty.INTERFACE _ => SOME (gcAccess, access)
						  | Ty.ARRAY _ => SOME (gcAccess, access)
						  | Ty.STRING => SOME (gcAccess, access)
						  | _ => NONE
						)
					  | _ => NONE
				) (Symbol.entries venv')
				
			val store = List.map Tr.move pointers
			val fetch = List.map (fn (a, b) => Tr.move (b, a)) pointers
			
			fun call () =
				let
					val {env = venv'', ty = funcTy, ir = (funcInitIR, funcIR)} =
						transExp venv' tenv level func class funcExp
				in
					case funcTy of
						Ty.ERROR => errorExp venv''
					  | Ty.FUNCTION (formalTys, retTy) =>
						let
							fun checkArgs (formal::formals) (actual::actuals) n =
								if subtype actual formal then
									checkArgs formals actuals (n+1)
								else
									(err pos ("Error: Type mismatch for argument no. " ^
									 Int.toString n ^ ", expected " ^
									 PT.asString formal ^ ", received " ^ PT.asString actual);
									 false)
							  | checkArgs [] [] _ = true
							  | checkArgs _ _ _ =
								(err pos ("Invalid number of arguments for callable expression. Expected: "
								 ^ Int.toString (List.length formalTys)
								 ^ ", but was: " ^ Int.toString (List.length args)); false)
						in
							if checkArgs formalTys argsTys 1 then
								case retTy of
									Ty.VOID =>
									let
										val call = [Tr.procCall2IR (funcIR, List.concat argsExpIRs)]
										val ir = (Tr.seq2IR (gcHandlerPush :: funcInitIR :: argsInitIRs @ store @ call @ fetch), [])
									in
										{env = venv'', ty = Ty.VOID, ir = ir}
									end
								  | t =>
									let
										val (call, rs, access, tmpSym) = Tr.funCall2IR (level, funcIR, List.concat argsExpIRs, Tr.sizeOfTy t)
										(* Save temporary in venv so we can identify it for GC'ing *)
										val venv''' = S.enter (venv'', tmpSym,
											E.VarEntry { access = access,
														 level = level,
														 ty = t,
														 vis = E.Public,
														 gcAccess = case t of
															Ty.CLASS _ => SOME (Tr.allocLocal level true 4)
														  | Ty.INTERFACE _ => SOME (Tr.allocLocal level true 4)
														  | _ => NONE }
										)
									in
										{env = venv''', ty = t, ir = (Tr.seq2IR (gcHandlerPush :: funcInitIR :: argsInitIRs @ store @ call :: fetch), rs)}
									end
							else
								errorExp venv''
						end
					  | _ => (err pos ("Error: Expression of type " ^ PT.asString funcTy ^ " is not callable");
							 errorExp venv'')
				end
		in
			case funcExp of
				A.VarExp (A.SimpleVar (sym, _)) => (
					case S.look (tenv, sym) of
						NONE => call ()
					  | SOME (ty as (Ty.CLASS {name, ...})) =>
						let
							(* Find all constructors *)
							val constructors = 
								case S.look (venv', name) of
									SOME (E.ClassEntry {constructors, ...}) =>
									constructors
								  | _ => []
							
							(* Find those that match the param list *)
							val constructors' = List.filter (fn entry =>
								case entry of
									E.FunEntry {formals, ...} =>
									(List.all (fn (formal, actual) =>
										subtype actual formal
									) (ListPair.zipEq (formals, argsTys))
										handle UnequalLengths => false)
								  | _ => false
								) constructors
							
							(* Find the most specific constructor: The most specific constructor is the constructor
							   that satisfies that (t1, t2, ..., tN) <= (t1', t2', ..., tN') for all constructor
							   param types (t1', t2', ..., tN'). Note that there cannot be more than 1 of these, since
							   the subtype relation is an antisymmetric relation on types (and therefore also on a
							   list of types). *)
							val constructors'' = List.filter (fn entry =>
								case entry of
									E.FunEntry {formals, ...} =>
									List.all (fn entry' =>
										case entry' of
											E.FunEntry {formals = formals', ...} =>
												List.all (fn (f1, f2) =>
													subtype f1 f2
												) (ListPair.zip (formals, formals'))
										  | _ => false
									) constructors'
								  | _ => false
							) constructors'
						in
							(* Report error if there are more than 1 best matching
							   constructor among the user declared ones *)
							if List.null constructors' andalso List.length constructors > 0 then
								(err pos ("Error: No matching constructor of " ^ PT.asString ty);
								{env = venv', ty = ty, ir = (Tr.emptyEx, [])})
							else if List.length constructors'' <> 1 andalso List.length constructors > 0 then
								(err pos ("Ambiguous call to overloaded constructor of " ^ PT.asString ty);
								{env = venv', ty = ty, ir = (Tr.emptyEx, [])})
							else
								let
									(* Build object structure *)
									val (methods, vars, _, vtableLabel) = fields venv' ty
									val (objInit, r, access, tmpSym) = Tr.objConsToIR level (ty, methods,
										List.map (fn (encaps, decl) =>
											case decl of
												E.VarEntry {access, ...} => access
											  | _ => raise Fail "Expected E.VarEntry"
										) vars,
										vtableLabel
									)
									
									(* Save temporary in venv so we can identify it for GC'ing *)
									val gcAccess = Tr.allocLocal level true 4
									val venv'' = S.enter (venv', tmpSym,
										E.VarEntry {access = access,
													level = level,
													ty = ty,
													vis = E.Public,
													gcAccess = SOME gcAccess }
									)
									
									val store' = store @ [Tr.move (gcAccess, access)]
									val fetch' = fetch @ [Tr.move (access, gcAccess)]
									
									(* Perform constructor call if there is a constructor *)
									val consCall = case List.getItem constructors'' of
										SOME (E.FunEntry {label, ...}, _) =>
											store' @ [Tr.procCall2IR ([List.hd (Tr.fun2IR label), r], List.concat argsExpIRs)] @ fetch'
									  | _ => [Tr.emptyEx]
								in
									{env = venv'', ty = ty, ir = (Tr.seq2IR (gcHandlerPush :: store @ objInit :: fetch @ argsInitIRs @ consCall), [r])}
								end
						end
					  | SOME (ty as (Ty.INTERFACE _)) =>
						(err pos ("Error: Cannot instantiate object of type " ^ PT.asString ty); errorExp venv')
					  | SOME ty => (err pos ("Error: Expected class type, received " ^ PT.asString ty); errorExp venv')
				)
			  | _ => call ()
		end
 |  transExp venv tenv level func class (A.ArrayExp {ty, exp, pos}) =
		let
			val {env = venv', ty = expTy, ir = (expInitIR, expIR)} = transExp venv tenv level func class exp
			val ty' = transTy tenv ty
		in
			case expTy of
				Ty.INT => {env = venv', ty = Ty.ARRAY ty', ir = (expInitIR, [Tr.allocArray2IR ty' expIR])}
			  | ty => (err pos ("Type mismatch: Expression expected " ^
				"to be of type int, but was: " ^
				PT.asString ty); errorExp venv')
		end
 |  transExp venv tenv level func class (A.AssignExp {var, exp, pos}) =
		let
			val {env = venv', ty = varTy, ir = (varInitIR, varIRs)} = transVar venv tenv level func class var
			val {env = venv', ty = expTy, ir = (expInitIR, expIRs)} = transExp venv' tenv level func class exp
		in
			if subtype expTy varTy then
				{env = venv',
				 ty = varTy,
				 ir = (Tr.seq2IR [varInitIR, expInitIR],
						[Tr.assign2IR (
							varIRs, expIRs, varTy, fields venv' expTy)]
						)
				}
			else
				(err pos ("Type mismatch: Cannot assign expression of type "
				^ PT.asString expTy ^ " to variable of type " ^ PT.asString varTy);
				errorExp venv')
		end
  | transExp venv tenv level func class (A.PostfixOpExp {exp, oper, pos}) =
	let
		val sOper = PO.asString oper ^ PO.asString oper (* Kinda ugly, but works for now *)
		val {env = venv', ty = varTy, ir = (varInitIR, varExpIR)} = transExp venv tenv level func class exp
	in
		case varTy of
			Ty.ERROR => errorExp venv'
		  | Ty.INT =>
			let val (initIR, expIR) = Tr.intPostfix2IR (oper = A.PlusOp) varExpIR
			in {env = venv', ty = Ty.INT, ir = (Tr.seq2IR (varInitIR :: initIR), expIR)}
			end
		  | Ty.FLOAT =>
			let val (initIR, expIR) = Tr.floatPostfix2IR (oper = A.PlusOp) varExpIR
			in {env = venv', ty = Ty.FLOAT, ir = (Tr.seq2IR (varInitIR :: initIR), expIR)}
			end
		  | ty =>
			(err pos ("Error: Cannot apply operator " ^ sOper ^
				" to expression of type " ^ PT.asString ty);
			 errorExp venv')
	end
  | transExp venv tenv level func class (A.PrefixOpExp {exp, oper, pos}) =
	let
		val sOper = PO.asString oper ^ PO.asString oper
		val {env = venv', ty = varTy, ir = (varInitIR, varExpIR)} = transExp venv tenv level func class exp
	in
		case varTy of
			Ty.ERROR => errorExp venv'
		  | Ty.INT =>
			let val (initIR, expIR) = Tr.intPrefix2IR (oper = A.PlusOp) varExpIR
			in {env = venv', ty = Ty.INT, ir = (Tr.seq2IR (varInitIR :: initIR), expIR)}
			end
		  | Ty.FLOAT =>
			let val (initIR, expIR) = Tr.floatPrefix2IR (oper = A.PlusOp) varExpIR
			in {env = venv', ty = Ty.FLOAT, ir = (Tr.seq2IR (varInitIR :: initIR), expIR)}
			end
		  | ty =>
			(err pos ("Error: Cannot apply operator " ^ sOper ^
				" to expression of type " ^ PT.asString ty);
			 errorExp venv')
	end
 
and transStat venv tenv level func break class (A.VarDeclStat x) =
		let
			val {env = (venv', tenv'), ir = (initIR, expIR)} =
				transDecl venv tenv level func class (fn (_, ty) =>
					(case ty of
						Ty.FUNCTION _ =>
						let val access = Tr.allocLocal level true 8
						in (access, E.Public, SOME access)
						end
					  | Ty.FLOAT => (Tr.allocLocal level false 4, E.Public, NONE)
					  | Ty.CLASS _ => (Tr.allocLocal level false 4, E.Public, SOME (Tr.allocLocal level true 4))
					  | Ty.INTERFACE _ => (Tr.allocLocal level false 4, E.Public, SOME (Tr.allocLocal level true 4))
					  | Ty.ARRAY _ => (Tr.allocLocal level false 4, E.Public, SOME (Tr.allocLocal level true 4))
					  | Ty.STRING => (Tr.allocLocal level false 4, E.Public, SOME (Tr.allocLocal level true 4))
					  | _ => (Tr.allocLocal level false 4, E.Public, NONE))
				) (A.VarDecl x)
		in
			{env = (venv', tenv'), ir = Tr.seq2IR (initIR :: expIR)}
		end
  | transStat venv tenv level func break class (A.ExpStat NONE) =
		{env = (venv, tenv), ir = Tr.emptyNx}
  | transStat venv tenv level func break class (A.ExpStat (SOME exp)) =
		let
			val {ty, ir = (initIR, expIR), ...} = transExp venv tenv level func class exp;
		in
			{env = (venv, tenv), ir = Tr.seq2IR (initIR :: expIR)}
		end
  | transStat venv tenv level func break class (A.CompoundStat stats) =
		let
			fun f (stat, {env = (venv, tenv), ir = ir}) =
				let
					val {env = (venv', tenv'), ir = ir'} =
						transStat venv tenv level func break class stat
				in
					{env = (venv', tenv'), ir = Tr.seq2IR [ir, ir']}
				end
			val {env = _, ir} = List.foldl f {env = (venv, tenv), ir = Tr.emptyNx} stats
		in
			{env = (venv, tenv), ir = ir}
		end
  | transStat venv tenv level func break class (A.SelectionStat {test, ifBody, elseBody = NONE, pos}) =
		let
			val {ty = testTy, ir = (testInitIR, testExpIR), ...} = transExp venv tenv level func class test
			val _ = case testTy of
					Ty.ERROR => ()
				  | Ty.BOOL => ()
				  | t => err pos ("Type mismatch: Expected expression of type bool, but was "
						^ PT.asString testTy)
			val {ir = bodyIR, ...} = transStat venv tenv level func break class ifBody
		in
			{env = (venv, tenv), ir = Tr.seq2IR [testInitIR, Tr.if2IR testExpIR bodyIR]}
		end
  | transStat venv tenv level func break class (A.SelectionStat {test, ifBody, elseBody = SOME elseBody, pos}) =
		let
			val {ty = testTy, ir = (testInitIR, testExpIR), ...} = transExp venv tenv level func class test;
			val _ = case testTy of
					Ty.ERROR => ()
				  | Ty.BOOL => ()
				  | t => err pos ("Type mismatch: Expected expression of type bool, but was "
						^ PT.asString testTy)
						
			val trStat = transStat venv tenv level func break class
			val {ir = bodyIR, ...} = trStat ifBody
			val {ir = elseIR, ...} = trStat elseBody
		in
			{env = (venv, tenv), ir = Tr.seq2IR [testInitIR, Tr.ifElse2IR testExpIR bodyIR elseIR]}
		end
  | transStat venv tenv level (x as (SOME {ty = funcTy as Ty.FUNCTION (_, returnTy), ...}))
	break class (A.ReturnStat (SOME exp, pos)) =
		let
			val label = Tr.frameLabel level
			val {ty = expTy, ir = (expInitIR, expIR), ...} = transExp venv tenv level x class exp
			val _ = case (returnTy, expTy) of
				(Ty.ERROR, _) => ()
			  | (_, Ty.ERROR) => ()
			  | (t, t') => if not (subtype t' t) then
							(err pos ("Type mismatch: Cannot return expression of type "
							^ PT.asString t'
							^ " from function of type " ^ PT.asString funcTy))
						else ()
		in
			{env = (venv, tenv), ir = Tr.seq2IR [expInitIR, Tr.return2IR level label (SOME expIR)]}
		end
  | transStat venv tenv level (SOME {ty = funcTy as Ty.FUNCTION (_, returnTy), ...})
	break class (A.ReturnStat (NONE, pos)) =
		let
			val label = Tr.frameLabel level
			val _ = case returnTy of
				Ty.ERROR => ()
			  | Ty.VOID => ()
			  | t => (err pos ("Type mismatch: Function of type " ^ PT.asString funcTy
					^ " must return a value of type "
					^ PT.asString returnTy))
		in
			{env = (venv, tenv), ir = Tr.return2IR level label NONE}
		end
  | transStat venv tenv level _ break class (A.ReturnStat (_, pos)) =
		let
			val _ = err pos "Cannot return outside function"
		in
			{env = (venv, tenv), ir = Tr.emptyEx}
		end
  | transStat venv tenv level func (SOME break) class (A.BreakStat pos) =
		let
			val breakIR = Tr.break2IR break
		in
			{env = (venv, tenv), ir = breakIR}
		end
  | transStat venv tenv level func NONE class (A.BreakStat pos) =
		let
			val _ = err pos "Error: Break statements must only occur inside loops"
		in
			{env = (venv, tenv), ir = Tr.emptyNx}
		end
  | transStat venv tenv level func break class (A.IterationStat {init = NONE, test, incr, body, pos}) =
		let
			val testIR = case test of
				NONE => NONE
			  | SOME test =>
				let
					val {ty = testTy, ir = testIR, ...} =
						transExp venv tenv level func class test
				in
					case testTy of
						Ty.ERROR => NONE
					  | Ty.BOOL => SOME testIR
					  | t =>
						(err pos ("Type mismatch: Conditional expression must be of type bool, but was "
						 ^ PT.asString t);
						 NONE)
				end
			val incrIR = case incr of
				NONE => NONE
			  | SOME incr =>
				let
					val {ty = _, ir = incrIR, ...} =
						transExp venv tenv level func class incr
				in
					SOME incrIR
				end
			  
			val doneLabel = Tr.newLabel "loop_done"
			val {ir = bodyIR, ...} = transStat venv tenv level func (SOME doneLabel) class body
			
			val bodyIR' = case incrIR of
				NONE => bodyIR
			  | SOME (incrInitIR, incrIR) => Tr.seq2IR ([bodyIR, incrInitIR] @ incrIR)
		in
			{env = (venv, tenv), ir = Tr.iteration2IR NONE testIR bodyIR' doneLabel}
		end
  | transStat venv tenv level func break class
	(A.IterationStat { init = SOME (A.Decl (x as {var, ty, exp, pos = initPos}))
					 , test, incr, body, pos}) =
		let
			val {env = (venv', tenv'), ir = initIR} =
				transDecl venv tenv level func class (fn (_, ty) =>
					(case ty of
						Ty.FUNCTION _ => (Tr.allocLocal level true 8, E.Public, NONE)
					  | Ty.FLOAT => (Tr.allocLocal level true 4, E.Public, NONE)
					  | Ty.CLASS _ => (Tr.allocLocal level false 4, E.Public, SOME (Tr.allocLocal level true 4))
					  | Ty.INTERFACE _ => (Tr.allocLocal level false 4, E.Public, SOME (Tr.allocLocal level true 4))
					  | _ => (Tr.allocLocal level false 4, E.Public, NONE))
				) (A.VarDecl x)
				
			val testIR = case test of
				NONE => NONE
			  | SOME test =>
				let
					val {ty = ty, ir = testIR, ...} =
						transExp venv' tenv' level func class test
				in
					case ty of
						Ty.ERROR => NONE
					  | Ty.BOOL => SOME testIR
					  | t =>
						(err pos ("Type mismatch: Condition expression must be of type bool, but was "
						 ^ PT.asString t);
						 NONE)
				end
			val incrIR = case incr of
				NONE => NONE
			  | SOME incr =>
				let
					val {ty = _, ir = incrIR, ...} =
						transExp venv' tenv' level func class incr
				in
					SOME incrIR
				end
			
			val doneLabel = Tr.newLabel "loop_done"
			val {ir = bodyIR, ...} = transStat venv' tenv' level func (SOME doneLabel) class body
			
			val bodyIR' = case incrIR of
				NONE => bodyIR
			  | SOME (incrInitIR, incrExpIR) => Tr.seq2IR ([bodyIR, incrInitIR] @ incrExpIR)
		in
			{env = (venv, tenv), ir = Tr.iteration2IR (SOME initIR) testIR bodyIR' doneLabel}
		end
  | transStat venv tenv level func break class
	(A.IterationStat {init = SOME (A.Exp init'), test, incr, body, pos}) =
		let
			val {ty = _, ir = initIR, ...} =
				transExp venv tenv level func class init'
			val testIR = case test of
				NONE => NONE
			  | SOME test =>
				let
					val {ty = ty, ir = testIR, ...} =
						transExp venv tenv level func class test
				in
					case ty of
						Ty.ERROR => NONE
					  | Ty.BOOL => SOME testIR
					  | t =>
						(err pos ("Type mismatch: Condition expression must be of type bool, but was "
						 ^ PT.asString t);
						 NONE)
				end
			val incrIR = case incr of
				NONE => NONE
			  | SOME incr =>
				let
					val {ty = ty, ir = incrIR, ...} =
						transExp venv tenv level func class incr
				in
					SOME incrIR
				end
			  
			val doneLabel = Tr.newLabel "loop_done"
			val {ir = bodyIR, ...} = transStat venv tenv level func (SOME doneLabel) class body
			
			val bodyIR' = case incrIR of
				NONE => bodyIR
			  | SOME (incrInitIR, incrExpIR) => Tr.seq2IR ([bodyIR, incrInitIR] @ incrExpIR)
		in
			{env = (venv, tenv), ir = Tr.iteration2IR (SOME initIR) testIR bodyIR' doneLabel}
		end;

end (* Semant *)
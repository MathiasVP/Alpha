structure Absyn =
struct

structure S = Symbol

type pos = int

datatype var = SimpleVar of S.symbol * pos
             | SubscriptVar of exp * exp * pos
			 | FieldVar of exp * S.symbol * pos
			 
and encapsulation = PUBLIC | PROTECTED | PRIVATE

and exp = VarExp of var
		| IntExp of int
		| StringExp of string
		| CharExp of string
		| FloatExp of real
		| BoolExp of bool
		| ThisExp
		| ArrayExp of arraydata
		| UnOpExp of unopdata
		| BinOpExp of binopdata
		| LambdaExp of lambdadata
		| CallOrConsExp of calldata
		| AssignExp of assigndata
		| PostfixOpExp of postfixopdata
		| PrefixOpExp of prefixopdata
				
and stat	= VarDeclStat of vardecldata
			| ExpStat of exp option
			| CompoundStat of stat list
			| SelectionStat of selectiondata
			| ReturnStat of exp option * pos
			| BreakStat of pos
			| IterationStat of iterationdata

and decl	= FunctionDecl of fundecldata
			| VarDecl of vardecldata
			| InterfaceDecl of interfacedecldata
			| ClassDecl of classdecldata
			
and oper	= PlusOp | MinusOp
			| TimesOp | DivideOp
			| AndOp | OrOp
			| EqOp | NeqOp
			| LtOp | LeOp | GtOp | GeOp
			| BangOp | UminusOp

and ty		= NameTy of (S.symbol * pos)
			| FunTy of funtydata
			| ArrayTy of ty
			
and iterationinit = Decl of vardecldata
				  | Exp of exp

withtype binopdata = { left: exp
					 , oper: oper
					 , right: exp
					 , pos: pos }
					 
and unopdata = { exp: exp
			   , oper: oper
			   , pos: pos }
				  
and lambdadata = { formals: decl list
				 , returnTy: ty
				 , body: stat
				 , pos: pos }
				 
and arraydata = { ty: ty
				, exp: exp
				, pos: pos }
				 
and funtydata =	{ formalTys: ty list
				, returnTy: ty
				, pos: pos }
				 
and calldata = { func: exp
				, args: exp list
				, pos: pos}
				  
and	assigndata  = { var: var
				  , exp: exp
				  , pos: pos }
				  
and postfixopdata = { exp: exp
					, oper: oper
					, pos: pos }

and prefixopdata = { exp: exp
					, oper: oper
					, pos: pos }
				  
and vardecldata = { var: S.symbol
				  , ty: ty option
				  , exp: exp option
				  , pos: pos}
				
and interfacedecldata = { name: S.symbol
						, extends: S.symbol option
						, body:
							{ name: S.symbol
							, formals: decl list
							, returnTy: ty
							, pos: pos} list
						, pos: pos }
						
and classdecldata = { name: S.symbol
					, extends: S.symbol option
					, implements: S.symbol list
					, body: (encapsulation * decl) list
					, pos: pos}
				  
and selectiondata = { test: exp
					, ifBody: stat
					, elseBody: stat option
					, pos: pos}
					
and iterationdata = { init: iterationinit option
					, test: exp option
					, incr: exp option
					, body: stat
					, pos: pos}
					
and fundecldata = { name: S.symbol
				  , formals: decl list
				  , returnTy: ty option
				  , body: stat
				  , pos: pos }
					
fun visitString (zero, newline, tab, cr, x, accum, map, base) wide str =
	let
		fun f (#"\\" :: cdr) =
			(case cdr of
				#"0" :: cdr' => accum (zero (), if wide then accum (zero (), f cdr') else f cdr')
			  | #"n" :: cdr' => accum (newline (), if wide then accum (zero (), f cdr') else f cdr')
			  | #"t" :: cdr' => accum (tab (), if wide then accum (zero (), f cdr') else f cdr')
			  | #"r" :: cdr' => accum (cr (), if wide then accum (zero (), f cdr') else f cdr')
			  | #"\\" :: cdr' => accum (map #"\\", if wide then accum (zero (), f cdr') else f cdr')
			  | #"\"" :: cdr' => accum (map #"\"", if wide then accum (zero (), f cdr') else f cdr')
			  | #"'" :: cdr' => accum (map #"'", if wide then accum (zero (), f cdr') else f cdr')
			  | #"x" :: a :: b :: c :: d :: cdr' => accum (x (a, b, c, d), f cdr')
			  | _ => raise Fail "Unexpected escape sequence")
		  | f (a::b::c::cdr) =
			let
				val conv = Int.toLarge o Char.ord
				val a' = conv a
				val b' = conv b
				val c' = conv c
				(* unconv is the inverse of conv. ie unconv (conv a) = a *)
				val unconv = Char.chr o Int.fromLarge
			in
				case (IntInf.andb (a', 0x80), IntInf.andb (a', 0x20), IntInf.andb (a', 0x10)) of
					(0, _, _) => accum (map a, if wide then accum (zero (), f (b::c::cdr)) else f (b::c::cdr)) (* U+0000 to U+007F *)
				  | (_, 0, _) =>
					let (* U+0080 to U+07FF *)
						val ch1 = IntInf.andb (a', 0x1C)
						val ch2 = IntInf.orb (IntInf.<< (IntInf.andb (a', 0x3), Word.fromInt 6), IntInf.andb (b', 0x3F))
					in
						accum (map (unconv ch2), accum (map (unconv ch1), f (c::cdr)))
					end
				  | (_, _, 0) =>
					let (* U+0800 to UU+FFFF *)
						val ch1 = IntInf.andb (IntInf.orb (IntInf.<<(a', Word.fromInt 4), (IntInf.~>> (IntInf.andb (b', 0x3C), Word.fromInt 2))), 0xFF)
						val ch2 = IntInf.andb (IntInf.orb (IntInf.<< (IntInf.andb (b', 0x3), Word.fromInt 6), IntInf.andb (c', 0x3F)), 0xFF)
					in
						accum (map (unconv ch2), accum (map (unconv ch1), f cdr))
					end
				  | _ => raise Fail "Unexpected utf-8 encoding"
			end
		  | f (a::b::cdr) =
			let
				val conv = Int.toLarge o Char.ord
				val a' = conv a
				val b' = conv b
				val unconv = Char.chr o Int.fromLarge
			in
				case (IntInf.andb (a', 0x80), IntInf.andb (a', 0x20)) of
					(0, _) => accum (map a, if wide then accum (zero (), f (b::cdr)) else f (b::cdr)) (* U+0000 to U+007F *)
				  | (_, 0) =>
					let (* U+0080 to U+07FF *)
						val ch1 = IntInf.andb (a', 0x1C)
						val ch2 = IntInf.orb (IntInf.<< (IntInf.andb (a', 0x3), Word.fromInt 6), IntInf.andb (b', 0x3F))
					in
						accum (map (unconv ch2), accum (map (unconv ch1), f cdr))
					end
			end
		  | f (a::cdr) = accum (map a, if wide then accum (zero (), f cdr) else f cdr) (* U+0000 to U+007F *)
		  | f [] = base
	in
		f (String.explode str)
	end
					
end (* Absyn *)


structure Translate =
struct

structure F = X86Frame
structure A = Absyn
structure T = Tree
structure PT = PrintTree(F)

exception Bug of string

val err = ErrorMsg.error

datatype level =
         Top
       | Level of {frame: F.frame, parent: level} * unit ref

type frame = {frame: F.frame, parent: level}

type access = level * F.access list

datatype exp = Ex of Tree.exp
             | Nx of Tree.stm
             | Cx of Temp.label * Temp.label -> Tree.stm

type breakpoint = Tree.label

type frag = F.frag

local
    val frags: (frag list) ref = ref []
in
    fun addFrag frag = (frags := frag::(!frags))
    fun getFrags () = !frags
end

val outermost = Top

(* ---------- Printing ---------- *)

fun asStringLevel Top = Symbol.name Temp.topLabel
  | asStringLevel (Level ({frame, parent}, _)) =
    "Level {frame = " ^
    F.asStringFrame frame ^
    ", parent = " ^
    asStringLevel parent ^
    "}"

fun asStringAccess (level, access) =
    "(" ^
    asStringLevel level ^
    ", " ^
    List.foldl (fn (acc, s) => F.asStringAccess acc ^ ", " ) "" access ^
    ")"

fun asStringExp (Ex t) = "Ex(" ^ PT.asStringExp t ^ ")"
  | asStringExp (Nx t) = "Nx(" ^ PT.asStringStm t ^ ")"
  | asStringExp (Cx f) =
    let
        val labelTrue = Temp.newLabel "true_label"
        val labelFalse = Temp.newLabel "false_label"
    in
        "Cx(" ^ PT.asStringStm (f (labelTrue, labelFalse)) ^ ")"
    end

fun printX asStringX (outstream, x) =
    ( TextIO.output (outstream, asStringX x ^ "\n")
    ; TextIO.flushOut outstream)

val printLevel  = printX asStringLevel
val printAccess = printX asStringAccess
val printExp    = printX asStringExp

fun printFrags frags =
	List.app (fn x =>
		let
			val _ = case x of
				F.PROC {body, frame} => print (PT.asStringStm body ^ "\n\n")
			  | F.STRING (label, s) => print (Symbol.name label ^ ": \"" ^ s ^ "\"\n\n")
			  | F.NUMBER (label, s) => print (Symbol.name label ^ ": " ^ s ^ "\n\n")
			  | F.GLOBAL (sym, _) => print (Symbol.name sym ^ "\n\n")
			  | F.TABLE (label, labels) => print (Symbol.name label ^
				": [" ^ String.concat (List.map (fn lab => Symbol.name lab) labels) ^ "]")
		in
			()
		end
	) frags
	
	
fun sizeOfTy (Types.FUNCTION _) = 8
  | sizeOfTy _ = 4

fun newLabel s = Temp.newLabel s

fun newLevel {parent=l, name=n, formals=f} =
    let
        val frame = F.newFrame {name = n, formals = f}
    in
        Level ({frame = frame, parent = l}, ref ())
    end
	
fun name Top = "top"
  | name (Level ({frame, ...}, _)) = Symbol.name (F.name frame)

fun allocLocal Top _ size =
    raise Bug "attempt to allocate local variable in top scope"
  | allocLocal (l as Level ({frame, parent}, _)) b size =
    (l, List.tabulate (size div 4, (fn _ => F.allocLocal frame b)))
(* TODO: Change all 4s (representing bytes) into 1s (representing words)? *)

fun allocMember Top size =
	raise Fail "attempt to allocate member variable in top scope"
  | allocMember (l as Level ({frame, ...}, _)) size =
	(l, List.tabulate (size div 4, fn _ => F.allocMember frame))
	
fun allocGlobal level sym writable =
	let
		val _ = addFrag (F.GLOBAL (sym, writable))
	in
		(level, [F.allocGlobal sym writable])
	end

fun allocVtableEntry Top offset interfaceEntry =
	raise Fail "attempt to allocate vtable entry in top scope"
  | allocVtableEntry level offset interfaceEntry =
	(level, [F.allocVtableEntry offset interfaceEntry])
	
fun accessOfFormal l nr escaping size =
    (l, List.tabulate (size div 4, fn n => F.accessOfFormal (nr + n) escaping))
	
fun frameLabel Top = raise Bug "Cannot get label from TOP level"
  | frameLabel (level as Level ({frame, parent}, _)) = #name frame

fun seq [] = T.EXP (T.CONST (T.INT 0))
  | seq [s] = s
  | seq (h::t) = T.SEQ (h, seq t)
 
fun relOp2RelBinOp T.REQ = T.BEQ
  | relOp2RelBinOp T.RNEQ = T.BNEQ
  | relOp2RelBinOp T.RLT = T.BLT
  | relOp2RelBinOp T.RGT = T.BGT
  | relOp2RelBinOp T.RLE = T.BLE
  | relOp2RelBinOp T.RGE = T.BGE
 
fun unEx (Ex e) = e
  | unEx (Cx genstm) =
    let
        val t = Temp.newLabel "unEx_t"
        val f = Temp.newLabel "unEx_f"
    in
		(* A CJUMP is easily optimized in x86 (setCC instructions),
		   so let's provide easy-to-optimize IR for the code gen phase *)
		case genstm (t, f) of
			T.INTCJUMP(relop, left, right, _, _) => T.INTBINOP (relOp2RelBinOp relop, left, right)
		  | T.FLOATCJUMP(relop, left, right, _, _) => T.FLOATBINOP (relOp2RelBinOp relop, left, right)
		  | test =>
			let
				val r = Temp.newtemp ()
			in
				T.ESEQ ( seq [T.MOVE (T.TEMP r, T.CONST (T.INT 1))
					   , test
					   , T.LABEL f
					   , T.MOVE (T.TEMP r, T.CONST (T.INT 0))
					   , T.LABEL t]
				, T.TEMP r)
			end
    end
  | unEx (Nx s) = T.ESEQ (s, T.CONST (T.INT 0))

fun unNx (Ex e) = T.EXP e
  | unNx (Cx genstm) = 
    let
        val l = Temp.newLabel "unNx"
    in
        T.SEQ (genstm(l, l), T.LABEL l)
    end
  | unNx (Nx s) = s

fun unCx (Ex (T.CONST (T.INT 0))) = (fn (t, f) => T.JUMP(T.NAME f, [f]))
  | unCx (Ex (T.CONST _)) = (fn (t, f) => T.JUMP(T.NAME t, [t]))
  | unCx (Ex e) = (fn (t, f) => 
    let
        val r = Temp.newtemp()
    in
        seq [T.MOVE (T.TEMP r, e),
			 T.INTCJUMP (T.RNEQ, T.TEMP r, T.CONST (T.INT 0), t, f)]
    end)
  | unCx (Cx genstm) = genstm
  | unCx (Nx _) = raise Bug "Should never call unCx on Nx"

val emptyEx = Ex (T.CONST (T.INT 0))
val emptyNx = Nx (T.EXP (T.CONST (T.INT 0)))

val newBreakPoint = Temp.newLabel

fun jump2IR label =
	Nx (Tree.JUMP (Tree.NAME label, [label]))
	
fun subscript2IR (base, offset, size) =
    let
        val offsetT = Temp.newtemp ()
        val baseT = Temp.newtemp ()
        val negativeL = Temp.newLabel "subs_neg"
        val nonNegativeL = Temp.newLabel "subs_nneg"
        val overflowL = Temp.newLabel "subs_ovf"
        val noOverflowL = Temp.newLabel "subs_novf"
        val base' = unEx base
        val offset' = unEx offset
		
		val results = List.tabulate (size div 4, fn n =>
				Ex (T.MEM (T.INTBINOP (T.PLUS,
									   T.TEMP baseT,
									   T.INTBINOP (T.PLUS,
												   T.TEMP offsetT,
												   T.CONST (T.INT (4*n)))), T.DWORD))
		)
		
		val initIR = seq [
					  T.MOVE (T.TEMP offsetT, offset'),
					  T.MOVE (T.TEMP baseT, base'),
					  T.INTCJUMP (T.RLT,
								  T.TEMP offsetT,
								  T.CONST (T.INT 0),
								  negativeL,
								  nonNegativeL),
					T.LABEL negativeL,
					  T.EXP (T.CALL (T.NAME (Temp.namedLabel "abort"), [])),
					T.LABEL nonNegativeL,
					  T.INTCJUMP (T.RGE,
								  T.TEMP offsetT, 
								  T.MEM (T.INTBINOP (T.MINUS, T.TEMP baseT, T.CONST (T.INT 4)), T.DWORD),
								  overflowL,
								  noOverflowL),
					T.LABEL overflowL,
					  T.EXP (T.CALL (T.NAME (Temp.namedLabel "abort"), [])),
					T.LABEL noOverflowL,
					  T.MOVE (T.TEMP offsetT,
							  T.INTBINOP (T.MUL,
										  T.TEMP offsetT,
										  T.CONST (T.INT size)))
		]
    in
		(Nx initIR, results)
    end
	
fun stringSubscript2IR (base, offset) =
	let
		val baseT = Temp.newtemp ()
        val offsetT = Temp.newtemp ()
        val negativeL = Temp.newLabel "subs_neg"
        val nonNegativeL = Temp.newLabel "subs_nneg"
		
		val initBase = T.MOVE (T.TEMP baseT, unEx base)
		val initOffset = T.MOVE (T.TEMP offsetT, unEx offset)
		
		val negativeCond = T.INTCJUMP (T.RLT,
									   T.TEMP offsetT,
									   T.CONST (T.INT 0),
									   negativeL,
									   nonNegativeL)

		val result = T.MEM (T.INTBINOP (T.PLUS,
										T.TEMP baseT,
										T.INTBINOP (T.PLUS,
												    T.INTBINOP (T.MUL,
																T.TEMP offsetT,
																T.CONST (T.INT 2)),
												    T.CONST (T.INT 4))), T.WORD)
	in
		Ex (T.ESEQ (seq [
			initBase,
			initOffset,
			negativeCond,
			T.LABEL negativeL,
			T.EXP (T.CALL (T.NAME (Temp.namedLabel "abort"), [])),
			T.LABEL nonNegativeL
		], result))
	end
	
fun memberInClass exp (level, access) =
	let
		val exp' = unEx exp
	in
		List.map (fn acc => Ex (F.memberInClass exp' acc)) access
	end
	
fun levelEq (Level (_, u1), Level (_, u2)) = (u1 = u2)
  | levelEq _ = false

fun simpleVar ((toLevel, access)) = List.map (fn acc => Ex (F.exp acc (T.TEMP F.FP))) access

fun table2IR name labels =
	let
		val label = Temp.newLabel name
	in
		addFrag (F.TABLE (label, labels));
		label
	end
	
fun intPostfix2IR incr exp =
	let
		val rs = List.map unEx exp
		val ts = List.tabulate (List.length exp, fn _ => Temp.newtemp ())
		
		val instrs = List.concat (List.map (fn (r, t) =>
			[Nx (T.MOVE (T.TEMP t, r)),
			 Nx (T.MOVE (r, T.INTBINOP (
				if incr then T.PLUS else T.MINUS,
				r,
				T.CONST (T.INT 1))))
			]) (ListPair.zip (rs, ts)))
	in
		(instrs, List.map (fn t => Ex (T.TEMP t)) ts)
	end
	
fun floatPostfix2IR incr exp =
	let
		val rs = List.map unEx exp
		val ts = List.tabulate (List.length exp, fn _ => Temp.newtemp ())
		
		val instrs = List.concat (List.map (fn (r, t) =>
			[Nx (T.MOVE (T.TEMP t, r)),
			 Nx (T.MOVE (r, T.INTBINOP (
				if incr then T.PLUS else T.MINUS,
				r,
				T.CONST (T.FLOAT 1.0))))
			]) (ListPair.zip (rs, ts)))
	in
		(instrs, List.map (fn t => Ex (T.TEMP t)) ts)
	end
	
fun intPrefix2IR incr exps =
	let
		val rs = List.map unEx exps
		val instrs = List.map (fn r =>
			Nx (T.MOVE (r,
					T.INTBINOP (
						if incr then T.PLUS else T.MINUS,
						r,
						T.CONST (T.INT 1))))
		) rs
	in
		(instrs, exps)
	end
	
fun floatPrefix2IR incr exps =
	let
		val rs = List.map unEx exps
		val instrs = List.map (fn r =>
			Nx (T.MOVE (r,
					T.INTBINOP (
						if incr then T.PLUS else T.MINUS,
						r,
						T.CONST (T.FLOAT 1.0))))
		) rs
	in
		(instrs, exps)
	end

fun not exp = Ex (T.INTBINOP (T.XOR, unEx exp, T.CONST (T.INT 1)))

fun intNeg exp = Ex (T.INTBINOP (T.MINUS, T.CONST (T.INT 0), unEx exp))

(* Not very pretty, since we're representing negation of floats by
   0 - floating value instead of 0.0 - floating value, but we can't
   pattern match on reals in SML *)
fun floatNeg exp = Ex (T.FLOATBINOP (T.MINUS, T.CONST (T.INT 0), unEx exp))

(* Convert a class object to an instance of a base class,
   by adding a constant to the pointer pointing to the object *)
fun convert exps (_, _, tyOffsets, _) toTy =
	case (exps, toTy) of
		([exp], Types.INTERFACE _) =>
			(case List.find (fn (ty, offset) => ty = toTy) tyOffsets of
				SOME (_, offset) => [Ex (T.INTBINOP (T.PLUS,
							T.MEM (unEx exp, T.DWORD),
							T.CONST (T.INT offset)))]
			  | NONE => raise Fail "Type offset not found for implicit cast")
	  | (exps, _) => exps
	

fun assign2IR (vars, exps, ty, fields) =
    let
		(* Do possible base-class conversion *)
		val exps' = convert exps fields ty
		val moves = List.foldl (fn ((var, exp), moves) =>
			moves @ [T.MOVE (unEx var, unEx exp)]
		) [] (ListPair.zipEq (vars, exps'))
    in
        Nx (seq moves)
    end

fun this2IR level = simpleVar (accessOfFormal level 0 true 4)
	
fun break2IR break =
    Nx (T.JUMP (T.NAME break, [break]))

fun int2IR i = Ex (T.CONST (T.INT i))

fun float2IR r = Ex (T.CONST (T.FLOAT r))

fun bool2IR true = Ex (T.CONST (T.INT 1))
  | bool2IR false = Ex (T.CONST (T.INT 0))
	
fun string2IR str =
    let
		fun one _ = 1
		fun two _ = 2
		(* Add 2 for the zero terminat0r! *)
		val strlen = A.visitString (one, one, one, one, two, op+, one, 2) true
        val label = Temp.newLabel "string"
		val r = Temp.newtemp ()
		(* Add 4 for the forwardee *)
		val alloc = T.CALL (T.NAME (Temp.namedLabel "allocate"), [T.CONST (T.INT (strlen str + 4))])
		val strcpy = T.EXP (T.CALL (T.NAME (Temp.namedLabel "_StrCpyW"), [T.INTBINOP (T.PLUS, T.TEMP r, T.CONST (T.INT 4)), T.NAME label]))
    in
        addFrag (F.STRING (label, str));
        Ex (T.ESEQ (seq [
			T.MOVE (T.TEMP r, alloc),
			strcpy
		], T.TEMP r))
    end
	
fun char2IR str =
	let
		(* Convert the (possibly escaped) charater literal into a hex string *)
		val format = A.visitString (fn _ => "0",
									fn _ => "0a",
									fn _ => "09",
									fn _ => "0d",
									fn (a, b, c, d) => (String.implode [a, b, c, d]),
									fn (a, b) => b ^ a,
									(Int.fmt StringCvt.HEX) o Char.ord,
									"") false
		val _ = print (format str ^ "\n")
	in
		Ex (T.CONST (T.INT (Option.valOf (StringCvt.scanString (Int.scan StringCvt.HEX) (format str)))))
	end

fun if2IR [testExp] thenExp =
    let
        val test' = unCx testExp
        val labelThen = Temp.newLabel "if_then"
        val labelEnd = Temp.newLabel "if_end"
    in
		(* This should only be able to be statements actually? *)
        case (test', thenExp)
         of (_, Cx func) =>
            Cx (fn (t, f) =>
                   seq [ test' (labelThen, labelEnd)
                       , T.LABEL labelThen
                       , func (t, f)
                       , T.LABEL labelEnd])
          | (_, Nx _) =>
            Nx (seq [ test' (labelThen, labelEnd)
                       , T.LABEL labelThen
                       , unNx thenExp
                       , T.LABEL labelEnd])
          | (_, Ex ex) =>
            Nx (seq [ test' (labelThen, labelEnd)
                       , T.LABEL labelThen
                       , T.EXP ex
                       , T.LABEL labelEnd])
    end
  | if2IR _ _ = emptyEx

fun ifElse2IR [testExp] thenExp elseExp =
    let
        val test' = unCx testExp;
        val labelThen = Temp.newLabel "if_then";
        val labelElse = Temp.newLabel "if_else";
        val labelJoin = Temp.newLabel "if_join";
		
		val cxCase = Cx (fn (t, f) => 
			seq [test' (labelThen, labelElse),
				 T.LABEL labelThen,
				 unCx thenExp (t, f),
				 T.JUMP (T.NAME labelJoin, [labelJoin]),
				 T.LABEL labelElse,
				 unCx elseExp (t, f),
				 T.LABEL labelJoin])
    in
		(* This should only be able to be statements actually? *)
		case (test', thenExp, elseExp)
			 of (_, Cx _, Cx _) => cxCase
			  | (_, Cx _, Ex _) => cxCase
			  | (_, Ex _, Cx _) => cxCase
			  | (_, Ex _, Ex _) =>
				let
					val r = Temp.newtemp ()
				in
					Ex (T.ESEQ (seq [test' (labelThen, labelElse),
								  T.LABEL labelThen,
								  T.MOVE (T.TEMP r, unEx thenExp),
								  T.JUMP (T.NAME labelJoin, [labelJoin]),
								  T.LABEL labelElse,
								  T.MOVE (T.TEMP r, unEx elseExp),
								  T.LABEL labelJoin],
							  T.TEMP r))
				end
			  | (_, Nx _, Nx _) =>
				 Nx (seq [test' (labelThen, labelElse),
								  T.LABEL labelThen,
								  unNx thenExp,
								  T.JUMP (T.NAME labelJoin, [labelJoin]),
								  T.LABEL labelElse,
								  unNx elseExp,
								  T.LABEL labelJoin])
			  | (_, _, _) =>
				raise Bug "encountered thenBody and elseBody of different kinds"
    end
  | ifElse2IR _ _ _ = emptyEx
	
fun iteration2IR (SOME (initInit, init)) (SOME (testInit, [test])) body doneLabel =
	let
        val init' = seq ((unNx initInit) :: (List.map unNx init))
        val test' = unCx test
		val testInit' = unNx testInit
        val body' = unNx body
        val labelTest = Temp.newLabel "loop_test"
        val labelBody = Temp.newLabel "loop_body"
    in
        Nx (seq [init',
			T.LABEL labelTest,
			testInit',
			test' (labelBody, doneLabel),
			T.LABEL labelBody,
			body',
			T.JUMP (T.NAME labelTest, [labelTest]),
			T.LABEL doneLabel])
    end
  | iteration2IR NONE (SOME (testInit, [test])) body doneLabel =
	let
        val test' = unCx test
        val testInit' = unNx testInit
        val body' = unNx body
        val labelTest = Temp.newLabel "loop_test"
        val labelBody = Temp.newLabel "loop_body"
    in
        Nx (seq [T.LABEL labelTest,
			testInit',
			test' (labelBody, doneLabel),
			T.LABEL labelBody,
			body',
			T.JUMP (T.NAME labelTest, [labelTest]),
			T.LABEL doneLabel])
    end
  | iteration2IR (SOME (initInit, init)) NONE body doneLabel =
	let
		val init' = seq ((unNx initInit) :: (List.map unNx init))
        val body' = unNx body
        val labelBody = Temp.newLabel "loop_body"
    in
        Nx (seq [init',
			T.LABEL labelBody,
			body',
			T.JUMP (T.NAME labelBody, [labelBody])])
    end
  | iteration2IR NONE NONE body doneLabel =
	let
        val body' = unNx body
        val labelBody = Temp.newLabel "loop_body"
    in
        Nx (seq [T.LABEL labelBody,
			body',
			T.JUMP (T.NAME labelBody, [labelBody])])
    end
  | iteration2IR _ _ _ _ = raise Fail "Invalid combination of option type values for iteration2IR"
	
local
	fun RelA2T A.EqOp = T.REQ
	  | RelA2T A.NeqOp = T.RNEQ
	  | RelA2T A.LtOp = T.RLT
	  | RelA2T A.LeOp = T.RLE
	  | RelA2T A.GtOp = T.RGT
	  | RelA2T A.GeOp = T.RGE
	  | RelA2T _ = raise Fail "Invalid relational operator"
	  
	fun BinA2T A.PlusOp = T.PLUS
	  | BinA2T A.MinusOp = T.MINUS
	  | BinA2T A.DivideOp = T.DIV
	  | BinA2T A.TimesOp = T.MUL
	  | BinA2T A.AndOp = T.AND
	  | BinA2T A.OrOp = T.OR
	  | BinA2T _ = raise Fail "Invalid binary operator"
	  
	fun isOperator A.PlusOp = true
	  | isOperator A.MinusOp = true
	  | isOperator A.DivideOp = true
	  | isOperator A.TimesOp = true
	  | isOperator A.AndOp = true
	  | isOperator A.OrOp = true
	  | isOperator _ = false
	  
	  fun intOp2IR' (oper, l, r) = Ex (T.INTBINOP (BinA2T oper, unEx l, unEx r))
	  fun floatOp2IR' (oper, l, r) = Ex (T.FLOATBINOP (BinA2T oper, unEx l, unEx r))
	  
	  fun op2ir oper ([left], [right]) caseOp caseRel =
		if isOperator oper then caseOp (oper, left, right)
		else Cx (fn (t, f) => caseRel (oper, left, right, t, f))
	  | op2ir oper (left, right) caseOp caseRel = 
		if isOperator oper then emptyEx
		else
			Cx (fn (t, f) =>
				seq (List.concat (List.map (fn (l, r) =>
					let
						val label = Temp.newLabel "continue"
					in
						[caseRel (oper, l, r, label, f), T.LABEL label]
					end) (ListPair.zipEq (left, right))) @ [T.JUMP (T.NAME t, [t])])
			)
in

	fun binIntOp2IR oper (left, right) =
		op2ir oper (left, right) intOp2IR'
		(fn (oper, left, right, t, f) =>
			T.INTCJUMP (RelA2T oper, unEx left, unEx right, t, f))
	  
	fun binRealOp2IR oper (left, right) =
		op2ir oper (left, right) floatOp2IR'
		(fn (oper, left, right, t, f) =>
			T.FLOATCJUMP (RelA2T oper, unEx left, unEx right, t, f))
end

fun return2IR level label (SOME [exp]) =
	let
		val label' = Temp.namedLabel ((Symbol.name label) ^ "_end")
	in
		Nx (seq [
			T.MOVE (T.TEMP F.RV, unEx exp),
			T.JUMP (T.NAME label', [label'])
		])
	end
  | return2IR level label NONE =
	let
		val label' = Temp.namedLabel ((Symbol.name label) ^ "_end")
	in
		Nx (T.JUMP (T.NAME label', [label']))
	end
  | return2IR level label (SOME exps) =
	let
		val n = 4 * List.length exps
		val label' = Temp.namedLabel (Symbol.name label ^ "_end")
		val dst = case simpleVar (accessOfFormal level 1 true 4) of
			[dst] => unEx dst
		  | _ => raise Fail "Expected 1 expression"
		val t = Temp.newtemp ()
		val (_, moves) = List.foldl (fn (exp, (offset, moves)) =>
			(offset + 4,
				moves @
					[T.MOVE (
						T.MEM (
							T.INTBINOP (T.PLUS,
										T.TEMP t,
										T.CONST (T.INT (n - offset))), T.DWORD),
					unEx exp
				)]
			)
		) (4, []) exps
	in
		Nx (seq (T.MOVE (T.TEMP t, dst) :: moves @ [T.JUMP (T.NAME label', [label'])]))
	end

fun seq2IR [] =
    let
        val mtseqLabel = Temp.newLabel "mtseq"
    in
        Nx (T.LABEL mtseqLabel)
    end
  | seq2IR [exp] = exp
  | seq2IR (exp :: exps) = Nx (T.SEQ (unNx exp, unNx (seq2IR exps)))

fun relopStr2IR (left, right, str) =
    Ex (F.externalCall (str, [unEx left, unEx right]))

fun stringOp2IR A.EqOp ([left], [right]) = relopStr2IR (left, right, "stringEqual")
  | stringOp2IR A.NeqOp ([left], [right]) = relopStr2IR (left, right, "stringNotEqual")
  | stringOp2IR A.PlusOp ([left], [right]) = Ex (F.externalCall ("strConcat", [unEx left, unEx right]))
  | stringOp2IR _ ([left], [right]) = raise Fail "Illegal operation on strings"
  | stringOp2IR _ (_, _) = raise Fail "Expected 1 expression for each string"

fun entryCall2IR (label, exps) =
	Ex (T.CALL (T.NAME label, List.map unEx exps))

fun fun2IR label = [Ex (T.NAME label), emptyEx]

fun funCall2IR (level, [funcExp, envExp], exps, size) = 
	let
		val funcExp' = unEx funcExp
		val envExp' = unEx envExp
		val (r as (_, acc)) = allocLocal level true size
		val (T.MEM (r'', _)) = F.exp (List.last acc) (T.TEMP F.FP)
		val (init, res, access) = if size > 4 then
			(Ex (T.CALL (funcExp', envExp' :: r'' :: List.map unEx exps)),
			 simpleVar r, r)
		else
			let val res = Temp.newtemp ()
			in
				(Nx (T.MOVE (
					T.TEMP res,
					T.CALL (funcExp', envExp' :: List.map unEx exps))
				 ),
				[Ex (T.TEMP res)],
				(level, [F.accessOfTemp res])
				)
			end
	in
		(init, res, access, Symbol.intSymbol ())
	end
  | funCall2IR _ = raise Fail "Expected function and environment in exp list"
  
fun objConsToIR level (ty, methods, varsAcc, label) =
	let
		val t = Temp.newtemp ()
		(* Calculate the size of the object on the heap. (excluding vtables) *)
		val objSize = List.foldl (fn ((_, acc), size) =>
			(4 * (List.length acc)) + size
		) 4 varsAcc
		val forwardeeAcc = List.hd varsAcc
		val initForwardee = case memberInClass (Ex (T.TEMP t)) forwardeeAcc of
			[exp] => T.MOVE (unEx exp, T.CONST (T.INT 0))
		  | _ => raise Fail "Expected expression of size 1"
		  
		val allocFailedLabel = newLabel "alloc_failed"
		val allocSucceeded = newLabel "alloc_succeeded"
		val allocMem = T.MOVE (T.TEMP t,
						T.CALL (T.NAME (Temp.namedLabel "allocate"),
						[T.CONST (T.INT (objSize))]))
		val setupVTable = (T.MOVE (T.MEM (T.TEMP t, T.DWORD), T.NAME (Option.valOf label)))
		val checkAlloc = T.INTCJUMP (T.REQ,
									  T.TEMP t,
									  T.CONST (T.INT 0),
									  allocFailedLabel,
									  allocSucceeded)
		
		val ir = seq [allocMem, checkAlloc, T.LABEL allocSucceeded, setupVTable, initForwardee, T.LABEL allocFailedLabel]
	in
		(Nx ir, Ex (T.TEMP t), (level, [F.accessOfTemp t]), Symbol.intSymbol ())
	end

fun procCall2IR ([funcExp, envExp], exps) = 
	let
		val funcExp' = unEx funcExp
		val envExp' = unEx envExp
	in
		(* Add the pointer containing closure environment to the arg list *)
		Nx (T.EXP (T.CALL (funcExp', envExp' :: (List.map unEx exps))))
	end
  | procCall2IR (_, _) = emptyEx

fun funEntryExit {level = Level ({frame, parent}, _), body = body} =
    let
        val body' = F.entryExit1 (frame, unNx body)
        val frag = F.PROC {body = body', frame = frame}
    in
        addFrag frag
    end
  | funEntryExit {level = Top, ...} =
    raise Bug "attempt to add function at top level"
	
fun initEntryExit {level = level as Level ({frame, parent}, _), body = body} =
	let
		val frag = F.PROC {body = unNx body, frame = frame}
	in
		addFrag frag
	end
  | initEntryExit {level = Top, ...} =
    raise Bug "Cannot add initialisation code at level = Top"

fun getResult () = getFrags ()

fun move (dst, src) =
	let
		val dst' = case simpleVar dst of
			[exp] => exp
		  | _ => raise Fail "Expected expression of size 1"
		val src' = case simpleVar src of
			[exp] => exp
		  | _ => raise Fail "Expected expression of size 1"
	in
		Nx (T.MOVE (unEx dst', unEx src'))
	end

fun forward2IR level name objSize forwardeeAcc genForwardIR =
	let
		val forwardLabel = newLabel ("forward_" ^ name)
		val level' = newLevel {
			parent = level,
			name = forwardLabel,
			formals = 4
		}
		val obj = Temp.newtemp ()
		val new_obj = Temp.newtemp ()
		(* Get the forwardee pointer *)
		val forwardee = case memberInClass (Ex (T.TEMP obj)) forwardeeAcc of
			[exp] => unEx exp
		  | _ => raise Fail "forward2IR: Expected expression of size 1"
		val initNewObj = T.MOVE (T.TEMP new_obj, forwardee)
		val assignForwardee = T.MOVE (forwardee, T.TEMP new_obj)
		(* First argument to the forward function is ty** *)
		val objIR = T.MEM (unEx (List.hd (simpleVar (accessOfFormal level 0 true 4))), T.DWORD)
		val updateArg = T.MOVE (objIR, T.TEMP new_obj)
		(* The first member in a class is always the forwardee member *)
		val noForwardLabel = newLabel "no_forward"
		val doForwardLabel = newLabel "do_forward"
		val objNotNull = newLabel "not_null"
		val forwardedLabel = newLabel "forwarded"
		val doForwardLabel2 = newLabel "do_forward2"
		val doneLabel = Temp.namedLabel (Symbol.name forwardLabel ^ "_end")
		
		val objNullCond = T.INTCJUMP (T.REQ,
							   T.TEMP obj,
							   T.CONST (T.INT 0),
							   noForwardLabel,
							   objNotNull)
		val containsCond = T.INTCJUMP (T.REQ,
									   T.CALL (
										T.NAME (Temp.namedLabel "inFromSpace"),
										[T.TEMP obj]),
									   T.CONST (T.INT 0),
									   noForwardLabel,
									   doForwardLabel)
		val forwardeeNullCond = T.INTCJUMP (T.REQ,
											T.TEMP new_obj,
											T.CONST (T.INT 0),
											doForwardLabel2,
											forwardedLabel)
		val allocInToSpace = T.MOVE (T.TEMP new_obj,
									 T.CALL (
										T.NAME (Temp.namedLabel "allocInToSpace"),
										[T.CONST (T.INT objSize)]))
		val new_forwardee = case memberInClass (Ex (T.TEMP new_obj)) forwardeeAcc of
			[exp] => unEx exp
		  | _ => raise Fail "forward2IR: Expected expression of size 1"
		val zeroForwardee = T.MOVE (new_forwardee, T.CONST (T.INT 0))
			
		val ir = seq2IR ([
			Nx (T.MOVE (T.TEMP obj, objIR)),					(* obj = *arg *)
			Nx objNullCond, 									(* if obj == nullptr: goto noForwardLabel *)
			Nx (T.LABEL objNotNull),
			Nx containsCond, 									(* if obj is not in from space: goto noForwardLabel *)
			Nx (T.LABEL doForwardLabel),
			Nx initNewObj, 										(* new_obj = obj->forwardee *)
			Nx forwardeeNullCond, 								(* if new_obj is not null: goto forwardedLabel *)
			Nx (T.LABEL doForwardLabel2),
			Nx allocInToSpace,									(* new_obj = alloc object *)
			Nx zeroForwardee]									(* new_obj->forwardee = 0 *)
			@ genForwardIR (new_obj, obj) @ [					(* Forward all members *)
			Nx assignForwardee,									(* obj->forwardee = new_obj *)
			Nx updateArg,										(* *arg = new_obj *)
			Nx (T.LABEL forwardedLabel),
			Nx (T.MOVE (T.TEMP F.RV, T.TEMP new_obj)),			(* return new_obj *)
			Nx (T.JUMP (T.NAME doneLabel, [doneLabel])),
			Nx (T.LABEL noForwardLabel),
			Nx (T.MOVE (T.TEMP F.RV, T.TEMP obj)),				(* return obj *)
			Nx (T.JUMP (T.NAME doneLabel, [doneLabel]))
			]
		)
			
		val _ = funEntryExit {level = level', body = ir}
	in
		forwardLabel
	end
	
local
	fun handleClassOrInterface accessExp =
		let
			(* Remove the MEM since we need to pass a pointer to a pointer
			   to the object to the forward function, such that the object
			   pointer can be modified by the forwarder *)
			val exp = case accessExp of
				[Ex (T.MEM (exp, _))] => exp
			  | _ => raise Fail "pushGCHandler2IR: Expected T.MEM expression of size 1"
			(* Most inner MEM: Get the object, middle MEM: Get vptr, outer MEM: Get gc func *)
			val gc = T.MEM (T.MEM (T.MEM (exp, T.DWORD), T.DWORD), T.DWORD)
		in
			SOME (Ex (T.CALL (gc, [exp])))
		end
in
fun callGCHandler (Types.FUNCTION _, accessExp) =
	let
		(* Lambda layout is:
			(func, env). env = [forwardee pointer, forward function, c1, c2, ..., cN] *)
		val env = case accessExp of
			[_, Ex (T.MEM (env, _))] => env
		  | _ => raise Fail "pushGCHandler2IR: Expected expression of size 2"
		val gc = T.MEM (T.INTBINOP (T.PLUS, T.MEM (env, T.DWORD), T.CONST (T.INT 4)), T.DWORD)
	in
		SOME (Ex (T.CALL (gc, [env])))
	end
  | callGCHandler (Types.ARRAY t, accessExp) =
	let
		val ptr = case accessExp of
			[Ex (T.MEM (exp, _))] => exp 
		  | _ => raise Fail "pushGCHandler2IR: Expected expression of size 1"
		val ptrTmp = Temp.newtemp ()
		val initPtrTmp = T.MOVE (T.TEMP ptrTmp, ptr)
		
		(* TODO: Check if ptrTmp is zero before doing T.MEM? *)
		val memPtrTmp = Temp.newtemp ()
		val initMemPtrTmp = T.MOVE (T.TEMP memPtrTmp,
									T.INTBINOP (T.MINUS,
												T.MEM (T.TEMP ptrTmp, T.DWORD),
												T.CONST (T.INT 4)))
		val sizeTmp = Temp.newtemp ()
		val initSizeTmp = T.MOVE (
			T.TEMP sizeTmp,
			T.INTBINOP (T.PLUS,
						T.INTBINOP (T.MUL,
									T.MEM (T.TEMP memPtrTmp, T.DWORD),
									T.CONST (T.INT (sizeOfTy t))),
			T.CONST (T.INT 4)))
		
		val endPtrTmp = Temp.newtemp ()
		val initEndPtrTmp = T.MOVE (T.TEMP endPtrTmp, 
									T.INTBINOP (T.PLUS,
												T.TEMP memPtrTmp,
												T.TEMP sizeTmp))

		val resTmp = Temp.newtemp ()
		val initResTmp = T.MOVE (T.TEMP resTmp,
								 T.CALL (T.NAME (Temp.namedLabel "allocInToSpace"), [T.INTBINOP (T.PLUS, T.TEMP sizeTmp, T.CONST (T.INT 4))]))
				
		val gcArrayLoopLabel = Temp.newLabel "gc_array_loop"
		val gcArrayLoopDoneLabel = Temp.newLabel "gc_array_done"
		val gcArrayLoopDoLabel = Temp.newLabel "gc_array_do"
		val gcArrayLoopSkipLabel = Temp.newLabel "gc_array_skip"
		
		val cond = T.INTCJUMP (T.REQ,
							   T.MEM (T.TEMP ptrTmp, T.DWORD),
							   T.TEMP endPtrTmp,
							   gcArrayLoopDoneLabel,
							   gcArrayLoopDoLabel)
		val incrPtrTmp = T.MOVE (T.MEM (T.TEMP ptrTmp, T.DWORD),
								 T.INTBINOP (T.PLUS,
											 T.MEM (T.TEMP ptrTmp, T.DWORD),
											 T.CONST (T.INT (sizeOfTy t))))
		val jump = T.JUMP (T.NAME gcArrayLoopLabel, [gcArrayLoopLabel])
		
		val gcArrayDoForwardLabel = Temp.newLabel "gc_array_do_forward"
		val gcArrayIsForwardedLabel = Temp.newLabel "gc_array_is_forwarded"
		val gcArrayUpdateArg = Temp.newLabel "gc_array_update_arg"
		
		val forwardeeTmp = Temp.newtemp ()
		val initForwardeeTmp = T.MOVE (T.TEMP forwardeeTmp,
									   T.MEM (T.INTBINOP (T.MINUS,
												T.MEM (T.TEMP ptrTmp, T.DWORD),
												T.CONST (T.INT 8)), T.DWORD))
		val condIsForwarded = T.INTCJUMP (T.REQ,
										  T.TEMP forwardeeTmp,
										  T.CONST (T.INT 0),
										  gcArrayDoForwardLabel,
										  gcArrayIsForwardedLabel)
										  
		val moveForwardeeToRes = T.MOVE (T.TEMP resTmp, T.TEMP forwardeeTmp)

		val moveResToForwardee = T.MOVE (T.MEM (T.INTBINOP (T.MINUS,
															T.TEMP memPtrTmp,
															T.CONST (T.INT 4)), T.DWORD),
										 T.TEMP resTmp)
				
		(* This is kinda ugly. callGCHandler expects T.MEMs, and thus the
		   code that checks if the object is valid cannot be passed to callGCHandler.
		   Instead we mutate a list of conditionals that should be true for the object
		   to be considered valid, and then we prepend these conditions to the statements.
		   An alternative would be to modify every case in callGCHandler to allow for
		   T.ESEQs *)
		val validObjCond = ref [] : T.stm list ref
		val call = callGCHandler (t, List.tabulate ((sizeOfTy t) div 4, fn n =>
			let
				val baseTmp = Temp.newtemp ()
				val objTmp = Temp.newtemp ()
				val gcArrayLoopContLabel = Temp.newLabel "gc_array_cont"
				val initBaseTmp = T.MOVE (T.TEMP baseTmp, T.MEM (T.TEMP ptrTmp, T.DWORD))
				val initObjTmp = T.MOVE (T.TEMP objTmp,
										 T.INTBINOP (T.PLUS,
													 T.TEMP baseTmp,
													 T.CONST (T.INT (4*n))))
			in
				validObjCond := (!validObjCond) @ [
					T.INTCJUMP (T.REQ,
								T.TEMP objTmp,
								T.CONST (T.INT 0),
								gcArrayLoopSkipLabel,
								gcArrayLoopContLabel),
					T.LABEL gcArrayLoopContLabel,
					initBaseTmp,
					initObjTmp
				];
				Ex (T.MEM (T.TEMP objTmp, T.DWORD))
			end))
				
		val memcpy = T.CALL (T.NAME (Temp.namedLabel "memcpy"),
			[T.INTBINOP (T.PLUS, T.TEMP resTmp, T.CONST (T.INT 4)), T.TEMP memPtrTmp, T.TEMP sizeTmp])
	in
		case call of
			NONE =>
			SOME (Ex (T.ESEQ (
				seq [
					initPtrTmp,
					initForwardeeTmp,
					condIsForwarded,
					T.LABEL gcArrayDoForwardLabel,
					initMemPtrTmp,
					initSizeTmp,
					initResTmp,
					T.MOVE (T.TEMP resTmp, memcpy),
					moveResToForwardee,
					T.JUMP (T.NAME gcArrayUpdateArg, [gcArrayUpdateArg]),
					T.LABEL gcArrayIsForwardedLabel,
					moveForwardeeToRes,
					T.LABEL gcArrayUpdateArg,
					T.MOVE (T.MEM (ptr, T.DWORD), T.INTBINOP (T.PLUS, T.TEMP resTmp, T.CONST (T.INT 4)))
				], T.INTBINOP (T.PLUS, T.TEMP resTmp, T.CONST (T.INT 4))
			)))
		  | SOME call =>
			SOME (Ex (T.ESEQ (
				seq ([initPtrTmp,
					 initForwardeeTmp,
					 condIsForwarded,
					 T.LABEL gcArrayDoForwardLabel,
					 initMemPtrTmp,
					 initSizeTmp,
					 initEndPtrTmp,
					 initResTmp,
					 T.LABEL gcArrayLoopLabel,
					 cond,	
					 T.LABEL gcArrayLoopDoLabel
				] @ !validObjCond @ [
					 unNx call,
					 T.LABEL gcArrayLoopSkipLabel,
					 incrPtrTmp,
					 jump,
					 T.LABEL gcArrayLoopDoneLabel,
					 T.MOVE (T.TEMP resTmp, memcpy),
					 moveResToForwardee,
					 T.JUMP (T.NAME gcArrayUpdateArg, [gcArrayUpdateArg]),
					 T.LABEL gcArrayIsForwardedLabel,
					 moveForwardeeToRes,
					 T.LABEL gcArrayUpdateArg,
					 T.MOVE (T.MEM (ptr, T.DWORD), T.INTBINOP (T.PLUS, T.TEMP resTmp, T.CONST (T.INT 4)))
				]), T.INTBINOP (T.PLUS, T.TEMP resTmp, T.CONST (T.INT 4))
			)))
	end
  | callGCHandler (Types.INTERFACE _, accessExp) = handleClassOrInterface accessExp
  | callGCHandler (Types.CLASS _, accessExp) = handleClassOrInterface accessExp
  | callGCHandler (Types.STRING, accessExp) =
	let
		val ptr = case accessExp of
			[Ex exp] => exp 
		  | _ => raise Fail "pushGCHandler2IR: Expected expression of size 1"
		  
		val src = Temp.newtemp ()
		val initSrc = T.MOVE (T.TEMP src, ptr)
		
		val gcStringDoForwardLabel = Temp.newLabel "gc_string_do_forward"
		val gcStringIsForwardedLabel = Temp.newLabel "gc_string_is_forwarded"
		val gcStringDoneLabel = Temp.newLabel "gc_string_done"
		
		val cond = T.INTCJUMP (T.REQ,
							   T.MEM ((T.TEMP src), T.DWORD),
							   T.CONST (T.INT 0),
							   gcStringDoForwardLabel,
							   gcStringIsForwardedLabel)
		
		val dst = Temp.newtemp ()
		val strlen = T.CALL (T.NAME (Temp.namedLabel "_lstrlenW"), [T.INTBINOP (T.PLUS, T.TEMP src, T.CONST (T.INT 4))])
		val initDst = T.MOVE (T.TEMP dst,
			T.CALL (T.NAME (Temp.namedLabel "allocInToSpace"), [T.INTBINOP (T.PLUS, strlen, T.CONST (T.INT 5))]))
		val updateForwardee = T.MOVE (T.MEM ((T.TEMP src), T.DWORD), T.TEMP dst)
		val strcpy = T.EXP (T.CALL (T.NAME (Temp.namedLabel "_StrCpyW"),
			[T.INTBINOP (T.PLUS, T.TEMP dst, T.CONST (T.INT 4)),
			 T.INTBINOP (T.PLUS, T.TEMP src, T.CONST (T.INT 4))]))
		val forwardeeToDst = T.MOVE (T.TEMP dst, T.MEM (T.TEMP src, T.DWORD))
		val updateArg = T.MOVE (ptr, T.TEMP dst)
		val jump = T.JUMP (T.NAME gcStringDoneLabel, [gcStringDoneLabel])
	in
		SOME (Ex (T.ESEQ (seq [
			initSrc,
			cond,
			T.LABEL gcStringDoForwardLabel,
			initDst,
			updateForwardee,
			strcpy,
			jump,
			T.LABEL gcStringIsForwardedLabel,
			forwardeeToDst,
			T.LABEL gcStringDoneLabel,
			updateArg
		], T.TEMP dst)))
	end
  | callGCHandler _ = NONE
end
	
fun genForwardIR members (new_obj, obj) =
	List.foldl (fn ((ty, acc), ir) =>
		let
			fun handleClassOrInterface () =
				let
					val c = case unEx (List.hd (memberInClass (Ex (T.TEMP obj)) acc)) of
						T.MEM (c, _) => c
					  | _ => raise Fail "Expected T.MEM"
					val gc = T.MEM (T.MEM (T.MEM (c, T.DWORD), T.DWORD), T.DWORD)

					val callForward = T.CALL (gc, [c])
				in
					[Nx (T.MOVE (
						unEx (List.hd (memberInClass (Ex (T.TEMP new_obj)) acc)),
						callForward))]
				end
					
			val ir' = case ty of
				Types.CLASS _ => handleClassOrInterface ()
			  | Types.FUNCTION _ =>
				let
					val gc = T.MEM (T.INTBINOP (T.PLUS,
												unEx (List.last (memberInClass (Ex (T.TEMP obj)) acc)),
												T.CONST (T.INT 4)), T.DWORD)

					 val (funcExp, envExp) = case List.map unEx (memberInClass (Ex (T.TEMP obj)) acc) of
						[funcExp, T.MEM (envExp, _)] => (funcExp, envExp)
					  | _ => raise Fail "Expected expression of size 2"
					
					val callForward = T.CALL (gc, [envExp])
					val (funcDst, envDst) = case memberInClass (Ex (T.TEMP new_obj)) acc of
						[Ex funcDst, Ex envDst] => (funcDst, envDst)
					  | _ => raise Fail "Expected expression of size 2"
				in
					[Nx (T.MOVE (funcDst, funcExp)),
					 Nx (T.MOVE (envDst, callForward))]
				end
			  | Types.ARRAY _ =>
				let
					val callForward = case callGCHandler (ty, memberInClass (Ex (T.TEMP obj)) acc) of
						SOME callForward => unEx callForward
					  | _ => raise Fail "Expected SOME expression of size 1"
					  
					val newArr = case memberInClass (Ex (T.TEMP new_obj)) acc of
						[newArr] => unEx newArr
					  | _ => raise Fail "Expected expression of size 1"
				in
					[Nx (T.MOVE (newArr, callForward))]
				end
			  | Types.STRING =>
				let
					val callForward = case callGCHandler (ty, memberInClass (Ex (T.TEMP obj)) acc) of
						SOME callForward => unEx callForward
					  | _ => raise Fail "Expected SOME expression of size 1"
					  
					val newStr = case memberInClass (Ex (T.TEMP new_obj)) acc of
						[newStr] => unEx newStr
					  | _ => raise Fail "Expected expression of size 1"
				in
					[Nx (T.MOVE (newStr, callForward))]
				end
			  | Types.INTERFACE _ => handleClassOrInterface ()
			  | _ =>
				let
					(* We know it's a scalar value, so just do a plain old copy *)
					val old = unEx (List.hd (memberInClass (Ex (T.TEMP obj)) acc))
					val new = unEx (List.hd (memberInClass (Ex (T.TEMP new_obj)) acc))
				in
					[Nx (T.MOVE (new, old))]
				end
		in
			ir @ ir'
		end
	) [] members
	
fun forwardClassObj2IR level name members =
let
	val (_, forwardeeAcc) = List.hd members
	val objSize = List.foldl (fn ((_ ,(_, acc)), size) =>
		(4 * (List.length acc)) + size
	) 4 members (* 4 bytes from vptr *)
		
	fun genForwardIR' (new_obj, obj) =
		let
			(* Skip the first member since this is the forwardee pointer *)
			val forwardIR = genForwardIR (List.tl members) (new_obj, obj)
		in
			(* Remember to forward the vptr! *)
			(Nx (T.MOVE (T.MEM (T.TEMP new_obj, T.DWORD), T.MEM (T.TEMP obj, T.DWORD)))) :: forwardIR
		end
in
	forward2IR level name objSize forwardeeAcc genForwardIR'
end

fun forwardLambdaObj2IR (level, label, captures, forwardee, forwarder) =
let
	(* Start at 8 bytes to account for GC overhead *)
	val objSize =  List.foldl (fn ((_, (_, acc), _), size) =>
		(4 * (List.length acc)) + size
	) 8 captures

	fun genForwardIR' (new_obj, obj) =
		genForwardIR (List.map (fn (_, acc, ty) =>(ty, acc)) captures) (new_obj, obj)
in
	forward2IR level (Symbol.name label) objSize forwardee genForwardIR'
end

fun allocArray2IR ty [exp] =
	let
		val r = Temp.newtemp ()
		val exp' = unEx exp
	in
		(* Alloc size + 8 since we use position -1 for the size and -2 for the forwardee ptr *)
		Ex (T.ESEQ (seq [
			T.MOVE (T.TEMP r,
					T.CALL (T.NAME (Temp.namedLabel "allocate"),
						[T.INTBINOP (T.PLUS,
									 T.INTBINOP (T.MUL,
													  exp',
													  T.CONST (T.INT (sizeOfTy ty))),
									 T.CONST (T.INT 8))])),
			T.MOVE (T.MEM (T.INTBINOP (T.PLUS, T.TEMP r, T.CONST (T.INT 4)), T.DWORD), exp')
		], T.INTBINOP (T.PLUS, T.TEMP r, T.CONST (T.INT 8))))
	end
  | allocArray2IR ty _ = emptyEx

fun initLambda (args as (level, label, captures, forwardee, forwarder)) = 
	let
		val t = Temp.newtemp ()
		val r1 = Temp.newtemp ()
		(* Allocate space for captures + function ptr.
		   Add 4 bytes for forwarding function and another
		   4 bytes for forwardee pointer*)
		val envSize = 4 * (List.length captures) + 8
		val malloc = (T.CALL (T.NAME (Temp.namedLabel "allocate"), [T.CONST (T.INT envSize)]))
		
		(* Move captured variables into the closure environment *)
		fun moveCapture ((acc, _, _), (nr, ir)) =
			let
				val src = List.map unEx (simpleVar acc)
				
				val (offset, moves) =
					List.foldl (fn (s, (offset, moves)) =>
					let
						val dst = T.MEM (T.INTBINOP (T.PLUS, T.TEMP t, T.CONST (T.INT offset)), T.DWORD)
					in
						(offset + 4, moves @ [T.MOVE (dst, s)])
					end
				) (nr, []) src
			in
				(offset, seq (ir :: moves))
			end
		(* Start at offset 8 since the first 2 fields are reserved for GC'ing overhead *)
		val (_, captureValsIR) = (foldl moveCapture (8, unNx emptyNx) captures)
		(* Create function to GC environment *)
		val closureForwarder = T.NAME (forwardLambdaObj2IR args)
	in
		(Nx (seq [	T.MOVE (T.TEMP t, malloc),
				T.MOVE (T.TEMP r1, T.NAME label),
				T.MOVE (T.MEM (T.INTBINOP (T.PLUS,
										   T.TEMP t,
										   T.CONST (T.INT 4)), T.DWORD),
						closureForwarder),
				captureValsIR
			]),
			Ex (T.TEMP r1),
			Ex (T.TEMP t)
		)
	end
	
fun pushGCHandler2IR level tyAccs =
	let
		val label = newLabel "gc_handler"
		val level' = newLevel {
			parent = level,
			name = label,
			formals = 4
		}
		(* Same functionality as simpleVar, but with another frame pointer *)
		fun simpleVar' ((toLevel, access)) =
			let
				val fp = case simpleVar (accessOfFormal level' 0 true 4) of
					[exp] => unEx exp
				  | _ => raise Fail "Expected expression of size 1"
			in List.map (fn acc => Ex (F.exp acc fp)) access
			end
			
		val ir = List.mapPartial (fn (ty, access) =>
			callGCHandler (ty, simpleVar' access)
		) tyAccs
	in
		funEntryExit {level = level', body = seq2IR ir};
		Ex (T.CALL (T.NAME (Temp.namedLabel "push_gc_handler"), [T.NAME label]))
	end
	
end (* Translate *)
structure X86Frame: FRAME =
struct

(* We will use the following format for an activation record:
 *
 * ^ higher addresses
 * ------------------------------ previous frame
 *   ...
 *   argument n                   [FP+4*(2+n)]
 *   ...
 *   argument 1                   [FP+4*2]
 *   return address               [FP+4]
 * ------------------------------ current frame
 *   old frame pointer            [FP]            <-- frame pointer
 *   local variable 1             [FP-4*1]
 *   ...
 *   local variable m             [FP-4*m]
 *   ---------------- if CALL..
 *   argument n'
 *   ...
 *   argument 1
 *   return address
 * ------------------------------ ..next frame will look like this
 *   old frame pointer
 *   ...
 * ------------------------------
 * v lower addresses
 *)

structure Sy = Symbol
structure Tm = Temp
structure Tr = Tree
structure A = Assem

exception Bug of string

type frame = { name: Tm.label           (* label of code of function *)
             , formals: int       		(* Number of formal params? *)
             , locals: int ref}			(* number of locals within the frame *)

datatype access =
		 InClass of int					(* Value is either captured (by a lambda function)
											or a member in a class *)
	   | InVTable of int * bool			(* Value stored in vtable position #1 in this vtable.
										   #2 is true iff it's an interface function *)
       | InFrame of int                 (* value in memory, offset from FP *)
       | InReg of Tm.temp               (* value in register *)
	   | InGlobal of Sy.symbol * bool	(* value stored in global variable *)

type register = string
	   
datatype frag =
         PROC of {body: Tr.stm, frame: frame}
       | STRING of Tm.label * string
       | NUMBER of Tm.label * string
	   | GLOBAL of Sy.symbol * bool
	   | TABLE of Tm.label * (Tm.label list)

val FP = Tm.newtemp ()                  (* Frame pointer: %ebp *)
val SP = Tm.newtemp ()                  (* Stack pointer: %esp *)
val RV = Tm.newtemp ()                  (* Return value: %eax *)

val EAX = RV                            (* %eax: add, mult, .. *)
val EBX = Tm.newtemp ()                 (* %ebx: base of array *)
val ECX = Tm.newtemp ()                 (* %ecx: count of loop *)
val EDX = Tm.newtemp ()                 (* %edx: data *)
val ESI = Tm.newtemp ()                 (* %esi: source index (string cpy) *)
val EDI = Tm.newtemp ()                 (* %edi: destination index *)

val XMM0 = Tm.newtemp ()
val XMM1 = Tm.newtemp ()
val XMM2 = Tm.newtemp ()
val XMM3 = Tm.newtemp ()
val XMM4 = Tm.newtemp ()
val XMM5 = Tm.newtemp ()
val XMM6 = Tm.newtemp ()
val XMM7 = Tm.newtemp ()

val wordSize = 4                        (* 32 bit words *)

(* Register Lists *)
val specialregs = [FP, SP, RV]
val calleesaves = [EBX, ESI, EDI]
val callersaves = [EAX, ECX, EDX]
val calldefs = callersaves @ [RV]

fun asStringFrame (frame:frame) =
    "{name = " ^
    Sy.name (#name frame) ^
    ", formals = " ^
	String.concat (List.tabulate (#formals frame, fn _ => "t")) ^
    ", locals = " ^
    Int.toString (!(#locals frame)) ^
    "}"

fun asStringAccess (InFrame i) =
    "InFrame(" ^
    Int.toString i ^
    ")"
  | asStringAccess (InReg tmp) =
    "InReg(" ^
    Tm.makestring tmp ^
    ")"
  | asStringAccess (InGlobal (sym, w)) =
	"InGlobal(" ^
	 Sy.name sym ^
	 ", " ^
	 Bool.toString w ^
	 ")"
  | asStringAccess (InClass n) =
	"InClass(" ^
	 Int.toString n ^
	 ")"
  | asStringAccess (InVTable (n, b)) =
	"InVTable(" ^
	Int.toString n ^
	", " ^
	Bool.toString b ^
	")"

fun printx asStringX (outstream, x) =
    ( TextIO.output (outstream, asStringX x ^ "\n")
    ; TextIO.flushOut outstream)

fun printFrame (outstream, f)  = printx asStringFrame  (outstream, f)
fun printAccess (outstream, a) = printx asStringAccess (outstream, a)

fun newFrame {name, formals} = {name=name, formals=formals, locals=ref 0}

fun frameSize (f: frame) =
    let
        val formalsSize = wordSize * (#formals f)
        val localsSize = wordSize * !(#locals f)
    in
        formalsSize + localsSize
    end

fun name (fr:frame) = #name fr

fun offsetOfFormal nr = 8 + nr * wordSize

fun accessOfFormal nr escaping =
    if escaping then InFrame (offsetOfFormal nr)
    else InReg (Tm.newtemp ())

fun accessOfTemp tmp = InReg tmp
	
fun local2access (escapes: bool, noOfLocals: int) =
    if escapes
    then InFrame (~ noOfLocals * wordSize)
    else InReg (Tm.newtemp ())

fun allocLocal (f:frame) escapes =
    let
        val locals = #locals f
    in
		if escapes then
			locals := !locals + 1
		else ();
        local2access (escapes, !locals)
    end
	
fun allocMember (f:frame) =
	let
		val locals = #locals f
		val access = InClass (4 * !locals)
	in
		locals := !locals + 1;
		access
	end
	
fun allocVtableEntry offset interfaceEntry = InVTable (offset, interfaceEntry)
	
fun allocGlobal sym writable = InGlobal (sym, writable)

fun memberInClass exp (InClass k) =
	Tr.MEM (Tr.INTBINOP (Tr.PLUS,
				 exp,
				 Tr.CONST (Tr.INT k)), Tr.DWORD)
  | memberInClass exp (InVTable (k, false)) =
	Tr.MEM (Tr.INTBINOP (Tr.PLUS,
						 Tr.MEM (exp, Tr.DWORD),
						 Tr.CONST (Tr.INT k)), Tr.DWORD)
  | memberInClass exp (InVTable (k, true)) =
		Tr.MEM (Tr.INTBINOP (Tr.PLUS, exp, Tr.CONST (Tr.INT k)), Tr.DWORD)
  | memberInClass _ _ = raise Fail "Expected InClass or InVTable"
  
fun number2formal nr =
    Tr.MEM (Tr.INTBINOP ( Tr.PLUS
                     , Tr.TEMP FP
                     , Tr.CONST (Tr.INT (offsetOfFormal nr))), Tr.DWORD)

fun exp (InFrame k) fp =
    Tr.MEM (Tr.INTBINOP (Tr.PLUS, fp, Tr.CONST (Tr.INT k)), Tr.DWORD)
  | exp (InReg temp) _ =
    Tr.TEMP temp
  | exp (InGlobal (sym, _)) _ =
	Tr.MEM (Tr.NAME sym, Tr.DWORD)
  | exp (InClass k) fp =
	Tr.MEM (Tr.INTBINOP (
		Tr.PLUS, 
		exp (InFrame 8) fp,
		Tr.CONST (Tr.INT k)), Tr.DWORD)
  | exp (InVTable (k, false)) fp =
	Tr.MEM (Tr.INTBINOP (
		Tr.PLUS,
		exp (InClass 0) fp,
		Tr.CONST (Tr.INT k)), Tr.DWORD)
  | exp (InVTable (k, true)) fp =
	Tr.INTBINOP (
		Tr.PLUS,
		exp (InClass 0) fp,
		Tr.CONST (Tr.INT k))

fun number (label, s) =
	"_DATA SEGMENT\n" ^ Sy.name label ^ " dd " ^ s ^ "\n_DATA ENDS\n"
	
fun string (label, s) =
	let
		(* The following escape sequences are available in Alpha:
			- \0: Null char
			- \n: Newline char
			- \t: Tab char
			- \r: Carriage return
			- \\: For writing \ in a string
			- \": For writing " in a string
			- \xabc: For ascii value abc
		
		  In MASM a string literal is constructing using:
		  string db 'A string', 0ah, 'more of the string', 0h, 'etc'
		  
		*)
		fun x86ify s =
			let
				(* Really annoying: A masm string cannot be empty,
				   so we remove any '' in the string literal. *)
				fun removeEmpties (#"'" :: #"'" :: #"," :: s) = removeEmpties s
				  | removeEmpties (#"'" :: #"'" :: s) = removeEmpties s
				  | removeEmpties (ch :: s) = (String.str ch) ^ (removeEmpties s)
				  | removeEmpties [] = ""
				val _ = List.app print (List.map (Int.toString o Char.ord) (String.explode s))
				val _ = print "\n"
				val format = Absyn.visitString (fn _ => "0h,",
												fn _ => "0ah,",
												fn _ => "09h,",
												fn _ => "0dh,",
												fn (a, b, c, d) =>
													let
														val ch1 = String.implode [c, d, #"h"]
														val ch2 = String.implode [a, b, #"h"]
													in
														(if c = #"0" then "" else "0") ^ ch1 ^ "," ^
														(if a = #"0" then "" else "0") ^ ch2 ^ ","
													end,
												op^,
												fn ch => Int.toString (Char.ord ch) ^ ",",
												"") true
			in
				removeEmpties (explode (format s ^ "0h"))
			end
	in
		"_DATA SEGMENT\n" ^ Sy.name label ^ " db " ^ x86ify s ^ "\n_DATA ENDS\n"
	end

fun global sym =
	"_BSS SEGMENT\nCOMM " ^ Sy.name sym ^ ":DWORD\n_BSS ENDS\n"
	
fun table (label, labels) =
	"_DATA SEGMENT\n" ^
	Sy.name label ^ ":\n" ^
	String.concat (List.map (fn lab => "dword " ^ Sy.name lab ^ "\n") labels) ^
	"\n_DATA ENDS\n"

fun move (reg, var) = Tr.MOVE (Tr.TEMP reg, Tr.TEMP var)

fun seq [] = Tr.EXP (Tr.CONST (Tr.INT 0))
  | seq [exp] = exp
  | seq (exp :: exps) = (Tr.SEQ (exp, (seq exps)))

fun externalCall (str, args) = Tr.CALL (Tr.NAME (Tm.namedLabel str), args)

fun entryExit1 (frame as {name, formals = _, locals = _}, body) =
    let
        (* extend body to save 'callee save' registers in temporaries *)
        val toSave = calleesaves
        val saved = map (fn _ => Temp.newtemp ()) toSave
        val saveIR = seq (ListPair.mapEq move (saved, toSave))
        val restoreIR = seq (List.rev (ListPair.mapEq move (toSave, saved)))
		(* Save callee saves, do body, label for jumping and restore callee saves *)
        val body' = seq [saveIR, body, Tr.LABEL (Tm.namedLabel ((Sy.name name) ^ "_end")), restoreIR]
    in
        body'
    end

(* inform register allocator about register usage *)
fun entryExit2 (frame, body) =
    (A.OPER { assem = "\t; SP, FP, calleesaves have values"
            , src = []
            , dst = [SP, FP] @ calleesaves
            , jump = NONE
            , doc = ""})
    :: body
    @ [A.OPER { assem = "\t; FP, SP, RV, calleesaves still live"
              , src = specialregs @ calleesaves
              , dst = []
              , jump = SOME []
              , doc = ""}]

fun entryExit3 ( frame as {name, formals, locals}: frame
                   , body : A.instr list) =
    let
        val size = frameSize frame
        val id = Sy.name name
    in
        { prolog =  "PUBLIC " ^ id ^ "\n" ^
					"_TEXT SEGMENT \n" ^
					id ^ " PROC \n" ^
					"\tpush ebp\n" ^
					"\tmov ebp, esp\n" ^
					(if size > 0 then
						"\tsub esp, " ^ Int.toString size ^ "\n"
					else "") ^
					"\tcall gc_handler_inc\n"
        , body = body
        , epilog =  "\tcall gc_handler_dec\n" ^
					(if size > 0 then
						"\tadd esp, " ^ Int.toString size ^ "\n"
					else "") ^
					"\tmov esp, ebp\n" ^
					"\tpop ebp\n" ^
					"\tret\n" ^
					id ^ " ENDP\n" ^
					"_TEXT ENDS" }
    end

local
	val regmaxbit = [ (FP,  "ebp")
					, (SP,  "esp")
					, (EAX, "eax")
					, (EBX, "ebx")
					, (ECX, "ecx")
					, (EDX, "edx")
					, (ESI, "esi")
					, (EDI, "edi")
					, (XMM0, "xmm0")
					, (XMM1, "xmm1")
					, (XMM2, "xmm2")
					, (XMM3, "xmm3")
					, (XMM4, "xmm4")
					, (XMM5, "xmm5")
					, (XMM6, "xmm6")
					, (XMM7, "xmm7")]
	val reg16bit = [ ("eax", "ax")
				   , ("ebx", "bx")
				   , ("ecx", "cx")
				   , ("edx", "dx")]
	val reg8bit = [ ("eax", "al")
				  , ("ebx", "bl")
				  , ("ecx", "cl")
				  , ("edx", "dl")]
in
	val tempMap = Temp.Table.fromList regmaxbit
	fun nameForSize Tr.DWORD r = r
	  | nameForSize Tr.WORD r =
		(case List.find (fn (maxbit, _) => maxbit = r) reg16bit of
			NONE => raise Fail "No 16 bit version available for register"
		  | SOME (_, r') => r')
	  | nameForSize Tr.BYTE r =
		(case List.find (fn (maxbit, _) => maxbit = r) reg8bit of
			NONE => raise Fail "No 8 bit version available for register"
		  | SOME (_, r') => r')
end
	
val tempToSize = ref Temp.Table.empty
fun forceSize n t =
	tempToSize := Temp.Table.enter (!tempToSize, t, n)
	
fun size t = Temp.Table.look (!tempToSize, t)
	
fun toReg allocation t =
	case Temp.Table.look (allocation, t) of
		NONE => raise Fail ("No register found for temporary: " ^ (asStringReg t))
	  | SOME reg =>
		let
			val reg' = case Temp.Table.look (!tempToSize, t) of
						NONE => reg
					  | SOME n => nameForSize n reg
		in
			reg'
		end
	
and emit out emitfrag lib frags =
	let
		val prologue =
			".686P\n" ^
			".XMM\n" ^
			".model flat\n\n" ^
			"include " ^ lib ^ "/lib.inc\n" ^
			"includelib " ^ lib ^ "/lib.lib\n\n"
		val epilogue = "\nend"
		
		val _ = TextIO.output (out, prologue)
		val frags' = List.foldl (fn (frag, frags') =>
			emitfrag (out, frags', frag)
		) [] frags
		val _ = List.app (fn frag => (
			let val _ = emitfrag (out, frags', frag)
			in ()
			end)
		) frags'
	in
		TextIO.output (out, epilogue)
	end
(* ---------- Printing ---------- *)

and asStringReg r =
    case Temp.Table.look (tempMap, r)
     of SOME regname => regname
      | NONE => Temp.makestring r

val registers = List.map asStringReg [EAX, EBX, ECX, EDX, ESI, EDI,
	 XMM0, XMM1, XMM2, XMM3, XMM4, XMM5, XMM6, XMM7]

end (* X86Frame *)

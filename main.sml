structure F = X86Frame
structure G = X86Gen
structure S = Symbol
structure Te = Temp
structure C = Canon
structure A = Assem
structure R = RegAlloc
structure PT = PrintTree(F)

fun emitproc (out, frags, frag as F.PROC {body, frame}) =
    let
		val stms = C.linearize body
        val stms' = C.traceSchedule (C.basicBlocks stms)
		val _ = print (S.name (F.name frame) ^ ":\n")
		val _ = List.app (fn stm => PT.printStm (TextIO.stdOut, stm)) stms'
		
		val (instrs, regClass, frags') = (List.foldl (fn (stmt, (instrs, regClassMap, frags)) =>
			let
				val (instrs', regClassMap', frags') = G.codegen frame stmt regClassMap frags
				(* Merge the two reg class maps *)
				val regClassMap'' =
					Temp.Table.unionWith (fn (regs1, regs2) => IntBinarySet.intersection (regs1, regs2))
					(regClassMap, regClassMap')
			in
				(instrs @ instrs', regClassMap'', frags')
			end) ([], Temp.Table.empty, frags) stms')

		val instrs' = F.entryExit2 (frame, instrs)
		val (instrs'', allocation) = R.alloc (instrs', frame, regClass)
		val {prolog, epilog, body=instrs'''} = F.entryExit3 (frame, instrs'')
		
		val format = A.format (F.toReg allocation)
    in
		TextIO.output (out, "\n" ^ prolog);
		List.app (fn i => TextIO.output (out, format i)) instrs''';
		TextIO.output (out, epilog ^ "\n");
		frags'
    end
  | emitproc (out, frags, F.STRING (lab, s)) =
	let val _ = TextIO.output (out, F.string (lab, s))
	in frags
	end
  | emitproc (out, frags, F.NUMBER (lab, s)) =
	let val _ = TextIO.output (out, F.number (lab, s))
	in frags
	end
  | emitproc (out, frags, F.GLOBAL (sym, w)) =
	let val _ = if w then TextIO.output (out, F.global sym) else ()
	in frags
	end
  | emitproc (out, frags, F.TABLE (lab, labels)) =
	let val _ = TextIO.output (out, F.table (lab, labels))
	in frags
	end;
	
let
	val (fileIn, fileOut, libPath) = case CommandLine.arguments () of
		fileIn :: fileOut :: [] => (fileIn, fileOut, "C:/Alpha/lib")
	  | fileIn :: fileOut :: libPath :: [] => (fileIn, fileOut, libPath)
	  | _ => raise Fail "Usage: alpha input.a output.a [library directory]"

	val out = TextIO.openOut fileOut
	val absyn = Parse.parse (fileIn)
	val (frags, success) =
		if !ErrorMsg.anyErrors then
			(NONE, false)
		else (SOME (Semant.transProg absyn), not (!ErrorMsg.anyErrors))
in
	case (frags, success) of
		(NONE, _) => OS.Process.exit OS.Process.failure
	  | (SOME _, false) => OS.Process.exit OS.Process.failure
	  | (SOME frags, true) =>
		(F.emit out emitproc libPath frags;
		 OS.Process.exit OS.Process.success)
end;